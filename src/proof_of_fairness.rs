#![allow(non_snake_case)]
use crate::error::{FsDkrError, FsDkrResult};

use curv::cryptographic_primitives::hashing::{Digest, DigestExt};
use curv::{BigInt, HashChoice};
use paillier::Paillier;
use paillier::{Add, EncryptWithChosenRandomness, Mul, RawCiphertext};
use paillier::{EncryptionKey, Randomness, RawPlaintext};

use curv::arithmetic::{Converter, Modulo, Samplable};
use curv::elliptic::curves::*;
use serde::{Deserialize, Serialize};

/// non interactive proof of fairness, taken from <https://hal.inria.fr/inria-00565274/document>

/// Witness: x
///
/// Statement: {c, Y} such that c = g^x * r^N mod N^2  and Y = x*G
///
/// Protocol:
///
/// 1. P picks random values u from Z_n, s from Z_n*
///    and computes e_u = g^u * s^N mod N^2 ,  T = u*G
/// 2. using Fiat-Shamir the parties computes a challenge e
/// 3. P sends z = u + ex , w = s* r^e mod N^2
/// 4. V checks:
///     T  = z*G - e*Y
///     e_u = g^z * w^N * c^{-e} mod N^2
///
/// note: we need u to hide ex : |u| > |ex| + SEC_PARAM, taking u from Z_n works assuming
/// n = 2048, |x| < 256, |e| < 256

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub struct FairnessProof<E: Curve, H: Digest + Clone> {
    pub e_u: BigInt,
    pub T: Point<E>,
    pub z: BigInt,
    pub w: BigInt,
    #[serde(skip)]
    pub hash_choice: HashChoice<H>,
}

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub struct FairnessWitness<E: Curve = Secp256k1> {
    pub x: Scalar<E>,
    pub r: BigInt,
}

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub struct FairnessStatement<E: Curve = Secp256k1> {
    pub ek: EncryptionKey,
    pub c: BigInt,
    pub Y: Point<E>,
}

impl<E: Curve, H: Digest + Clone> FairnessProof<E, H> {
    pub fn prove(witness: &FairnessWitness<E>, statement: &FairnessStatement<E>) -> Self {
        let u = BigInt::sample_below(&statement.ek.n);
        let s = BigInt::sample_below(&statement.ek.n);

        let e_u = Paillier::encrypt_with_chosen_randomness(
            &statement.ek,
            RawPlaintext::from(u.clone()),
            &Randomness(s.clone()),
        )
        .0
        .into_owned();
        let u_fe: Scalar<E> = Scalar::<E>::from(&u);
        let T = Point::<E>::generator() * u_fe;

        let e = H::new()
            .chain_bigint(&BigInt::from_bytes(&T.to_bytes(true)))
            .chain_bigint(&e_u)
            .chain_bigint(&statement.c)
            .chain_bigint(&statement.ek.n)
            .chain_bigint(&BigInt::from_bytes(&statement.Y.to_bytes(true)))
            .result_bigint();

        let z = u + &e * &witness.x.to_bigint();
        let r_x_e = BigInt::mod_pow(&witness.r, &e, &statement.ek.nn);
        let w = BigInt::mod_mul(&r_x_e, &s, &statement.ek.nn);
        FairnessProof {
            e_u,
            T,
            z,
            w,
            hash_choice: HashChoice::new(),
        }
    }

    pub fn verify(&self, statement: &FairnessStatement<E>) -> FsDkrResult<()> {
        let e = H::new()
            .chain_bigint(&BigInt::from_bytes(&self.T.to_bytes(true)))
            .chain_bigint(&self.e_u)
            .chain_bigint(&statement.c)
            .chain_bigint(&statement.ek.n)
            .chain_bigint(&BigInt::from_bytes(&statement.Y.to_bytes(true)))
            .result_bigint();

        let enc_z_w = Paillier::encrypt_with_chosen_randomness(
            &statement.ek,
            RawPlaintext::from(self.z.clone()),
            &Randomness(self.w.clone()),
        )
        .0
        .into_owned();
        let c_e = Paillier::mul(
            &statement.ek,
            RawCiphertext::from(statement.c.clone()),
            RawPlaintext::from(e.clone()),
        );
        let e_u_add_c_e = Paillier::add(&statement.ek, RawCiphertext::from(self.e_u.clone()), c_e)
            .0
            .into_owned();

        let z_fe: Scalar<E> = Scalar::<E>::from(&self.z);
        let z_G = Point::<E>::generator() * z_fe;
        let e_fe: Scalar<E> = Scalar::<E>::from(&e);
        let e_Y = statement.Y.clone() * e_fe;
        let T_add_e_Y = e_Y + self.T.clone();

        match T_add_e_Y == z_G && e_u_add_c_e == enc_z_w {
            true => Ok(()),
            false => Err(FsDkrError::FairnessProof {
                t_add_eq_z_g: T_add_e_Y == z_G,
                e_u_add_eq_z_w: e_u_add_c_e == enc_z_w,
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::proof_of_fairness::{FairnessProof, FairnessStatement, FairnessWitness};
    use curv::arithmetic::{One, Samplable};
    use curv::elliptic::curves::Secp256k1;
    use curv::elliptic::curves::{Point, Scalar};
    use curv::BigInt;
    use paillier::{
        EncryptWithChosenRandomness, KeyGeneration, Paillier, Randomness, RawPlaintext,
    };
    use sha2::Sha256;

    type GE = Point<Secp256k1>;
    type FE = Scalar<Secp256k1>;

    #[test]
    fn test_fairness_proof() {
        let (ek, _) = Paillier::keypair().keys();
        let x: FE = FE::random();
        let x_bn = x.to_bigint();
        let r = BigInt::sample_below(&ek.n);

        let c = Paillier::encrypt_with_chosen_randomness(
            &ek,
            RawPlaintext::from(x_bn),
            &Randomness(r.clone()),
        )
        .0
        .into_owned();

        let Y = GE::generator() * x.clone();

        let witness = FairnessWitness { x, r };

        let statement = FairnessStatement { ek, c, Y };

        let proof = FairnessProof::<_, Sha256>::prove(&witness, &statement);
        let verify = proof.verify(&statement);
        assert!(verify.is_ok());
    }

    #[should_panic]
    #[test]
    fn test_bad_fairness_proof() {
        let (ek, _) = Paillier::keypair().keys();
        let x: FE = FE::random();
        let x_bn = x.to_bigint();
        let r = BigInt::sample_below(&ek.n);

        let c = Paillier::encrypt_with_chosen_randomness(
            &ek,
            RawPlaintext::from(x_bn + BigInt::one()),
            &Randomness(r.clone()),
        )
        .0
        .into_owned();

        let Y = GE::generator() * x.clone();

        let witness = FairnessWitness { x, r };

        let statement = FairnessStatement { ek, c, Y };

        let proof = FairnessProof::<_, Sha256>::prove(&witness, &statement);
        let verify = proof.verify(&statement);
        assert!(verify.is_ok());
    }
}
