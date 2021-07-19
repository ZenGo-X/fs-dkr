#![allow(non_snake_case)]
#![allow(clippy::many_single_char_names)]

use paillier::Paillier;
use paillier::{Add, EncryptWithChosenRandomness, Mul, RawCiphertext};
use paillier::{EncryptionKey, Randomness, RawPlaintext};

use curv::arithmetic::{BigInt, Modulo, Samplable};
use curv::cryptographic_primitives::hashing::hash_sha256::HSha256;
use curv::cryptographic_primitives::hashing::traits::Hash;
use curv::cryptographic_primitives::proofs::ProofError;
use curv::elliptic::curves::traits::*;
use serde::{Deserialize, Serialize};
use zeroize::Zeroize;

/// Non interactive proof of fairness, taken from <https://hal.inria.fr/inria-00565274/document>
///
/// Witness: x
///
/// Statement: {c, Y} such that c = g^x * r^N mod N^2  and Y = x*G
///
/// Protocol:
///
/// 1. P picks random values u from Z_n, s from Z_n*
///    and computes e_u = g^u * s^N mod N^2 , T = u*G
/// 2. using Fiat-Shamir the parties computes a challenge e
/// 3. P sends z = u + ex , w = s * r^e mod N^2
/// 4. V checks: \
///     `T  = z*G - e*Y` \
///     `e_u = g^z * w^N * c^{-e} mod N^2`
///
/// _Note_: we need u to hide ex : |u| > |ex| + SEC_PARAM, taking u from Z_n works assuming
/// n = 2048, |x| < 256, |e| < 256

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub struct FairnessProof<P> {
    pub e_u: BigInt,
    pub T: P,
    pub z: BigInt,
    pub w: BigInt,
}

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub struct FairnessWitness<S: ECScalar> {
    pub x: S,
    pub r: BigInt,
}

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub struct FairnessStatement<P> {
    pub ek: EncryptionKey,
    pub c: BigInt,
    pub Y: P,
}

impl<P> FairnessProof<P>
where
    P: ECPoint + Clone + Zeroize,
    P::Scalar: PartialEq + Clone + Zeroize,
{
    pub fn prove(witness: &FairnessWitness<P::Scalar>, statement: &FairnessStatement<P>) -> Self {
        let u = BigInt::sample_below(&statement.ek.n);
        let s = BigInt::sample_below(&statement.ek.n);

        let e_u = Paillier::encrypt_with_chosen_randomness(
            &statement.ek,
            RawPlaintext::from(u.clone()),
            &Randomness(s.clone()),
        )
        .0
        .into_owned();
        let u_fe: P::Scalar = ECScalar::from(&u);
        let T = P::generator() * u_fe;

        let e = HSha256::create_hash(&[
            &T.bytes_compressed_to_big_int(),
            &e_u,
            &statement.c,
            &statement.ek.n,
            &statement.Y.bytes_compressed_to_big_int(),
        ]);

        let z = u + &e * &witness.x.to_big_int();
        let r_x_e = BigInt::mod_pow(&witness.r, &e, &statement.ek.nn);
        let w = BigInt::mod_mul(&r_x_e, &s, &statement.ek.nn);
        FairnessProof { e_u, T, z, w }
    }

    pub fn verify(&self, statement: &FairnessStatement<P>) -> Result<(), ProofError> {
        let e = HSha256::create_hash(&[
            &self.T.bytes_compressed_to_big_int(),
            &self.e_u,
            &statement.c,
            &statement.ek.n,
            &statement.Y.bytes_compressed_to_big_int(),
        ]);

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

        let z_fe: P::Scalar = ECScalar::from(&self.z);
        let z_G = P::generator() * z_fe;
        let e_fe: P::Scalar = ECScalar::from(&e);
        let e_Y = statement.Y.clone() * e_fe;
        let T_add_e_Y = e_Y + self.T.clone();

        match T_add_e_Y == z_G && e_u_add_c_e == enc_z_w {
            true => Ok(()),
            false => Err(ProofError),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::proof_of_fairness::{FairnessProof, FairnessStatement, FairnessWitness};
    use curv::arithmetic::{One, Samplable};
    use curv::elliptic::curves::secp256_k1::{FE, GE};
    use curv::elliptic::curves::traits::{ECPoint, ECScalar};
    use curv::BigInt;
    use paillier::{
        EncryptWithChosenRandomness, KeyGeneration, Paillier, Randomness, RawPlaintext,
    };
    use zeroize::Zeroize;

    #[test]
    fn test_fairness_proof() {
        let (ek, _) = Paillier::keypair().keys();
        let x: FE = ECScalar::new_random();
        let x_bn = x.to_big_int();
        let r = BigInt::sample_below(&ek.n);

        let c = Paillier::encrypt_with_chosen_randomness(
            &ek,
            RawPlaintext::from(x_bn.clone()),
            &Randomness(r.clone()),
        )
        .0
        .into_owned();

        let Y = GE::generator() * &x;

        let witness = FairnessWitness { x, r };

        let statement = FairnessStatement { ek, c, Y };

        let proof = FairnessProof::prove(&witness, &statement);
        let verify = proof.verify(&statement);
        assert!(verify.is_ok());
    }

    #[test]
    fn test_bad_fairness_proof() {
        let (ek, _) = Paillier::keypair().keys();
        let x: FE = ECScalar::new_random();
        let x_bn = x.to_big_int();
        let r = BigInt::sample_below(&ek.n);

        let c = Paillier::encrypt_with_chosen_randomness(
            &ek,
            RawPlaintext::from(x_bn.clone() + BigInt::one()),
            &Randomness(r.clone()),
        )
        .0
        .into_owned();

        let Y = GE::generator() * &x;

        let witness = FairnessWitness { x, r };

        let statement = FairnessStatement { ek, c, Y };

        let proof = FairnessProof::prove(&witness, &statement);
        let verify = proof.verify(&statement);
        assert!(verify.is_err());
    }
}
