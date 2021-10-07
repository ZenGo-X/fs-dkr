#![cfg_attr(feature = "cargo-clippy", allow(clippy::many_single_char_names))]

mod error;
mod proof_of_fairness;
mod test;

use crate::error::{FsDkrError, FsDkrResult};
use crate::proof_of_fairness::{FairnessProof, FairnessStatement, FairnessWitness};
use curv::arithmetic::{Samplable, Zero};
use curv::cryptographic_primitives::secret_sharing::feldman_vss::{
    ShamirSecretSharing, VerifiableSS,
};
use curv::elliptic::curves::traits::{ECPoint, ECScalar};
use curv::BigInt;
use multi_party_ecdsa::protocols::multi_party_ecdsa::gg_2018::party_i::Keys;
use multi_party_ecdsa::protocols::multi_party_ecdsa::gg_2020::party_i::SharedKeys;
use multi_party_ecdsa::protocols::multi_party_ecdsa::gg_2020::state_machine::keygen::LocalKey;
pub use paillier::DecryptionKey;
use paillier::{
    Add, Decrypt, Encrypt, EncryptWithChosenRandomness, EncryptionKey, KeyGeneration, Mul,
    Paillier, Randomness, RawCiphertext, RawPlaintext,
};
use serde::{Deserialize, Serialize};
use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt::Debug;
use zeroize::Zeroize;
use zk_paillier::zkproofs::{NICorrectKeyProof, SALT_STRING};

// Everything here can be broadcasted
#[derive(Clone, Deserialize, Serialize)]
pub struct RefreshMessage<P> {
    party_index: usize,
    fairness_proof_vec: Vec<FairnessProof<P>>,
    coefficients_committed_vec: VerifiableSS<P>,
    points_committed_vec: Vec<P>,
    points_encrypted_vec: Vec<BigInt>,
    dk_correctness_proof: NICorrectKeyProof,
    ek: EncryptionKey,
    remove_party_indices: Vec<usize>,
    new_party: bool,
}

impl<P> RefreshMessage<P> {
    pub fn distribute_new_party(t: usize, n: usize) -> (Self, Keys)
    where
        P: ECPoint + Clone + Zeroize,
        P::Scalar: PartialEq + Clone + Debug + Zeroize,
    {
        // the new party does not know yet what index will it receive at this point.
        // We use the 0 index as the "unknown yet" index
        let default_index = 0;

        let new_party_key = Keys::create(default_index);

        // generate a dummy refresh message
        // this can be replaced at some point by a JoinMessage that contains only the key + proof
        let refresh_message = RefreshMessage {
            // in a join message, we only care about the ek and the correctness proof
            ek: new_party_key.ek.clone(),
            dk_correctness_proof: NICorrectKeyProof::proof(&new_party_key.dk, None),
            new_party: true,

            // these fields need to be filled/generated while refreshing
            party_index: default_index,
            fairness_proof_vec: Vec::new(),
            coefficients_committed_vec: VerifiableSS {
                parameters: ShamirSecretSharing {
                    threshold: t,
                    share_count: n,
                },
                commitments: vec![],
            },
            points_committed_vec: Vec::new(),
            points_encrypted_vec: Vec::new(),
            remove_party_indices: Vec::new(),
        };

        (refresh_message, new_party_key)
    }

    pub fn distribute(local_key: &LocalKey<P>) -> (Self, DecryptionKey)
    where
        P: ECPoint + Clone + Zeroize,
        P::Scalar: PartialEq + Clone + Debug + Zeroize,
    {
        let secret = local_key.keys_linear.x_i.clone();
        // secret share old key
        let (vss_scheme, secret_shares) =
            VerifiableSS::<P>::share(local_key.t as usize, local_key.n as usize, &secret);

        // commit to points on the polynomial
        let points_committed_vec: Vec<_> = (0..secret_shares.len())
            .map(|i| P::generator() * secret_shares[i].clone())
            .collect();

        //encrypt points on the polynomial using Paillier keys
        let (points_encrypted_vec, randomness_vec): (Vec<_>, Vec<_>) = (0..secret_shares.len())
            .map(|i| {
                let randomness = BigInt::sample_below(&local_key.paillier_key_vec[i].n);
                let ciphertext = Paillier::encrypt_with_chosen_randomness(
                    &local_key.paillier_key_vec[i],
                    RawPlaintext::from(secret_shares[i].to_big_int()),
                    &Randomness::from(randomness.clone()),
                )
                .0
                .into_owned();
                (ciphertext, randomness)
            })
            .unzip();

        // generate proof of fairness for each {point_committed, point_encrypted} pair
        let fairness_proof_vec: Vec<_> = (0..secret_shares.len())
            .map(|i| {
                let witness = FairnessWitness {
                    x: secret_shares[i].clone(),
                    r: randomness_vec[i].clone(),
                };
                let statement = FairnessStatement {
                    ek: local_key.paillier_key_vec[i].clone(),
                    c: points_encrypted_vec[i].clone(),
                    Y: points_committed_vec[i].clone(),
                };
                FairnessProof::prove(&witness, &statement)
            })
            .collect();

        let (ek, dk) = Paillier::keypair().keys();
        let dk_correctness_proof = NICorrectKeyProof::proof(&dk, None);

        (
            RefreshMessage {
                party_index: local_key.i as usize,
                fairness_proof_vec,
                coefficients_committed_vec: vss_scheme,
                points_committed_vec,
                points_encrypted_vec,
                dk_correctness_proof,
                ek,
                remove_party_indices: Vec::new(),
                new_party: false,
            },
            dk,
        )
    }

    pub fn validate_collect(refresh_messages: &[Self], t: usize, n: usize) -> FsDkrResult<()>
    where
        P: ECPoint + Clone + Zeroize + Debug,
        P::Scalar: PartialEq + Clone + Debug + Zeroize,
    {
        // check we got at least threshold t refresh messages
        if refresh_messages.len() <= t {
            return Err(FsDkrError::PartiesThresholdViolation {
                threshold: t as u16,
                refreshed_keys: refresh_messages.len(),
            });
        }

        // check all vectors are of same length
        let reference_len = refresh_messages[0].fairness_proof_vec.len();

        for (k, refresh_message) in refresh_messages.iter().enumerate() {
            let fairness_proof_len = refresh_message.fairness_proof_vec.len();
            let points_commited_len = refresh_message.points_committed_vec.len();
            let points_encrypted_len = refresh_message.points_encrypted_vec.len();

            if !(fairness_proof_len == reference_len
                && points_commited_len == reference_len
                && points_encrypted_len == reference_len)
            {
                return Err(FsDkrError::SizeMismatchError {
                    refresh_message_index: k,
                    fairness_proof_len,
                    points_commited_len,
                    points_encrypted_len,
                });
            }
        }

        for refresh_message in refresh_messages.iter() {
            for i in 0..n {
                //TODO: we should handle the case of t<i<n
                if refresh_message
                    .coefficients_committed_vec
                    .validate_share_public(&refresh_message.points_committed_vec[i], i + 1)
                    .is_err()
                {
                    return Err(FsDkrError::PublicShareValidationError);
                }
            }
        }

        Ok(())
    }

    pub fn collect_new_party(
        refresh_messages: &[Self],
        paillier_key: Keys,
        party_index: usize,
        t: usize,
        n: usize,
    ) -> FsDkrResult<LocalKey<P>>
    where
        P: ECPoint + Clone + Zeroize + Debug,
        P::Scalar: PartialEq + Clone + Debug + Zeroize,
    {
        RefreshMessage::validate_collect(refresh_messages, t, n)?;

        let parameters = ShamirSecretSharing {
            threshold: t,
            share_count: n,
        };

        let (cipher_text_sum, li_vec) = RefreshMessage::get_ciphertext_sum(
            refresh_messages,
            party_index,
            &parameters,
            &paillier_key.ek,
        );
        let new_share = Paillier::decrypt(&paillier_key.dk, cipher_text_sum)
            .0
            .into_owned();

        let new_share_fe: P::Scalar = ECScalar::from(&new_share);
        let paillier_dk = paillier_key.dk.clone();
        let key_linear_x_i = new_share_fe.clone();
        let key_linear_y = P::generator() * new_share_fe.clone();
        let keys_linear = SharedKeys {
            x_i: key_linear_x_i,
            y: key_linear_y,
        };
        let mut pk_vec: Vec<_> = (0..n)
            .map(|i| refresh_messages[0].points_committed_vec[i].clone() * li_vec[0].clone())
            .collect();

        for i in 0..n as usize {
            for j in 1..(t as usize + 1) {
                pk_vec[i] = pk_vec[i].clone()
                    + refresh_messages[j].points_committed_vec[i].clone() * li_vec[j].clone();
            }
        }

        let available_parties: HashMap<usize, EncryptionKey> = refresh_messages
            .iter()
            .map(|msg| (msg.party_index, msg.ek.clone()))
            .collect();

        let paillier_key_vec: Vec<EncryptionKey> = (1..n + 1)
            .map(|party| {
                let ek = available_parties.get(&party);

                // TODO: hacky, here I generate a dummy key if the given index is not in the
                // computation. This needs a better reasoning
                match ek {
                    None => Paillier::keypair().keys().0,
                    Some(key) => key.clone(),
                }
            })
            .collect();

        // secret share old key
        let (vss_scheme, _) = VerifiableSS::<P>::share(t, n, &new_share_fe);

        let local_key = LocalKey {
            paillier_dk,
            pk_vec,
            keys_linear,
            paillier_key_vec,
            // TODO: not really sure how to handle y_sum_s and h1_h2_n_tilde_vec
            y_sum_s: P::generator(),
            h1_h2_n_tilde_vec: [].to_vec(),
            vss_scheme,
            i: party_index as u16,
            t: t as u16,
            n: n as u16,
        };

        Ok(local_key)
    }

    fn get_ciphertext_sum<'a>(
        refresh_messages: &'a [Self],
        party_index: usize,
        parameters: &'a ShamirSecretSharing,
        ek: &'a EncryptionKey,
    ) -> (RawCiphertext<'a>, Vec<P::Scalar>)
    where
        P: ECPoint + Clone + Zeroize + Debug,
        P::Scalar: PartialEq + Clone + Debug + Zeroize,
    {
        // TODO: check we have large enough qualified set , at least t+1
        //decrypt the new share
        // we first homomorphically add all ciphertext encrypted using our encryption key
        let ciphertext_vec: Vec<_> = (0..refresh_messages.len())
            .map(|k| refresh_messages[k].points_encrypted_vec[(party_index - 1) as usize].clone())
            .collect();

        let indices: Vec<_> = (0..(parameters.threshold + 1) as usize)
            .map(|i| refresh_messages[i].party_index - 1)
            .collect();

        // optimization - one decryption
        let li_vec: Vec<_> = (0..parameters.threshold as usize + 1)
            .map(|i| {
                VerifiableSS::<P>::map_share_to_new_params(
                    parameters.clone().borrow(),
                    indices[i],
                    &indices,
                )
            })
            .collect();

        let ciphertext_vec_at_indices_mapped: Vec<_> = (0..(parameters.threshold + 1) as usize)
            .map(|i| {
                Paillier::mul(
                    ek,
                    RawCiphertext::from(ciphertext_vec[i].clone()),
                    RawPlaintext::from(li_vec[i].to_big_int()),
                )
            })
            .collect();

        let ciphertext_sum = ciphertext_vec_at_indices_mapped.iter().fold(
            Paillier::encrypt(ek, RawPlaintext::from(BigInt::zero())),
            |acc, x| Paillier::add(ek, acc, x.clone()),
        );

        (ciphertext_sum, li_vec)
    }

    pub fn collect(
        refresh_messages: &[Self],
        mut local_key: &mut LocalKey<P>,
        new_dk: DecryptionKey,
        new_parties: &[Self],
    ) -> FsDkrResult<()>
    where
        P: ECPoint + Clone + Zeroize + Debug,
        P::Scalar: PartialEq + Clone + Debug + Zeroize,
    {
        RefreshMessage::validate_collect(
            refresh_messages,
            local_key.t as usize,
            local_key.n as usize,
        )?;

        let mut statement: FairnessStatement<P>;
        for refresh_message in refresh_messages.iter() {
            for i in 0..(local_key.n as usize) {
                statement = FairnessStatement {
                    ek: local_key.paillier_key_vec[i].clone(),
                    c: refresh_message.points_encrypted_vec[i].clone(),
                    Y: refresh_message.points_committed_vec[i].clone(),
                };
                if refresh_message.fairness_proof_vec[i]
                    .verify(&statement)
                    .is_err()
                {
                    let proof = refresh_message.fairness_proof_vec[i].clone();
                    proof.verify(&statement).unwrap();
                    return Err(FsDkrError::FairnessProof);
                }
            }
        }

        let old_ek = local_key.paillier_key_vec[(local_key.i - 1) as usize].clone();
        let (cipher_text_sum, li_vec) = RefreshMessage::get_ciphertext_sum(
            refresh_messages,
            local_key.i as usize,
            &local_key.vss_scheme.parameters,
            &old_ek,
        );

        for refresh_message in refresh_messages.iter().chain(new_parties.iter()) {
            if refresh_message
                .dk_correctness_proof
                .verify(&refresh_message.ek, SALT_STRING)
                .is_err()
            {
                return Err(FsDkrError::PaillierVerificationError {
                    party_index: refresh_message.party_index,
                });
            }

            // if the proof checks, we add the new paillier public key to the key
            local_key.paillier_key_vec[refresh_message.party_index - 1] =
                refresh_message.ek.clone();
        }

        let new_share = Paillier::decrypt(&local_key.paillier_dk, cipher_text_sum)
            .0
            .into_owned();

        let new_share_fe: P::Scalar = ECScalar::from(&new_share);

        // zeroize the old dk key
        local_key.paillier_dk.q.zeroize();
        local_key.paillier_dk.p.zeroize();
        local_key.paillier_dk = new_dk;

        // update old key and output new key
        local_key.keys_linear.x_i.zeroize();

        local_key.keys_linear.x_i = new_share_fe.clone();
        local_key.keys_linear.y = P::generator() * new_share_fe;

        // update local key list of local public keys (X_i = g^x_i is updated by adding all committed points to that party)
        for i in 0..local_key.n as usize {
            local_key.pk_vec[i] =
                refresh_messages[0].points_committed_vec[i].clone() * li_vec[0].clone();
            for j in 1..local_key.t as usize + 1 {
                local_key.pk_vec[i] = local_key.pk_vec[i].clone()
                    + refresh_messages[j].points_committed_vec[i].clone() * li_vec[j].clone();
            }
        }

        Ok(())
    }
}
