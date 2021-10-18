use crate::add_party::JoinMessage;
use crate::error::{FsDkrError, FsDkrResult};
use crate::proof_of_fairness::{FairnessProof, FairnessStatement, FairnessWitness};
use curv::arithmetic::{Samplable, Zero};
use curv::cryptographic_primitives::secret_sharing::feldman_vss::{
    ShamirSecretSharing, VerifiableSS,
};
use curv::elliptic::curves::traits::{ECPoint, ECScalar};
use curv::BigInt;
use multi_party_ecdsa::protocols::multi_party_ecdsa::gg_2020::state_machine::keygen::LocalKey;
pub use paillier::DecryptionKey;
use paillier::{
    Add, Decrypt, Encrypt, EncryptWithChosenRandomness, EncryptionKey, KeyGeneration, Mul,
    Paillier, Randomness, RawCiphertext, RawPlaintext,
};
use serde::{Deserialize, Serialize};
use std::borrow::Borrow;
use std::fmt::Debug;
use zeroize::Zeroize;
use zk_paillier::zkproofs::{DLogStatement, NICorrectKeyProof, SALT_STRING};

// Everything here can be broadcasted
#[derive(Clone, Deserialize, Serialize)]
pub struct RefreshMessage<P> {
    pub(crate) party_index: usize,
    fairness_proof_vec: Vec<FairnessProof<P>>,
    coefficients_committed_vec: VerifiableSS<P>,
    pub(crate) points_committed_vec: Vec<P>,
    points_encrypted_vec: Vec<BigInt>,
    dk_correctness_proof: NICorrectKeyProof,
    pub(crate) dlog_statement: DLogStatement,
    pub(crate) ek: EncryptionKey,
    pub(crate) remove_party_indices: Vec<usize>,
    pub(crate) public_key: P,
}

impl<P> RefreshMessage<P> {
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
                dlog_statement: local_key.h1_h2_n_tilde_vec[(local_key.i - 1) as usize].clone(),
                ek,
                remove_party_indices: Vec::new(),
                public_key: local_key.y_sum_s.clone(),
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

    pub(crate) fn get_ciphertext_sum<'a>(
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

    pub fn replace(
        new_parties: &mut [JoinMessage],
        key: &mut LocalKey<P>,
    ) -> FsDkrResult<(Self, DecryptionKey)>
    where
        P: ECPoint + Clone + Zeroize + Debug,
        P::Scalar: PartialEq + Clone + Debug + Zeroize,
    {
        for join_message in new_parties.iter_mut() {
            let party_index = join_message.get_party_index()?;
            join_message.party_index = Some(party_index);
            key.paillier_key_vec[party_index - 1] = join_message.ek.clone();
            key.h1_h2_n_tilde_vec[party_index - 1] = join_message.dlog_statement.clone();
        }

        Ok(RefreshMessage::distribute(key))
    }

    pub fn collect(
        refresh_messages: &[Self],
        mut local_key: &mut LocalKey<P>,
        new_dk: DecryptionKey,
        join_messages: &[&JoinMessage],
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
                refresh_message.fairness_proof_vec[i].verify(&statement)?;
            }
        }

        let old_ek = local_key.paillier_key_vec[(local_key.i - 1) as usize].clone();
        let (cipher_text_sum, li_vec) = RefreshMessage::get_ciphertext_sum(
            refresh_messages,
            local_key.i as usize,
            &local_key.vss_scheme.parameters,
            &old_ek,
        );

        for refresh_message in refresh_messages.iter() {
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

        for join_message in join_messages {
            let party_index = join_message.get_party_index()?;

            if join_message
                .dk_correctness_proof
                .verify(&join_message.ek, SALT_STRING)
                .is_err()
            {
                return Err(FsDkrError::PaillierVerificationError { party_index });
            }

            if join_message
                .composite_dlog_proof
                .verify(&join_message.dlog_statement)
                .is_err()
            {
                return Err(FsDkrError::DLogProofValidation { party_index });
            }

            // if the proof checks, we add the new paillier public key to the key
            local_key.paillier_key_vec[party_index - 1] = join_message.ek.clone();
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
