#![cfg_attr(feature = "cargo-clippy", allow(clippy::many_single_char_names))]

mod error;
mod proof_of_fairness;

use crate::error::{FsDkrError, FsDkrResult};
use crate::proof_of_fairness::{FairnessProof, FairnessStatement, FairnessWitness};
use curv::arithmetic::{Samplable, Zero};
use curv::cryptographic_primitives::secret_sharing::feldman_vss::VerifiableSS;
use curv::elliptic::curves::traits::{ECPoint, ECScalar};
use curv::BigInt;
use multi_party_ecdsa::protocols::multi_party_ecdsa::gg_2020::state_machine::keygen::LocalKey;
use paillier::{
    Add, Decrypt, DecryptionKey, Encrypt, EncryptWithChosenRandomness, EncryptionKey,
    KeyGeneration, Mul, Paillier, Randomness, RawCiphertext, RawPlaintext,
};
use std::fmt::Debug;
use zeroize::Zeroize;
use zk_paillier::zkproofs::{NICorrectKeyProof, SALT_STRING};

// Everything here can be broadcasted
#[derive(Clone)]
pub struct RefreshMessage<P> {
    party_index: usize,
    fairness_proof_vec: Vec<FairnessProof<P>>,
    coefficients_committed_vec: VerifiableSS<P>,
    points_committed_vec: Vec<P>,
    points_encrypted_vec: Vec<BigInt>,
    dk_correctness_proof: NICorrectKeyProof,
    ek: EncryptionKey,
    remove_party_indices: Vec<usize>,
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
                ek,
                remove_party_indices: Vec::new(),
            },
            dk,
        )
    }

    // TODO: change Vec<Self> to slice
    pub fn collect(
        refresh_messages: &[Self],
        mut local_key: &mut LocalKey<P>,
        new_dk: DecryptionKey,
    ) -> FsDkrResult<()>
    where
        P: ECPoint + Clone + Zeroize + Debug,
        P::Scalar: PartialEq + Clone + Debug + Zeroize,
    {
        // check we got at least threshold t refresh messages
        if refresh_messages.len() <= local_key.t as usize {
            return Err(FsDkrError::PartiesThresholdViolation {
                threshold: local_key.t,
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

        // TODO: for all parties: check that commitment to zero coefficient is the same as local public key
        // for each refresh message: check that SUM_j{i^j * C_j} = points_committed_vec[i] for all i
        // TODO: paralleize
        for refresh_message in refresh_messages.iter() {
            for i in 0..(local_key.n as usize) {
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

        // verify all  fairness proofs
        let mut statement: FairnessStatement<P>;
        for refresh_message in refresh_messages.iter() {
            for i in 0..(local_key.n as usize) {
                //TODO: we should handle the case of t<i<n
                statement = FairnessStatement {
                    ek: local_key.paillier_key_vec[i].clone(),
                    c: refresh_message.points_encrypted_vec[i].clone(),
                    Y: refresh_message.points_committed_vec[i].clone(),
                };
                if refresh_message.fairness_proof_vec[i]
                    .verify(&statement)
                    .is_err()
                {
                    return Err(FsDkrError::FairnessProof);
                }
            }
        }

        // TODO: check we have large enough qualified set , at least t+1
        //decrypt the new share
        // we first homomorphically add all ciphertext encrypted using our encryption key
        let ciphertext_vec: Vec<_> = (0..refresh_messages.len())
            .map(|k| refresh_messages[k].points_encrypted_vec[(local_key.i - 1) as usize].clone())
            .collect();

        let indices: Vec<_> = (0..(local_key.t + 1) as usize)
            .map(|i| refresh_messages[i].party_index - 1)
            .collect();
        // optimization - one decryption
        let li_vec: Vec<_> = (0..local_key.t as usize + 1)
            .map(|i| {
                VerifiableSS::<P>::map_share_to_new_params(
                    &local_key.vss_scheme.parameters,
                    indices[i],
                    &indices,
                )
            })
            .collect();
        let ciphertext_vec_at_indices_mapped: Vec<_> = (0..(local_key.t + 1) as usize)
            .map(|i| {
                Paillier::mul(
                    &local_key.paillier_key_vec[local_key.i as usize - 1],
                    RawCiphertext::from(ciphertext_vec[i].clone()),
                    RawPlaintext::from(li_vec[i].to_big_int()),
                )
            })
            .collect();

        let cipher_text_sum = ciphertext_vec_at_indices_mapped.iter().fold(
            Paillier::encrypt(
                &local_key.paillier_key_vec[local_key.i as usize - 1],
                RawPlaintext::from(BigInt::zero()),
            ),
            |acc, x| {
                Paillier::add(
                    &local_key.paillier_key_vec[local_key.i as usize - 1],
                    acc,
                    x.clone(),
                )
            },
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

#[cfg(test)]
mod tests {
    use crate::RefreshMessage;
    use curv::arithmetic::Converter;
    use curv::cryptographic_primitives::hashing::hash_sha256::HSha256;
    use curv::cryptographic_primitives::hashing::traits::Hash;
    use curv::cryptographic_primitives::secret_sharing::feldman_vss::{
        ShamirSecretSharing, VerifiableSS,
    };
    use curv::elliptic::curves::secp256_k1::GE;
    use curv::BigInt;
    use multi_party_ecdsa::protocols::multi_party_ecdsa::gg_2020::party_i::verify;
    use multi_party_ecdsa::protocols::multi_party_ecdsa::gg_2020::state_machine::keygen::{
        Keygen, LocalKey,
    };
    use multi_party_ecdsa::protocols::multi_party_ecdsa::gg_2020::state_machine::sign::{
        CompletedOfflineStage, OfflineStage, SignManual,
    };
    use paillier::DecryptionKey;
    use round_based::dev::Simulation;
    use std::collections::HashMap;

    #[test]
    fn test1() {
        //simulate keygen
        let t = 3;
        let n = 5;
        let mut keys = simulate_keygen(t, n);

        let old_keys = keys.clone();
        simulate_dkr(&mut keys);

        // check that sum of old keys is equal to sum of new keys
        let old_linear_secret_key: Vec<_> = (0..old_keys.len())
            .map(|i| old_keys[i].keys_linear.x_i)
            .collect();

        let new_linear_secret_key: Vec<_> =
            (0..keys.len()).map(|i| keys[i].keys_linear.x_i).collect();
        let indices: Vec<_> = (0..(t + 1) as usize).collect();
        let vss = VerifiableSS::<GE> {
            parameters: ShamirSecretSharing {
                threshold: t as usize,
                share_count: n as usize,
            },
            commitments: Vec::new(),
        };
        assert_eq!(
            vss.reconstruct(&indices[..], &old_linear_secret_key[0..(t + 1) as usize]),
            vss.reconstruct(&indices[..], &new_linear_secret_key[0..(t + 1) as usize])
        );
        assert_ne!(old_linear_secret_key, new_linear_secret_key);
    }

    #[test]
    fn test_sign_rotate_sign() {
        let mut keys = simulate_keygen(2, 5);
        let offline_sign = simulate_offline_stage(keys.clone(), &[1, 2, 3]);
        simulate_signing(offline_sign, b"ZenGo");
        simulate_dkr(&mut keys);
        let offline_sign = simulate_offline_stage(keys.clone(), &[2, 3, 4]);
        simulate_signing(offline_sign, b"ZenGo");
        simulate_dkr(&mut keys);
        let offline_sign = simulate_offline_stage(keys, &[1, 3, 5]);
        simulate_signing(offline_sign, b"ZenGo");
    }

    #[test]
    fn test_remove_sign_rotate_sign() {
        let mut keys = simulate_keygen(2, 5);
        let offline_sign = simulate_offline_stage(keys.clone(), &[1, 2, 3]);
        simulate_signing(offline_sign, b"ZenGo");
        simulate_dkr_removal(&mut keys, [1].to_vec());
        let offline_sign = simulate_offline_stage(keys.clone(), &[2, 3, 4]);
        simulate_signing(offline_sign, b"ZenGo");
        simulate_dkr_removal(&mut keys, [1, 2].to_vec());
        let offline_sign = simulate_offline_stage(keys, &[3, 4, 5]);
        simulate_signing(offline_sign, b"ZenGo");
    }

    fn simulate_keygen(t: u16, n: u16) -> Vec<LocalKey> {
        //simulate keygen
        let mut simulation = Simulation::new();
        simulation.enable_benchmarks(false);

        for i in 1..=n {
            simulation.add_party(Keygen::new(i, t, n).unwrap());
        }

        simulation.run().unwrap()
    }

    fn simulate_dkr_removal(keys: &mut Vec<LocalKey>, remove_party_indices: Vec<usize>) {
        // removal of a party is simply done by not broadcasting the encrypted messages to it.
        // if enough parties decide on that for a party index, they will not be able to reconstruct
        // a rotated key.
        let mut broadcast_messages: HashMap<usize, Vec<RefreshMessage<GE>>> = HashMap::new();
        let mut new_dks: HashMap<usize, DecryptionKey> = HashMap::new();
        let mut refresh_messages: Vec<RefreshMessage<GE>> = Vec::new();
        let mut party_key: HashMap<usize, LocalKey> = HashMap::new();

        for key in keys.iter_mut() {
            let (refresh_message, new_dk) = RefreshMessage::distribute(key);
            refresh_messages.push(refresh_message.clone());
            new_dks.insert(refresh_message.party_index, new_dk);
            party_key.insert(refresh_message.party_index, key.clone());
        }

        for refresh_message in refresh_messages.iter() {
            broadcast_messages.insert(refresh_message.party_index, Vec::new());
        }

        for refresh_message in refresh_messages.iter_mut() {
            if !remove_party_indices.contains(&refresh_message.party_index) {
                refresh_message.remove_party_indices = remove_party_indices.clone();
            } else {
                let mut new_remove_party_indices = remove_party_indices.clone();
                new_remove_party_indices.retain(|value| *value != refresh_message.party_index);
                refresh_message.remove_party_indices = new_remove_party_indices;
            }

            for (party_index, refresh_bucket) in broadcast_messages.iter_mut() {
                if refresh_message.remove_party_indices.contains(party_index) {
                    continue;
                }
                refresh_bucket.push(refresh_message.clone());
            }
        }

        for remove_party_index in remove_party_indices.iter() {
            assert_eq!(broadcast_messages[remove_party_index].len(), 1);
        }

        // keys will be updated to refreshed values
        for (party, key) in party_key.iter_mut() {
            if remove_party_indices.contains(party) {
                continue;
            }

            RefreshMessage::collect(
                broadcast_messages[party].clone().as_slice(),
                key,
                new_dks[party].clone(),
            )
            .expect("");
        }

        for remove_party_index in remove_party_indices {
            let result = RefreshMessage::collect(
                &broadcast_messages[&remove_party_index],
                &mut keys[remove_party_index],
                new_dks[&remove_party_index].clone(),
            );
            assert!(result.is_err());
        }
    }

    fn simulate_dkr(keys: &mut Vec<LocalKey>) -> (Vec<RefreshMessage<GE>>, Vec<DecryptionKey>) {
        let mut broadcast_vec: Vec<RefreshMessage<GE>> = Vec::new();
        let mut new_dks: Vec<DecryptionKey> = Vec::new();

        for key in keys.iter() {
            let (refresh_message, new_dk) = RefreshMessage::distribute(key);
            broadcast_vec.push(refresh_message);
            new_dks.push(new_dk);
        }

        // keys will be updated to refreshed values
        for i in 0..keys.len() as usize {
            RefreshMessage::collect(&broadcast_vec, &mut keys[i], new_dks[i].clone()).expect("");
        }

        (broadcast_vec, new_dks)
    }

    fn simulate_offline_stage(
        local_keys: Vec<LocalKey>,
        s_l: &[u16],
    ) -> Vec<CompletedOfflineStage> {
        let mut simulation = Simulation::new();
        simulation.enable_benchmarks(false);

        for (i, &keygen_i) in (1..).zip(s_l) {
            simulation.add_party(
                OfflineStage::new(
                    i,
                    s_l.to_vec(),
                    local_keys[usize::from(keygen_i - 1)].clone(),
                )
                .unwrap(),
            );
        }

        simulation.run().unwrap()
    }

    fn simulate_signing(offline: Vec<CompletedOfflineStage>, message: &[u8]) {
        let message = HSha256::create_hash(&[&BigInt::from_bytes(message)]);
        let pk = *offline[0].public_key();

        let parties = offline
            .iter()
            .map(|o| SignManual::new(message.clone(), o.clone()))
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let (parties, local_sigs): (Vec<_>, Vec<_>) = parties.into_iter().unzip();
        // parties.remove(0).complete(&local_sigs[1..]).unwrap();
        let local_sigs_except = |i: usize| {
            let mut v = vec![];
            v.extend_from_slice(&local_sigs[..i]);
            if i + 1 < local_sigs.len() {
                v.extend_from_slice(&local_sigs[i + 1..]);
            }
            v
        };

        assert!(parties
            .into_iter()
            .enumerate()
            .map(|(i, p)| p.complete(&local_sigs_except(i)).unwrap())
            .all(|signature| verify(&signature, &pk, &message).is_ok()));
    }
}
