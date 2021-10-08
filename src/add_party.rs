use crate::error::FsDkrResult;
use crate::refresh_message::RefreshMessage;
use curv::arithmetic::{BasicOps, Modulo, One, Samplable, Zero};
use curv::cryptographic_primitives::secret_sharing::feldman_vss::{
    ShamirSecretSharing, VerifiableSS,
};
use curv::elliptic::curves::traits::{ECPoint, ECScalar};
use curv::BigInt;
use multi_party_ecdsa::protocols::multi_party_ecdsa::gg_2018::party_i::Keys;
use multi_party_ecdsa::protocols::multi_party_ecdsa::gg_2020::party_i::SharedKeys;
use multi_party_ecdsa::protocols::multi_party_ecdsa::gg_2020::state_machine::keygen::LocalKey;
pub use paillier::DecryptionKey;
use paillier::{Decrypt, EncryptionKey, KeyGeneration, Paillier};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt::Debug;
use zeroize::Zeroize;
use zk_paillier::zkproofs::{DLogStatement, NICorrectKeyProof};

// Everything here can be broadcasted
#[derive(Clone, Deserialize, Serialize, Debug)]
pub struct JoinMessage {
    pub(crate) ek: EncryptionKey,
    pub(crate) dk_correctness_proof: NICorrectKeyProof,
    pub(crate) party_index: Option<usize>,
    pub(crate) dlog_statement: DLogStatement,
}

impl JoinMessage {
    pub fn distribute() -> (Self, Keys) {
        let new_party_key = Keys::create(0);

        let (ek_tilde, dk_tilde) = Paillier::keypair().keys();
        let one = BigInt::one();
        let phi = (&dk_tilde.p - &one) * (&dk_tilde.q - &one);
        let h1 = BigInt::sample_below(&phi);
        let s = BigInt::from(2).pow(256 as u32);
        let xhi = BigInt::sample_below(&s);
        let h1_inv = BigInt::mod_inv(&h1, &ek_tilde.n).unwrap();
        let h2 = BigInt::mod_pow(&h1_inv, &xhi, &ek_tilde.n);

        let dlog_statement = DLogStatement {
            N: ek_tilde.n.clone(),
            g: h1.clone(),
            ni: h2.clone(),
        };

        let join_message = JoinMessage {
            // in a join message, we only care about the ek and the correctness proof
            ek: new_party_key.ek.clone(),
            dk_correctness_proof: NICorrectKeyProof::proof(&new_party_key.dk, None),
            dlog_statement,
            party_index: None,
        };

        (join_message, new_party_key)
    }

    pub fn collect<P>(
        refresh_messages: &[RefreshMessage<P>],
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
            .chain(std::iter::once((party_index, paillier_key.ek)))
            .collect();

        let paillier_key_vec: Vec<EncryptionKey> = (1..n + 1)
            .map(|party| {
                let ek = available_parties.get(&party);

                match ek {
                    None => EncryptionKey {
                        n: BigInt::zero(),
                        nn: BigInt::zero(),
                    },
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
}