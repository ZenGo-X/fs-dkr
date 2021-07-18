mod proof_of_fairness;

use curv::cryptographic_primitives::secret_sharing::feldman_vss::VerifiableSS;
use curv::elliptic::curves::secp256_k1::GE;
use curv::elliptic::curves::traits::ECPoint;
use multi_party_ecdsa::protocols::multi_party_ecdsa::gg_2020::state_machine::keygen::LocalKey;
use paillier::{Encrypt, Paillier};
use std::fmt::Debug;

pub struct RefreshMessage {}

impl RefreshMessage {
    pub fn distribute<P>(old_key: &LocalKey)
    //-> Self
    where
        P: ECPoint + Clone,
        P::Scalar: PartialEq + Clone + Debug,
    {
        let secret = old_key.keys_linear.x_i;
        // secret share old key
        let (vss_scheme, secret_shares) =
            VerifiableSS::<GE>::share(old_key.t as usize, old_key.n as usize, &secret);
        // commit to points on the polynomial
        let points_committed_vec: Vec<_> = (1..old_key.t as usize + 1)
            .map(|i| vss_scheme.get_point_commitment(i))
            .collect();

        //encrypt points on the polynomial using Paillier keys
        //    let points_encrypted_vec : Vec<_>= (0..old_key.t as usize).map(|i|{
        //         Paillier::encrypt(&old_key.paillier_key_vec[i], &points_vec[i].to_big_int());
        //    }).collect();
    }

    pub fn collect(refresh_messages: &Vec<Self>) //-> LocalKey
    {
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
