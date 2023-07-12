use std::ops::{Mul};
use ff::*;
use rand::{thread_rng};
use bls12_381::{G1Projective, Scalar};
use pairing::group::{GroupEncoding};
use sha2::{Sha256, Digest};
use crate::utils;

pub struct NIZKPoKProof {
    com: G1Projective,
    rsp: Scalar
}

pub fn nizkpok_hash(com: &G1Projective, pubkey: &G1Projective) -> Scalar {
    let mut hasher = Sha256::new();
    hasher.update(com.to_bytes());
    hasher.update(pubkey.to_bytes());
    let mut hval: [u8; 32] = hasher.finalize()[..].try_into().expect("slice with incorrect length");
    hval[31] = 0; // hval < order r since Scalar is represented as a*R mod r

    let chl = Scalar::from_bytes(&hval).unwrap();
    chl
}

pub fn schnorr_prove(pubkey: &G1Projective, privkey: &Scalar) -> NIZKPoKProof {
    let mut rng = thread_rng();
    let g1 = utils::get_generator_in_g1();

    let rnd = Scalar::random(&mut rng);
    let com = utils::commit_in_g1(&g1, &rnd);
    let chl = nizkpok_hash(&com, pubkey);
    let rsp = rnd + chl * privkey;
    
    NIZKPoKProof { com: com, rsp: rsp }
}

pub fn schnorr_verify(proof: &NIZKPoKProof, pubkey: &G1Projective) -> bool {
    let g1 = utils::get_generator_in_g1();
    
    let check_lhs = utils::commit_in_g1(&g1, &proof.rsp);
    let chl = nizkpok_hash(&proof.com, pubkey);
    let check_rhs = proof.com + pubkey.mul(&chl);
    
    check_lhs == check_rhs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nizkpok_correctness() {
        let mut rng = thread_rng();
        let g1 = utils::get_generator_in_g1();

        for i in 0..100 {
            let privkey = Scalar::random(&mut rng);
            //let privkey = Scalar::from(i);
            let pubkey = utils::commit_in_g1(&g1, &privkey);

            let proof = schnorr_prove(&pubkey, &privkey);
            if schnorr_verify(&proof, &pubkey) != true {
                println!("fail: {}", i);
                return
            }
        }

        println!("nizkpok ok")
    }
}
