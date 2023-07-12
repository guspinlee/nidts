use std::ops::{Add, Mul, Neg};
use std::collections::{BTreeMap};
use std::collections::{HashMap};
use std::time::{Instant, Duration};
use ff::*;
use rand::{thread_rng};
use bls12_381::{pairing, G1Projective, G2Projective, Scalar};
use pairing::group::{Curve};
use crate::polynomial::*;
use crate::utils;
use crate::universe::*;
use crate::{XCoord, PartyId};
use crate::nizkpok::{NIZKPoKProof};
use crate::nizkpok;

pub struct NIDTSRegisterKey {
    pub party_regpubkey: Vec<G2Projective>,
    pub party_proof: Vec<NIZKPoKProof>
}

pub struct NIDTSCombineKey {
    pub evals_0: Vec<G1Projective>,     // evals_0 = { g1^{f(j)}, ... }
    pub hvals_1: Vec<G2Projective>      // hvals_1 = { hgid^{f(j)}, ... }
}

pub struct NIDTSVerificationKey {
    pub vk_0: G1Projective,             // g1^{f(0)}
    pub hgid: G2Projective              // hgid
}

pub struct NIDTSPartialSignature {
    pub party_id: PartyId,
    pub party_sigs: Vec<G2Projective>   // hm^s
}

pub struct NIDTSFullSignature {
    sigma_0: G2Projective,
    sigma_1: G1Projective,
    sigma_2: G2Projective
}

// generate party pubkey
pub fn nidts_generate_party_pubkey(secret: &Scalar, party_weight: usize) -> 
    Vec<G1Projective> {
    let g1 = utils::get_generator_in_g1();
    
    let mut party_pubkey = Vec::new();
    for i in 0..party_weight {
        let sk_i = secret + Scalar::from(i as u64);
        let pk_i = utils::commit_in_g1(&g1, &sk_i);
        party_pubkey.push(pk_i);
    }
    party_pubkey
}

// generate party regkey
pub fn nidts_generate_party_regkey(secret: &Scalar, party_pubkey: &Vec<G1Projective>,
    party_weight: usize, gid: &[u8]) -> NIDTSRegisterKey {
    let hgid = utils::hash_to_g2(gid);
    
    let mut party_regpubkey = Vec::new();
    let mut party_proof = Vec::new();

    for i in 0..party_weight {
        let sk_i = secret + Scalar::from(i as u64);
        let rpk_i = hgid.mul(sk_i);
        let proof_i = nizkpok::schnorr_prove(&party_pubkey[i], &sk_i);
        party_regpubkey.push(rpk_i);
        party_proof.push(proof_i);
    }
    
    NIDTSRegisterKey { 
        party_regpubkey: party_regpubkey, 
        party_proof: party_proof
    }
}

// verify party pubkey and regkey
fn verify_party_pubkey_and_regkey(party_pubkey: &Vec<G1Projective>, party_regkey: &NIDTSRegisterKey, 
    hgid: &G2Projective) -> bool {
    let mut rng = thread_rng();
    let g1 = utils::get_generator_in_g1();
    let party_weight = party_pubkey.len();

    // pubkey and regpubkey
    let mut rnds = Vec::new();
    if party_weight == 1 {
        let rnd_0 = Scalar::from(1);
        rnds.push(rnd_0);
    } else {
        for _i in 0..party_weight {
            let rnd_i = Scalar::random(&mut rng);
            rnds.push(rnd_i);
        }
    }

    let rnd_pubkey = utils::multi_exp_g1_fast(party_pubkey.as_slice(), rnds.as_slice());
    let rnd_regpubkey = utils::multi_exp_g2_fast(party_regkey.party_regpubkey.as_slice(), rnds.as_slice());

    let check_lhs = pairing(&rnd_pubkey.to_affine(), &hgid.to_affine());
    let check_rhs = pairing(&g1.to_affine(), &rnd_regpubkey.to_affine());
    if check_lhs != check_rhs { return false }

    // nizkpok proof
    for i in 0..party_weight {
        let valid = nizkpok::schnorr_verify(&party_regkey.party_proof[i], &party_pubkey[i]);
        if valid != true { return false }
    }
    true
}

// verify all pubkeys and regkeys
fn verify_universe_all_pubkeys_and_regkeys(universe: &NIDTSUniverse, gid: &[u8], 
    all_regkeys: &Vec<NIDTSRegisterKey>) -> bool {
    let hgid = utils::hash_to_g2(gid);

    for party in universe.get_parties_in_canonical_ordering().iter() {
        let party_pubkey = universe.get_pubkeys(party);
        let party_regkey = &all_regkeys[*party];
        
        let valid = verify_party_pubkey_and_regkey(&party_pubkey, &party_regkey, &hgid);
        if valid == false { return false; }
    }
    true
}

// compute public points for vk_0, evals_0, and hvals_1
fn compute_universe_public_points(universe: &NIDTSUniverse, all_regkeys: &Vec<NIDTSRegisterKey>) -> 
    (G1Projective, Vec<G1Projective>, Vec<G2Projective>) {
    let w = universe.get_total_weight();
    let t = universe.get_threshold();
    
    let mut lag_dur = Duration::new(0, 0);
    let mut exp_dur = Duration::new(0, 0);

    // get all pubkeys in canonical order
    let all_pubkeys: Vec<G1Projective> = universe.get_all_pubkeys();
    let mut all_regpubkeys: Vec<G2Projective> = Vec::new();
    for i in 0..all_regkeys.len() {
        let party_regpubkey = &all_regkeys[i].party_regpubkey;
        all_regpubkeys.append(&mut party_regpubkey.clone());
    }

    // compute x-coords of all signer points to compute lagrange coeffs
    let _par_xs: Vec<XCoord> = (1..w+1).collect();
    let par_xs: Vec<Scalar> = _par_xs.iter().map(|&x| Scalar::from(x as u64)).collect();

    let _pub_xs: Vec<XCoord> = ((w+1)..(2*w-t + 1)).collect();
    let pub_xs: Vec<Scalar> = _pub_xs.iter().map(|&x| Scalar::from(x as u64)).collect();

    // compute evals_0 = { g^f(w+1), ... g^{2w-t} }
    let mut evals_0: Vec<G1Projective> = Vec::new();
    let mut hvals_1: Vec<G2Projective> = Vec::new();
    
    // barycentric
    let baryws = Polynomial::lagrange_coefficients_barycentric_init(par_xs.as_slice());
    for x in pub_xs {
        // compute lagrange coefficients and g^f(x) and h2^f(x)
        let now = Instant::now();
        let lcs: Vec<Scalar> = Polynomial::lagrange_coefficients_barycentric(&baryws, par_xs.as_slice(), &x);
        lag_dur += now.elapsed();

        let now = Instant::now();
        let gfx = utils::multi_exp_g1_fast(all_pubkeys.as_slice(), lcs.as_slice());
        let hfx = utils::multi_exp_g2_fast(all_regpubkeys.as_slice(), lcs.as_slice());
        exp_dur += now.elapsed();

        evals_0.push(gfx);
        hvals_1.push(hfx);
    }

    // compute g^f(0)
    let now = Instant::now();
    //let lcs: Vec<Scalar> = Polynomial::lagrange_coefficients_naive(par_xs.as_slice(), &Scalar::from(0));
    let lcs: Vec<Scalar> = Polynomial::lagrange_coefficients(par_xs.as_slice());
    lag_dur += now.elapsed();
    println!("- lagrange coeffs time:\t {}.{:03}", lag_dur.as_secs(), lag_dur.subsec_millis());

    let now = Instant::now();
    let vk_0 = utils::multi_exp_g1_fast(all_pubkeys.as_slice(), lcs.as_slice());
    exp_dur += now.elapsed();
    println!("- lagrange mulexp time:\t {}.{:03}", exp_dur.as_secs(), exp_dur.subsec_millis());

    // return g^f(0), {g^f(w+1), ..., g^f(2w-t+1)}, ...
    (vk_0, evals_0, hvals_1)
}

// universe setup in offline
pub fn nidts_universe_setup(universe: &NIDTSUniverse, gid: &[u8], all_regkeys: &Vec<NIDTSRegisterKey>) -> 
    (NIDTSCombineKey, NIDTSVerificationKey) {
    // verify all public keys
    let now = Instant::now();
    let valid = verify_universe_all_pubkeys_and_regkeys(universe, gid, all_regkeys);
    assert_eq!(valid, true);
    let dur = now.elapsed();
    println!("- verify pubkeys time: \t {}.{:03}", dur.as_secs(), dur.subsec_millis());

    // compute vk_0, evals_0, hvals_1, hgid
    let (vk_0, evals_0, hvals_1) = compute_universe_public_points(
            universe, all_regkeys);
    let hgid = utils::hash_to_g2(gid);
    
    // setup ck and vk
    let ck = NIDTSCombineKey { 
        evals_0: evals_0.clone(), hvals_1: hvals_1
    };
    let vk = NIDTSVerificationKey { 
        vk_0: vk_0.clone(), hgid: hgid
    };
    
    (ck, vk)
}

// compute partial signature of a party
pub fn nidts_sign_partial(id: PartyId, secret: &Scalar, party_weight: usize, msg: &[u8]) -> 
    NIDTSPartialSignature {
    let h_m = utils::hash_to_g2(msg);

    let mut party_sigs: Vec<G2Projective> = Vec::new();
    for i in 0..party_weight {
        let sk_i = secret + Scalar::from(i as u64);
        let sig_i = h_m.mul(sk_i);
        party_sigs.push(sig_i);
    }

    NIDTSPartialSignature { party_id: id, party_sigs: party_sigs }
}

// sign all partials
pub fn nidts_sign_all_partials(universe: &NIDTSUniverse, party_secrets: HashMap<PartyId, Scalar>, 
    online_parties: usize, msg: &[u8]) -> Vec<NIDTSPartialSignature> {
    let mut partial_sigs = Vec::new();
    
    for party in 0..online_parties {
        let party_weight = universe.get_weight(&party);
        partial_sigs.push(
            nidts_sign_partial(party, party_secrets.get(&party).unwrap(),
                    party_weight, msg)
        );
    }
    partial_sigs
}

// verify partial sig of a party
pub fn nidts_verify_partial(party_pubkey: &Vec<G1Projective>, part_sig: &NIDTSPartialSignature, 
    h_m: &G2Projective) -> bool {
    let mut rng = thread_rng();
    let g1 = utils::get_generator_in_g1();
    let party_weight = party_pubkey.len();

    let mut rnds = Vec::new();
    if party_weight == 1 {
        let rnd_0 = Scalar::from(1);
        rnds.push(rnd_0);
    } else {
        for _i in 0..party_weight {
            let rnd_i = Scalar::random(&mut rng);   // 256 or 128 bit
            rnds.push(rnd_i);
        }
    }
    
    let rnd_pubkey = utils::multi_exp_g1_fast(party_pubkey.as_slice(), rnds.as_slice());
    let rnd_sig = utils::multi_exp_g2_fast(part_sig.party_sigs.as_slice(), rnds.as_slice());
    
    let check_lhs = pairing(&g1.to_affine(), &rnd_sig.to_affine());
    let check_rhs = pairing(&rnd_pubkey.to_affine(), &h_m.to_affine());
    
    check_lhs == check_rhs
}

// batch verify all partial sigs
pub fn nidts_batch_verify_all_partial_sigs(all_sigs: &mut BTreeMap<XCoord, G2Projective>,
    universe: &NIDTSUniverse, partial_sigs: &[NIDTSPartialSignature], msg: &[u8]) -> bool {
    let t = universe.get_threshold();
    let par_xs_ranges = universe.compute_private_xs_ranges();
    let h_m = utils::hash_to_g2(msg);

    // prepare all_pubkeys and all_parsigs
    let mut all_pubkeys: Vec<G1Projective> = Vec::new();
    let mut all_parsigs: Vec<G2Projective> = Vec::new();
    
    for partial_sig in partial_sigs.iter() {
        let signer_id = &partial_sig.party_id;
        let party_weight = universe.get_weight(signer_id);
        let party_pubkey = universe.get_pubkeys(signer_id);

        for (i, pk_i) in party_pubkey.iter().enumerate() {
            if i < party_weight {
                all_pubkeys.push(pk_i.clone());
            }
        }

        for (i, sig_i) in partial_sig.party_sigs.iter().enumerate() {
            if i < party_weight {
                all_parsigs.push(sig_i.clone());
            }
        }
        
        if all_parsigs.len() >= t {
            break;
        }
    }
    if all_parsigs.len() < t { 
        println!("partial sigs are not sufficient.");
        return false; 
    }

    // batch verify
    {
        let mut rng = thread_rng();
        let g1 = utils::get_generator_in_g1();

        // check sig in G2
        for sig_i in all_parsigs.iter() {
            utils::is_subgroup_in_g2(&sig_i);
        }

        let mut rnds = Vec::new();
        for _i in 0..all_parsigs.len() {
            let rnd_i = Scalar::random(&mut rng);   // 256 or 128 bit
            rnds.push(rnd_i);
        }
        
        let rnd_pubkey = utils::multi_exp_g1_fast(all_pubkeys.as_slice(), rnds.as_slice());
        let rnd_parsig = utils::multi_exp_g2_fast(all_parsigs.as_slice(), rnds.as_slice());
        
        let check_lhs = pairing(&g1.to_affine(), &rnd_parsig.to_affine());
        let check_rhs = pairing(&rnd_pubkey.to_affine(), &h_m.to_affine());
        
        if check_lhs != check_rhs {
            return false
        }
    }

    // build all_sigs
    for partial_sig in partial_sigs.iter() {
        let signer_id = &partial_sig.party_id;
    
        // add partial sig
        let (lo, _) = par_xs_ranges.get(signer_id).unwrap();
        let party_weight = universe.get_weight(signer_id);
        for (i, sig_i) in partial_sig.party_sigs.iter().enumerate() {
            if i < party_weight {
                all_sigs.insert((lo + i).clone(), sig_i.clone());
            }
        }
    
        if all_sigs.len() >= t {
            break;
        }
    }
        
    true
}

// verify all partial sigs
pub fn nidts_verify_all_partial_sigs(all_sigs: &mut BTreeMap<XCoord, G2Projective>, 
    universe: &NIDTSUniverse, partial_sigs: &[NIDTSPartialSignature], msg: &[u8]) -> bool {
    let t = universe.get_threshold();
    let par_xs_ranges = universe.compute_private_xs_ranges();
    let h_m = utils::hash_to_g2(msg);

    for partial_sig in partial_sigs.iter() {
        let signer_id = &partial_sig.party_id;

        // verify partial sig
        let party_pubkeys = universe.get_pubkeys(signer_id);
        let valid = nidts_verify_partial(&party_pubkeys, partial_sig, &h_m);
        if valid != true { 
            println!("partial sig is not valid.");
            return false;
        }
        
        // add partial sig
        let (lo, _) = par_xs_ranges.get(signer_id).unwrap();
        let party_weight = universe.get_weight(signer_id);
        for (i, sig_i) in partial_sig.party_sigs.iter().enumerate() {
            if i < party_weight {
                all_sigs.insert((lo + i).clone(), sig_i.clone());
            }
        }

        if all_sigs.len() >= t {
            break;
        }
    }
    
    if all_sigs.len() < t { 
        println!("partial sigs are not sufficient.");
        return false; 
    }
    true
}

// combine partial signatures
pub fn nidts_combine(universe: &NIDTSUniverse, ck: &NIDTSCombineKey, 
    partial_sigs: &[NIDTSPartialSignature], msg: &[u8]) -> Option<NIDTSFullSignature> {
    let t = universe.get_threshold();

    // verify all partial sigs
    let mut all_sigs: BTreeMap<XCoord, G2Projective> = BTreeMap::new();
    let now = Instant::now();
    let valid = nidts_verify_all_partial_sigs(&mut all_sigs, universe, partial_sigs, msg);
    //let valid = nidts_batch_verify_all_partial_sigs(&mut all_sigs, universe, partial_sigs, msg);
    if valid != true { return None; }
    let dur = now.elapsed();
    println!("- verify parsigs time: \t {}.{:03}", dur.as_secs(), dur.subsec_millis());

    // compute full signature
    // get x points
    let mut all_xs: Vec<Scalar> = all_sigs.keys().into_iter().take(t).into_iter().
            map(|x| Scalar::from(*x as u64)).collect();
    let mut pub_xs: Vec<Scalar> = universe.compute_public_xs().iter().
            map(|x| Scalar::from(*x as u64)).collect();
    all_xs.append(&mut pub_xs);

    let lcs: Vec<Scalar> = Polynomial::lagrange_coefficients(all_xs.as_slice());

    let signer_ys: Vec<G2Projective> = all_sigs.values().into_iter().take(t).into_iter().
            map(|y| y.clone()).collect();

    let sigma_0 = utils::multi_exp_g2_fast(signer_ys.as_slice(), &lcs.as_slice()[0..t]);
    let sigma_1 = utils::multi_exp_g1_fast(ck.evals_0.as_slice(), &lcs.as_slice()[t..]);
    let sigma_2 = utils::multi_exp_g2_fast(ck.hvals_1.as_slice(), &lcs.as_slice()[t..]);

    // construct full signature
    Some(NIDTSFullSignature { 
        sigma_0: sigma_0, sigma_1: sigma_1, sigma_2: sigma_2 
    })
}

// verify threshold signature
pub fn nidts_verify(msg: &[u8], vk: &NIDTSVerificationKey, sig: &NIDTSFullSignature) -> 
    bool {
    let g1 = utils::get_generator_in_g1();
    let h_m = utils::hash_to_g2(msg);

    // e(H(m), vk_0 / sigma_1) = e(sigma_0, g2)
    let check1_lhs = pairing(&vk.vk_0.add(&sig.sigma_1.neg()).to_affine(), &h_m.to_affine());
    let check1_rhs = pairing(&g1.to_affine(), &sig.sigma_0.to_affine());
    
    // e(hgid, sigma_1) = e(sigma_2, g2)
    let check2_lhs = pairing(&sig.sigma_1.to_affine(), &vk.hgid.to_affine());
    let check2_rhs = pairing(&g1.to_affine(), &sig.sigma_2.to_affine());
    
    check1_lhs == check1_rhs && check2_lhs == check2_rhs
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use std::time::{Instant};
    use std::rc::Rc;
    use rand::{Rng,thread_rng};
    
    fn nidts_assign_party_weights_equal(num_parties: usize, equal_weight: usize) -> Vec<usize> {
        let mut party_weights = Vec::new();
        for _i in 0..num_parties {
            party_weights.push(equal_weight);
        }
        party_weights
    }

    fn _nidts_assign_party_weights_random(num_parties: usize, max_weight: usize) -> Vec<usize> {
        let mut rng = thread_rng();
        let mut party_weights = Vec::new();
        for _i in 0..num_parties {
            let party_weight = rng.gen_range(1..max_weight+1);
            party_weights.push(party_weight);
        }
        party_weights
    }

    // generate all pubkeys
    fn nidts_generate_all_pubkeys_to_universe(num_parties: usize, party_weight: usize, 
        threshold: usize) -> (NIDTSUniverse, HashMap<PartyId, Scalar>) {
        let mut rng = thread_rng();

        let all_weights = nidts_assign_party_weights_equal(num_parties, party_weight);
        //let party_weights = nidts_assign_party_weights_random(num_parties, party_weight);

        let mut universe = NIDTSUniverse::new();
        let mut all_secrets: HashMap<PartyId, Scalar> = HashMap::new();

        for party in 0..num_parties {
            let party_secret = Scalar::random(&mut rng);
            let party_pubkey = nidts_generate_party_pubkey(&party_secret, all_weights[party]);

            universe.add_party(party, all_weights[party], Rc::new(party_pubkey));
            all_secrets.insert(party, party_secret.clone());
            //total_weight += all_weights[party];
        }
        universe.set_threshold(threshold);

        (universe, all_secrets)
    }

    // generate all regkeys
    fn nidts_generate_all_regkeys(universe: &NIDTSUniverse, gid: &[u8], 
        all_secrets: &HashMap<PartyId, Scalar>, num_parties: usize) -> Vec<NIDTSRegisterKey> {
        let mut all_regkeys = Vec::new();

        for party in 0..num_parties {
            let secret = all_secrets.get(&party).unwrap();
            let party_pubkey = universe.get_pubkeys(&party);
            let party_weight = universe.get_weight(&party);
            
            let party_regkey = nidts_generate_party_regkey(
                        &secret, &party_pubkey, party_weight, gid);
            all_regkeys.push(party_regkey);
        }
    
        all_regkeys
    }

    // test core
    fn test_nidts_sig_core(num_parties: usize, party_weight: usize, threshold: usize) {
        assert!(1 <= threshold && threshold <= num_parties * party_weight);
        println!("nidts: {} parties, {} weight, {} threshold", num_parties, party_weight, threshold);

        let gid = "NIDTS Group Identifier";

        // generate party pubkeys and add to universe
        let now = Instant::now();
        let (universe, all_secrets) = nidts_generate_all_pubkeys_to_universe(
                num_parties, party_weight, threshold);
        let dur = now.elapsed();
        println!("all pubkeys time:    \t {}.{:03}", dur.as_secs(), dur.subsec_millis());

        // generate party regkeys
        let now = Instant::now();
        let all_regkeys = nidts_generate_all_regkeys(&universe, &gid.as_bytes(), 
                &all_secrets, num_parties);
        let dur = now.elapsed();
        println!("all regkeys time:    \t {}.{:03}", dur.as_secs(), dur.subsec_millis());
        
        // universe setup offline
        println!("universe setup start:");
        let now = Instant::now();
        let (ck, vk) = nidts_universe_setup(&universe, &gid.as_bytes(), 
                &all_regkeys);
        let dur = now.elapsed();
        println!("universe setup time: \t {}.{:03}", dur.as_secs(), dur.subsec_millis());

        let msg = "Hello Multiverse";

        // partial signing for all parties
        let online_parties = num_parties;
        let now = Instant::now();
        let partial_sigs = nidts_sign_all_partials(&universe, all_secrets, 
                online_parties, &msg.as_bytes());
        let dur = now.elapsed();
        println!("partial signing time: \t {}.{:03}", dur.as_secs(), dur.subsec_millis());

        // combining partial signatures
        println!("combining sigs start:");
        let now = Instant::now();
        let threshold_sig = nidts_combine(&universe, &ck, partial_sigs.as_slice(), 
                msg.as_bytes()).unwrap();
        let dur = now.elapsed();
        println!("combining sigs time: \t {}.{:03}", dur.as_secs(), dur.subsec_millis());
        
        // verification
        let now = Instant::now();
        assert_eq!(nidts_verify(msg.as_bytes(), &vk, &threshold_sig), true);
        let dur = now.elapsed();
        println!("verification time:   \t {}.{:03}", dur.as_secs(), dur.subsec_millis());
    }

    #[test]
    fn test_nidts_correctness() {
        let nvals = [(100, 1), (200, 1), (300, 1), (400, 1), (500, 1)];
        //let nvals = [(1000, 1), (1500, 1), (2000, 1)];
        //let nvals = [(100, 5), (200, 5), (300, 5), (100, 10), (200, 10), (300, 10)];
        //let nvals = [(100, 1), (100, 2), (100, 3)];
        for (n, w) in nvals {
            let num_parties = n;
            let party_weight = w;
            let threshold = (num_parties * party_weight) / 2;
            
            test_nidts_sig_core(num_parties, party_weight, threshold);
            println!("");
        }
    }

    #[test]
    fn test_pairing_benchmark() {
        let mut rng = thread_rng();
        let g1 = utils::get_generator_in_g1();
        let g2 = utils::get_generator_in_g2();
        let msg = "Hello Pairing";

        println!("bls12_381 benchmark");

        // mul in Zp
        let x = Scalar::random(&mut rng);
        let y = Scalar::random(&mut rng);
        let now = Instant::now();
        for _i in 0..1000000 {
            let _z = x * y;
        }
        let dur = now.elapsed() / 1000000;
        println!("mul_zp time:      \t {}.{:09}", dur.as_secs(), dur.subsec_nanos());

        // map to hash
        let now = Instant::now();
        for _i in 0..100 {
            utils::hash_to_g1(&msg.as_bytes());
        }
        let dur = now.elapsed() / 100;
        println!("hash_g1 time:      \t {}.{:06}", dur.as_secs(), dur.subsec_micros());

        let now = Instant::now();
        for _i in 0..100 {
            utils::hash_to_g2(&msg.as_bytes());
        }
        let dur = now.elapsed() / 100;
        println!("hash_g2 time:      \t {}.{:06}", dur.as_secs(), dur.subsec_micros());

        // subgroup
        let xval = Scalar::random(&mut rng);
        let y1 = g1.mul(&xval);
        let now = Instant::now();
        for _i in 0..100 {
            utils::is_subgroup_in_g1(&y1);
        }
        let dur = now.elapsed() / 100;
        println!("grp_test_g1 time:  \t {}.{:06}", dur.as_secs(), dur.subsec_micros());

        let xval = Scalar::random(&mut rng);
        let y2 = g2.mul(&xval);
        let now = Instant::now();
        for _i in 0..100 {
            utils::is_subgroup_in_g2(&y2);
        }
        let dur = now.elapsed() / 100;
        println!("grp_test_g2 time:  \t {}.{:06}", dur.as_secs(), dur.subsec_micros());

        // exp
        let xval = Scalar::random(&mut rng);
        let now = Instant::now();
        for _i in 0..100 {
            let _pk = g1.mul(&xval);
        }
        let dur = now.elapsed() / 100;
        println!("exp_g1 time:       \t {}.{:06}", dur.as_secs(), dur.subsec_micros());

        let now = Instant::now();
        for _i in 0..100 {
            let _pk = g2.mul(&xval);
        }
        let dur = now.elapsed() / 100;
        println!("exp_g2 time:       \t {}.{:06}", dur.as_secs(), dur.subsec_micros());

        // mulexp
        let num_exp = 100;

        let xval = Scalar::random(&mut rng);
        let mut xvals: Vec<Scalar> = Vec::new();
        for _i in 0..num_exp {
            xvals.push(xval.clone());
        }

        let mut yvals1: Vec<G1Projective> = Vec::new();
        let mut yvals2: Vec<G2Projective> = Vec::new();
        for _i in 0..num_exp {
            yvals1.push(g1.clone());
            yvals2.push(g2.clone());
        }

        let now = Instant::now();
        for _i in 0..100 {
            utils::multi_exp_g1_fast(yvals1.as_slice(), &xvals.as_slice());
        }
        let dur = now.elapsed() / 100;
        println!("mulexp_g1_{} time:\t {}.{:06}", num_exp, dur.as_secs(), dur.subsec_micros());

        let now = Instant::now();
        for _i in 0..100 {
            utils::multi_exp_g2_fast(yvals2.as_slice(), &xvals.as_slice());
        }
        let dur = now.elapsed() / 100;
        println!("mulexp_g2_{} time:\t {}.{:06}", num_exp, dur.as_secs(), dur.subsec_micros());

        // pairing
        let now = Instant::now();
        for _i in 0..100 {
            pairing(&g1.to_affine(), &g2.to_affine());
        }
        let dur = now.elapsed() / 100;
        println!("pairing time:      \t {}.{:06}", dur.as_secs(), dur.subsec_micros());

    }
}
