pub mod sig_utils {
    use ff::*;
    use std::collections::{BTreeMap};
    use rand::{Rng, rngs::ThreadRng};
    use bls12_381::{Scalar};

    use crate::*;
    use crate::kzg::*;
    use crate::polynomial::*;

    pub fn sample_random_poly(
        rng: &mut ThreadRng,
        degree: usize) -> Polynomial {
        //rust ranges are bounded inclusively below and exclusively above
        let xs: Vec<Scalar> = (0..(degree+1)).map(|x| Scalar::from(x as u64)).collect();
        let ys: Vec<Scalar> = xs
            .iter()
            .enumerate()
            .map(|(_,_)| Scalar::random(&mut *rng))
            .collect();

        Polynomial::lagrange_interpolation(&xs[..], &ys[..])
    }

    // construct KZG CRS
    pub fn test_setup<const MAX_COEFFS: usize>(rng: &mut ThreadRng) -> 
        KZGParams {
        let s: Scalar = rng.gen::<u64>().into();
        setup(s, MAX_COEFFS)
    }

    // address book
    pub fn create_addr_book(num_parties: usize, k: usize) -> 
        BTreeMap<PartyId, Weight> {
        let mut ab : BTreeMap<PartyId, Weight> = BTreeMap::new();
        for party in 1..(num_parties+1) {
            ab.insert(party, k);
        }
        ab
    }

    pub fn get_parties_in_canonical_ordering(addr_book: &BTreeMap<PartyId, Weight>) -> 
        Vec<PartyId> {
        let mut parties = Vec::new();
        for (&party, _) in addr_book.iter() {
            parties.push(party);
        }
        parties
    }

    pub fn addr_book_to_private_xs_ranges(addr_book: &BTreeMap<PartyId, Weight>) ->
        BTreeMap<PartyId, (XCoord, XCoord)> {
        let mut mapping = BTreeMap::new();
        let mut consumed_weight: usize = 0;

        for party in get_parties_in_canonical_ordering(addr_book).iter() {
            let w = addr_book.get(party).unwrap();
            let party_weight = *w;
    
            let lo = consumed_weight + 1;
            let hi = consumed_weight + party_weight;
            mapping.insert(*party, (lo, hi));

            consumed_weight += party_weight;
        }
        mapping
    }
}
