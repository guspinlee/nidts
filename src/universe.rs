use std::collections::{BTreeMap};
use std::rc::Rc;
use std::fmt;
use crate::{UniverseId, PartyId, XCoord, Weight, AddressBook, PublicKey};

#[derive(Clone)]
pub struct NIDTSUniverse {
    /// contains mapping from party id to its weight and public keys
    pub addr_book: AddressBook,
    /// signing threshold for this universe
    pub signing_threshold: Weight,
}

/// prints the mapping from party id to its weight
impl fmt::Display for NIDTSUniverse {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut output = String::new();
        output.push_str(format!("universe: ").as_str());
        for (party, (weight, _)) in self.addr_book.iter() {
            output.push_str(format!("({},{}) ", party, weight).as_str());
        }
        output.push_str(format!("threshold: {}", self.signing_threshold).as_str());
        write!(f, "{}", output)
    }
}

impl NIDTSUniverse {
    /// creates a new, empty universe
    pub fn new() -> Self {
        NIDTSUniverse {
            addr_book: BTreeMap::new(),
            signing_threshold: 0
        }
    }

    //todo add error codes here
    pub fn add_party(&mut self, party_id: PartyId, weight: Weight, pubkeys: Rc<Vec<PublicKey>>) {
        if weight <= pubkeys.as_ref().len() {
            self.addr_book.insert(party_id, (weight, pubkeys.clone()) );
        } else {
            //todo: return some error code.
        }
    }

    pub fn set_threshold(&mut self, t: Weight) {
        self.signing_threshold = t;
    }

    pub fn get_threshold(&self) -> Weight {
        self.signing_threshold
    }

    pub fn get_total_weight(&self) -> Weight {
        let mut aggregate_weight: Weight = 0;
        for (&_, (weight, _)) in self.addr_book.iter() {
            aggregate_weight += weight;
        }
        aggregate_weight
    }

    pub fn get_weight(&self, party: &PartyId) -> Weight {
        // BTreeMap<PartyId, (Weight, Rc<Vec<PublicKey>>, ...)>;
        let (w, _) = self.addr_book.get(party).unwrap();
        *w
    }

    pub fn get_unique_universe_id(&self) -> UniverseId {
        return [0; 32];
    }

    pub fn get_parties_in_canonical_ordering(&self) -> Vec<PartyId> {
        let mut parties = Vec::new();
        for (&party, (_, _)) in self.addr_book.iter() {
            parties.push(party);
        }
        parties
    }

    pub fn compute_private_xs_ranges(&self) -> BTreeMap<PartyId, (XCoord, XCoord)> {
        let mut mapping = BTreeMap::new();
        let mut consumed_weight: usize = 0;

        for party in self.get_parties_in_canonical_ordering().iter() {
            let party_weight = self.get_weight(party);

            let lo = consumed_weight + 1;
            let hi = consumed_weight + party_weight;
            mapping.insert(*party, (lo, hi));

            consumed_weight += party_weight;
        }
        mapping
    }

    pub fn compute_public_xs(&self) -> Vec<XCoord> {
        let lo = self.get_total_weight() + 1;
        let hi = 2*self.get_total_weight() - self.get_threshold();
        let xs: Vec<XCoord> = (lo..hi+1).collect();
        xs
    }

    pub fn get_pubkeys(&self, party: &PartyId) -> Rc<Vec<PublicKey>> {
        // BTreeMap<PartyId, (Weight, Rc<Vec<PartyPublicKey>>), ...>;
        let (_, keys) = self.addr_book.get(party).unwrap();
        Rc::clone(keys)
    }

    pub fn get_all_pubkeys(&self) -> Vec<PublicKey> {
        let mut pubkeys = Vec::new();

        for party in self.get_parties_in_canonical_ordering().iter() {
            for party_key in self.get_pubkeys(party).iter() {
                pubkeys.push(party_key.clone());
            }
        }
        pubkeys
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nidts_universe() {
        let mut universe = NIDTSUniverse::new();
        universe.add_party(1, 10, Rc::new(Vec::new()) );
        universe.add_party(2, 10, Rc::new(Vec::new()) );
        universe.add_party(3, 5, Rc::new(Vec::new()) );
        universe.add_party(4, 3, Rc::new(Vec::new()) );
        universe.set_threshold(10);
        println!("{}", universe);

        for (party, (lo,hi)) in &universe.compute_private_xs_ranges() {
            println!("{party}: {lo}..{hi}");
        }
    }
}
