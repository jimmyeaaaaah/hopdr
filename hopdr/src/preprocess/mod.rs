mod alpha;
mod eta;
mod extravar;
mod forall_pass;
pub mod hes;
pub mod hfl_preprocessor;
mod ite_expand;
mod safety;
mod transform;
mod typing;

use crate::formula;
use crate::formula::Type as SimpleType;
use crate::parse;
use hes::ValidityChecking;
use rpds::HashTrieMap;
use std::collections::HashMap;

type IdentMap = HashTrieMap<parse::Ident, formula::Ident>;
pub struct Context {
    pub ident_map: IdentMap,
    pub inverse_map: HashMap<formula::Ident, parse::Ident>,
    pub original: Option<ValidityChecking<parse::Ident, SimpleType>>,
}

impl Context {
    fn new(ident_map: IdentMap, original: ValidityChecking<parse::Ident, SimpleType>) -> Context {
        let inverse_map = ident_map
            .iter()
            .map(|(x, y)| (y.clone(), x.clone()))
            .collect();
        Context {
            ident_map,
            inverse_map,
            original: Some(original),
        }
    }
    pub fn empty() -> Context {
        Context {
            ident_map: HashTrieMap::new(),
            inverse_map: HashMap::new(),
            original: None,
        }
    }
}
