mod alpha;
pub mod hes;
mod transform;
mod typing;

use rpds::{HashTrieMap};
use crate::parse;
use crate::formula;
use hes::{ValidityChecking};
use crate::formula::{Fv, Type as SimpleType, Variable, Ident, Subst};

type IdentMap = HashTrieMap<parse::Ident, formula::Ident>;
pub struct Context {
    pub ident_map: IdentMap,
    pub original: ValidityChecking<parse::Ident, SimpleType>,
}

impl Context {
    fn new(ident_map: IdentMap, original: ValidityChecking<parse::Ident, SimpleType>) -> Context {
        Context{ ident_map, original }
    }
}