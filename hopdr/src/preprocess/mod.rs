mod alpha;
mod eta;
mod extravar;
pub mod hes;
pub mod hfl_preprocessor;
mod safety;
mod transform;
mod typing;
mod forall_pass;

use crate::formula;
use crate::formula::Type as SimpleType;
use crate::parse;
use hes::ValidityChecking;
use rpds::HashTrieMap;

type IdentMap = HashTrieMap<parse::Ident, formula::Ident>;
pub struct Context {
    pub ident_map: IdentMap,
    pub original: ValidityChecking<parse::Ident, SimpleType>,
}

impl Context {
    fn new(ident_map: IdentMap, original: ValidityChecking<parse::Ident, SimpleType>) -> Context {
        Context {
            ident_map,
            original,
        }
    }
}
