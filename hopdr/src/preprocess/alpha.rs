use std::unimplemented;

use super::hes::{ValidityChecking, VariableS};
use crate::formula;
use crate::formula::{Type as SimpleType};
use crate::parse;

type In = ValidityChecking<VariableS<parse::Ident, SimpleType>>;
type Out = ValidityChecking<VariableS<formula::Ident, SimpleType>>;
pub fn alpha_renaming(_input: In) -> Out {
    unimplemented!()
}
