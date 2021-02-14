use std::unimplemented;

use super::hes::{Clause, Expr, ExprKind, ValidityChecking, VariableS};
use crate::formula;
use crate::formula::{OpKind, PredKind, Type as SimpleType};
use crate::parse;

type In = ValidityChecking<VariableS<parse::Ident, SimpleType>>;
type Out = ValidityChecking<VariableS<formula::Ident, SimpleType>>;
pub fn alpha_renaming(input: In) -> Out {
    unimplemented!()
}
