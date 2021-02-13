
guse std::unimplemented;

use super::hes::{Clause, Expr, ExprKind, VariableS, ValidityChecking};
use crate::formula::{OpKind, PredKind, Type as SimpleType};

type In = ValidityChecking<VariableS<SimpleType>>;
//type Out = ValidityChecking<
type Out = u64;
pub fn alpha_renaming(input: In) -> Out {
    unimplemented!()
}