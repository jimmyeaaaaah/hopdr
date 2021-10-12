use super::rtype::Tau;
use crate::formula::{
    Conjunctive, Constraint, Fv, Ident, IntegerEnvironment, Op, QuantifierKind, Rename, Subst, Top,
};

#[derive(Debug)]
pub struct Negative {}
pub type Sty = Tau<Negative, Constraint>;
