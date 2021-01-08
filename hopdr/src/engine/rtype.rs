use crate::formula::{Constraint};
use crate::util::P;

#[derive(Clone, Copy, Debug)]
pub struct Variable {
    id: u64,
}

pub enum Sigma {
    Integer(Variable),
    Tau(Tau),
}

pub enum Tau {
    Proposition(Constraint),
    Intersection(P<Tau>, P<Tau>),
    Arrow(P<Sigma>, P<Tau>)
}
