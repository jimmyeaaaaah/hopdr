use std::{unimplemented};
use super::{Problem, Clause, Goal, VerificationResult};
use crate::formula::pcsp::PCSP;
use crate::formula::{Constraint, Ident, P, Op};

// APLAS20

pub enum InferError {
    Msg(&'static str),
}

#[derive(Debug)]
pub enum TauKind {
    Proposition(Constraint),
    Intersection(Tau, Tau),
    IArrow(Ident, Tau),
    Arrow(Tau, Tau),
    Var(Ident, Vec<Ident>),
}
pub type Tau = P<TauKind>;

impl Goal {
    fn infer(&self, _constraints: &mut Vec<PCSP>) -> Result<(), InferError> {
        unimplemented!()
    }
}

impl Clause {
    fn infer(&self) -> Vec<PCSP> {
        let constraints = Vec::new();
        constraints
    }
}

fn infer(_problem: Problem) -> VerificationResult {
    unimplemented!();
}