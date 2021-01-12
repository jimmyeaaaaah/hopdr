use std::{unimplemented};
use super::{Problem, Clause, Goal, VerificationResult};
use crate::formula::pcsp::PCSP;

// APLAS20

pub enum InferError {
    Msg(&'static str),
}

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