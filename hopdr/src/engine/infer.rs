use std::{mem::uninitialized, unimplemented};
use super::{Problem, Clause, Goal, VerificationResult};
use crate::formula::pcsp::{PCSP, Atom};
use crate::formula::{Constraint, Ident, P};

// APLAS20

pub enum InferError {
    Msg(&'static str),
}

#[derive(Debug)]
pub enum TauKind {
    Proposition(Atom),
    IArrow(Ident, Tau),
    Arrow(Tau, Tau),
}
pub type Tau = P<TauKind>;

impl Tau {
    pub fn rty(&self) -> Atom {
        use TauKind::*;
        match &**self {
            TauKind::Proposition(x) => 
        }
    }
    // generate constraints by considering subtype s <= t
    fn subtype_inner(s: &Tau, t: &Tau, assumption: Atom, constraints: &mut Vec<PCSP>) {
        use TauKind::*;
        match (&**s, &**t) {
            (Proposition(x), Proposition(y)) => {
                constraints.push(PCSP::new(&Atom::mk_conj(&assumption, y), x));
            },
            (IArrow(i, t), IArrow(i2, t2)) => {
                Tau::subtype_inner(t, t2, assumption, constraints);
            },
            (Arrow(t1, s1), Arrow(t2, s2)) => {
                Tau::subtype_inner(s1, s2, assumption, constraints);
            },
            (Intersection(_, _), Intersection(_, _)) => {
                unimplemented!()
            },
            _ => panic!("program error: invalid subtyping")

        }
    }
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