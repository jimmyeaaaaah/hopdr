mod rtype;
mod infer;
mod pdr;

use std::rc::Rc;

use crate::formula::{Constraint, Variable};
use crate::util::P;

pub enum VerificationResult {
    Valid,
    Invalid,
    Unknown,
}

#[derive(Clone, Debug)]
pub struct Atom {

}

#[derive(Debug)]
pub enum GoalExpr {
    Atom(Atom),
    Constr(Constraint),
    Conj(Goal, Goal),
    Disj(Goal, Goal),
    Univ(Variable, Goal)
}

pub type Goal = P<GoalExpr>;

#[derive(Debug)]
pub struct Clause {
    body: Goal,
    head: Variable,
    args: Vec<Variable>,
}

#[derive(Debug)]
pub struct Problem {
    clauses: Vec<Clause>,
    top: Goal,
}

impl Clause {}

//fn infer_nu_validity(vc: )