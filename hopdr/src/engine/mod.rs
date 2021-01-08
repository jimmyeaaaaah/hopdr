mod rtype;
mod infer;

use crate::formula::{Constraint, Variable};
use crate::util::P;

#[derive(Clone, Debug)]
pub struct Atom {

}

#[derive(Clone, Debug)]
pub enum Goal {
    Atom(Atom),
    Constr(Constraint),
    Conj(P<Goal>, P<Goal>),
    Disj(P<Goal>, P<Goal>),
    Univ(Variable, P<Goal>)
}

#[derive(Clone, Debug)]
pub struct Clause {
    body: Goal,
    head: Variable,
    args: Vec<Variable>,
}

#[derive(Clone, Debug)]
pub struct Problem {
    clauses: Vec<Clause>,
    top: Goal,
}

//fn infer_nu_validity(vc: )