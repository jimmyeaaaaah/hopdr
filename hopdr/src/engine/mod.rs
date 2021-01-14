mod rtype;
mod infer;
mod pdr;

use std::rc::Rc;

use crate::formula::{Constraint, Variable, Ident, Op, IntegerEnvironment};
use crate::util::P;

pub enum VerificationResult {
    Valid,
    Invalid,
    Unknown,
}

#[derive(Debug)]
pub enum ConstKind {
    Int(i64),
    Bool(bool),
}

pub type Const = P<ConstKind>;

#[derive(Debug)]
pub enum AtomKind {
    Var(Ident),
    Const(Const),
    App(Atom, Atom),
    //Abs(Variable, Atom)
}

pub type Atom = P<AtomKind>;


impl Atom {
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