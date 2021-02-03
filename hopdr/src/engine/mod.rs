mod rtype;
mod infer;
mod pdr;



use crate::formula::{Constraint, Variable, Ident};
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

impl Const {
    pub fn mk_int(v: i64) -> Const {
        Const::new(ConstKind::Int(v))
    }
    pub fn mk_bool(v: bool) -> Const {
        Const::new(ConstKind::Bool(v))
    }
}

#[derive(Debug)]
pub enum AtomKind {
    Var(Ident),
    Const(Const),
    App(Atom, Atom),
    //Abs(Variable, Atom)
}

pub type Atom = P<AtomKind>;


impl Atom {
    pub fn mk_var(ident: Ident) -> Atom {
        Atom::new(AtomKind::Var(ident))
    }
    pub fn mk_const(ct: Const) -> Atom {
        Atom::new(AtomKind::Const(ct))
    }
    pub fn mk_app(lhs: Atom, rhs: Atom) -> Atom {
        Atom::new(AtomKind::App(lhs, rhs))
    }
}

#[derive(Debug)]
pub enum GoalKind {
    Atom(Atom),
    Constr(Constraint),
    Conj(Goal, Goal),
    Disj(Goal, Goal),
    Univ(Variable, Goal)
}

pub type Goal = P<GoalKind>;

impl Goal {
    pub fn mk_atom(x: Atom) -> Goal {
        Goal::new(GoalKind::Atom(x))
    }
    pub fn mk_constr(x: Constraint) -> Goal {
        Goal::new(GoalKind::Constr(x))
    }
    pub fn mk_conj(lhs: Goal, rhs: Goal) -> Goal {
        Goal::new(GoalKind::Conj(lhs, rhs))
    }
    pub fn mk_disj(lhs: Goal, rhs: Goal) -> Goal {
        Goal::new(GoalKind::Disj(lhs, rhs))
    }
    pub fn mk_univ(x: Variable, g: Goal) -> Goal {
        Goal::new(GoalKind::Univ(x, g))
    }
}

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


impl Clause {
    pub fn new(body: Goal, head: Variable, args: Vec<Variable>) -> Clause {
        Clause { body, head, args }
    }
}

//fn infer_nu_validity(vc: )