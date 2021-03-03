use crate::formula::{Constraint, Ident, Variable};
use crate::util::P;
use std::fmt;

#[derive(Debug)]
pub enum ConstKind {
    Int(i64),
}

pub type Const = P<ConstKind>;

impl fmt::Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ConstKind::*;
        match self.kind() {
            Int(i) => write!(f, "{}", i),
        }
    }
}

impl Const {
    pub fn mk_int(v: i64) -> Const {
        Const::new(ConstKind::Int(v))
    }
    pub fn is_int(&self) -> bool {
        use ConstKind::*;
        match self.kind() {
            Int(_) => true,
        }
    }
    pub fn int(&self) -> i64 {
        use ConstKind::*;
        match self.kind() {
            Int(x) => *x,
        }
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

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use AtomKind::*;
        match self.kind() {
            Var(i) => write!(f, "{}", i),
            Const(c) => write!(f, "{}", c),
            App(x, y) => write!(f, "{} {}", x, y),
        }
    }
}

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
    Univ(Variable, Goal),
}

pub type Goal = P<GoalKind>;

impl fmt::Display for Goal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use GoalKind::*;
        match self.kind() {
            Atom(a) => write!(f, "{}", a),
            Constr(c) => write!(f, "{}", c),
            Conj(x, y) => write!(f, "({} & {})", x, y),
            Disj(x, y) => write!(f, "({} | {})", x, y),
            Univ(x, y) => write!(f, "∀{}.{}", x, y),
        }
    }
}

impl Goal {
    pub fn is_true(&self) -> bool {
        match self.kind() {
            GoalKind::Constr(c) if c.is_true() => true,
            _ => false
        }
    }
    pub fn mk_atom(x: Atom) -> Goal {
        Goal::new(GoalKind::Atom(x))
    }
    pub fn mk_constr(x: Constraint) -> Goal {
        Goal::new(GoalKind::Constr(x))
    }
    pub fn mk_conj(lhs: Goal, rhs: Goal) -> Goal {
        if lhs.is_true() {
            rhs
        } else if rhs.is_true() {
            lhs
        } else {
            Goal::new(GoalKind::Conj(lhs, rhs))
        }
    }
    pub fn mk_disj(lhs: Goal, rhs: Goal) -> Goal {
        if lhs.is_true() {
            lhs
        } else if rhs.is_true() {
            rhs
        } else {
            Goal::new(GoalKind::Disj(lhs, rhs))
        }
    }
    pub fn mk_univ(x: Variable, g: Goal) -> Goal {
        Goal::new(GoalKind::Univ(x, g))
    }
}

#[derive(Debug)]
pub struct Clause {
    pub body: Goal,
    pub head: Variable,
    pub args: Vec<Ident>, // Vec<Ident> ??
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ", self.head)?;
        for arg in self.args.iter() {
            write!(f, "{} ", arg)?;
        }
        write!(f, "= {}", self.body)
    }
}

#[derive(Debug)]
pub struct Problem {
    pub clauses: Vec<Clause>,
    pub top: Goal,
}

impl Clause {
    pub fn new(body: Goal, head: Variable, args: Vec<Ident>) -> Clause {
        Clause { body, head, args }
    }
}
