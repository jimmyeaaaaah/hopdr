use crate::formula::{PredKind, OpKind};
use crate::util::P;

use std::fmt;

type Ident = String;


#[derive(Clone, Debug)]
pub enum Fixpoint {
    Greatest,
    Least,
}


impl fmt::Display for Fixpoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", match self {
            Fixpoint::Greatest => "ν",
            Fixpoint::Least => "μ",
        })
    }
}
#[derive(Clone, Debug)]
pub enum Expr {
    Var(Ident),
    Num(i64),
    True,
    False,
    Op(OpKind, P<Expr>, P<Expr>),
    Pred(PredKind, P<Expr>, P<Expr>),
    App(P<Expr>, P<Expr>),
    And(P<Expr>, P<Expr>),
    Or(P<Expr>, P<Expr>),
    Fix(Fixpoint, Ident, P<Expr>),
    Abs(Ident, P<Expr>),
    Univ(Ident, P<Expr>),
    Exist(Ident, P<Expr>),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Var(id) => write!(f, "{}", id),
            Expr::Op(op, e1, e2) => write!(f, "({} {} {})", e1, op, e2),
            Expr::Pred(pred, e1, e2) => write!(f, "({} {} {})", e1, pred, e2),
            Expr::App(e1, e2) => write!(f, "({} {})", e1, e2),
            Expr::And(e1, e2) => write!(f, "({} & {})", e1, e2),
            Expr::Or(e1, e2) => write!(f, "({} | {})", e1, e2),
            Expr::Num(x) => write!(f, "{}", x),
            Expr::True => write!(f, "true"),
            Expr::False => write!(f, "false"),
            Expr::Fix (op, id, e)=> write!(f, "{}{}. {}", op, id, e),
            Expr::Abs(id, e) => write!(f, "λ{}. {}", id, e),
            Expr::Univ(id, e) => write!(f, "∀{}. {}", id, e),
            Expr::Exist(id, e) => write!(f, "∃{}. {}", id, e)
        }
    }
}

#[derive(Clone, Debug)]
pub struct Clause {
    pub id: Ident,
    pub args: Vec<Ident>,
    pub expr: Expr,
    pub fixpoint: Fixpoint,
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.id)?;
        for arg in self.args.iter() {
            write!(f, " {}", arg)?;
        }
        write!(f, " = {}", self.expr)
    }
}

#[derive(Clone, Debug)]
pub struct NuHFLzValidityChecking {
    pub formulas: Vec<Clause>,
    pub toplevel: Expr,
}


#[derive(Debug)]
pub enum Problem {
    NuHFLZValidityChecking(NuHFLzValidityChecking)
}
