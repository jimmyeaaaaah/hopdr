use crate::formula{Pred, Op}
use crate::util::P;

use std::fmt;

type Ident = String;

#[derive(Clone, Debug)]
pub enum Expr {
    Var(Ident),
    Num(i64),
    True,
    False,
    Op(Op, P<Expr>, P<Expr>),
    Pred(Pred, P<Expr>, P<Expr>),
    App(P<Expr>, P<Expr>),
    And(P<Expr>, P<Expr>),
    Or(P<Expr>, P<Expr>),
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
        }
    }
}

#[derive(Clone, Debug)]
pub struct NuFormula {
    pub id: Ident,
    pub args: Vec<Ident>,
    pub expr: Expr,
}

impl fmt::Display for NuFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.id)?;
        for arg in self.args.iter() {
            write!(f, " {}", arg)?;
        }
        write!(f, " = {}", self.expr)
    }
}

#[derive(Clone, Debug)]
pub struct Formula {
    pub formulas: Vec<NuFormula>,
}
