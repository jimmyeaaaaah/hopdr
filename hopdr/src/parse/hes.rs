use crate::formula::{Fv, OpKind, PredKind};
use crate::util::Unique;

use std::fmt;

type Ident = String;

#[derive(Clone, Debug, PartialEq)]
pub enum Fixpoint {
    Greatest,
    Least,
}

impl fmt::Display for Fixpoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Fixpoint::Greatest => "ν",
                Fixpoint::Least => "μ",
            }
        )
    }
}

#[derive(Debug, PartialEq)]
pub enum ExprKind {
    Var(Ident),
    Num(i64),
    True,
    False,
    Op(OpKind, Expr, Expr),
    Pred(PredKind, Expr, Expr),
    App(Expr, Expr),
    And(Expr, Expr),
    Or(Expr, Expr),
    Fix(Fixpoint, Ident, Expr),
    Abs(Ident, Expr),
    Univ(Ident, Expr),
    Exist(Ident, Expr),
}

pub type Expr = Unique<ExprKind>;

impl Fv for Expr {
    type Id = Ident;

    fn fv_with_vec(&self, fvs: &mut std::collections::HashSet<Self::Id>) {
        match self.kind() {
            ExprKind::Var(x) => {
                fvs.insert(x.clone());
            }
            ExprKind::Pred(_, e1, e2)
            | ExprKind::Op(_, e1, e2)
            | ExprKind::App(e1, e2)
            | ExprKind::And(e1, e2)
            | ExprKind::Or(e1, e2) => {
                e1.fv_with_vec(fvs);
                e2.fv_with_vec(fvs);
            }
            ExprKind::Fix(_, x, _)
            | ExprKind::Abs(x, _)
            | ExprKind::Univ(x, _)
            | ExprKind::Exist(x, _) => {
                fvs.remove(x);
            }
            ExprKind::Num(_) | ExprKind::True | ExprKind::False => (),
        }
    }
}

impl Expr {
    pub fn mk_var(x: Ident) -> Expr {
        Expr::new(ExprKind::Var(x))
    }
    pub fn mk_num(x: i64) -> Expr {
        Expr::new(ExprKind::Num(x))
    }
    pub fn mk_true() -> Expr {
        Expr::new(ExprKind::True)
    }
    pub fn mk_false() -> Expr {
        Expr::new(ExprKind::False)
    }
    pub fn mk_op(op: OpKind, e1: Expr, e2: Expr) -> Expr {
        Expr::new(ExprKind::Op(op, e1, e2))
    }
    pub fn mk_pred(pred: PredKind, e1: Expr, e2: Expr) -> Expr {
        Expr::new(ExprKind::Pred(pred, e1, e2))
    }
    pub fn mk_app(e1: Expr, e2: Expr) -> Expr {
        Expr::new(ExprKind::App(e1, e2))
    }
    pub fn mk_and(e1: Expr, e2: Expr) -> Expr {
        Expr::new(ExprKind::And(e1, e2))
    }
    pub fn mk_or(e1: Expr, e2: Expr) -> Expr {
        Expr::new(ExprKind::Or(e1, e2))
    }
    pub fn mk_fix(f: Fixpoint, id: Ident, e: Expr) -> Expr {
        Expr::new(ExprKind::Fix(f, id, e))
    }
    pub fn mk_abs(id: Ident, e: Expr) -> Expr {
        Expr::new(ExprKind::Abs(id, e))
    }
    pub fn mk_univ(id: Ident, e: Expr) -> Expr {
        Expr::new(ExprKind::Univ(id, e))
    }
    pub fn mk_exist(id: Ident, e: Expr) -> Expr {
        Expr::new(ExprKind::Exist(id, e))
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            ExprKind::Var(id) => write!(f, "{}", id),
            ExprKind::Op(op, e1, e2) => write!(f, "({} {} {})", e1, op, e2),
            ExprKind::Pred(pred, e1, e2) => write!(f, "({} {} {})", e1, pred, e2),
            ExprKind::App(e1, e2) => write!(f, "({} {})", e1, e2),
            ExprKind::And(e1, e2) => write!(f, "({} & {})", e1, e2),
            ExprKind::Or(e1, e2) => write!(f, "({} | {})", e1, e2),
            ExprKind::Num(x) => write!(f, "{}", x),
            ExprKind::True => write!(f, "true"),
            ExprKind::False => write!(f, "false"),
            ExprKind::Fix(op, id, e) => write!(f, "{}{}. {}", op, id, e),
            ExprKind::Abs(id, e) => write!(f, "λ{}. {}", id, e),
            ExprKind::Univ(id, e) => write!(f, "∀{}. {}", id, e),
            ExprKind::Exist(id, e) => write!(f, "∃{}. {}", id, e),
        }
    }
}

// Clone should be removed
// reason: https://github.com/Geal/nom/issues/1132
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

#[derive(Debug)]
pub struct NuHFLzValidityChecking {
    pub formulas: Vec<Clause>,
    pub toplevel: Expr,
}

#[derive(Debug)]
pub enum Problem {
    NuHFLZValidityChecking(NuHFLzValidityChecking),
}

// technical reason in parse
// nom 5.0: https://github.com/Geal/nom/issues/1132
impl Clone for Expr {
    fn clone(&self) -> Expr {
        match self.kind() {
            ExprKind::Var(id) => Expr::mk_var(id.clone()),
            ExprKind::Op(op, e1, e2) => Expr::mk_op(*op, e1.clone(), e2.clone()),
            ExprKind::Pred(pred, e1, e2) => Expr::mk_pred(*pred, e1.clone(), e2.clone()),
            ExprKind::App(e1, e2) => Expr::mk_app(e1.clone(), e2.clone()),
            ExprKind::And(e1, e2) => Expr::mk_and(e1.clone(), e2.clone()),
            ExprKind::Or(e1, e2) => Expr::mk_or(e1.clone(), e2.clone()),
            ExprKind::Num(x) => Expr::mk_num(*x),
            ExprKind::True => Expr::mk_true(),
            ExprKind::False => Expr::mk_false(),
            ExprKind::Fix(op, id, e) => Expr::mk_fix(op.clone(), id.clone(), e.clone()),
            ExprKind::Abs(id, e) => Expr::mk_abs(id.clone(), e.clone()),
            ExprKind::Univ(id, e) => Expr::mk_univ(id.clone(), e.clone()),
            ExprKind::Exist(id, e) => Expr::mk_exist(id.clone(), e.clone()),
        }
    }
}
