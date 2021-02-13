use std::{collections::HashMap, error::Error, fmt, mem::uninitialized, unimplemented};

use fmt::Formatter;
use lazy_static::lazy;
use rpds::HashTrieMap;

use super::typing::typing;
use crate::formula::{OpKind, PredKind, Type as SimpleType};
use crate::parse;
use crate::util::{global_counter, Unique, P};
use crate::formula::hes;

type Ident = String;

#[derive(Debug)]
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
    Univ(Ident, Expr),
}
pub type Expr = Unique<ExprKind>;

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
            ExprKind::Univ(id, e) => write!(f, "∀{}. {}", id, e),
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
    pub fn mk_univ(id: Ident, e: Expr) -> Expr {
        Expr::new(ExprKind::Univ(id, e))
    }
}

#[derive(Clone, Debug)]
pub struct VariableS<Ty> {
    pub id: Ident,
    pub ty: Ty,
}
impl<Ty: fmt::Display> fmt::Display for VariableS<Ty> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.id, self.ty)
    }
}

type Variable = VariableS<SimpleType>;

#[derive(Debug)]
pub struct Clause<Var> {
    pub id: Var,
    pub args: Vec<Ident>,
    pub expr: Expr,
}

impl<Var: fmt::Display> fmt::Display for Clause<Var> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.id)?;
        for arg in self.args.iter() {
            write!(f, " {}", arg)?;
        }
        write!(f, " = {}", self.expr)
    }
}

#[derive(Debug)]
pub struct ValidityChecking<Var> {
    pub formulas: Vec<Clause<Var>>,
    pub toplevel: Expr,
}

impl Expr {
    pub fn from(e: parse::Expr) -> Expr {
        match e.into() {
            parse::ExprKind::Var(v) => Expr::mk_var(v),
            parse::ExprKind::Num(x) => Expr::mk_num(x),
            parse::ExprKind::True => Expr::mk_true(),
            parse::ExprKind::False => Expr::mk_false(),
            parse::ExprKind::Op(op, e1, e2) => Expr::mk_op(op, Expr::from(e1), Expr::from(e2)),
            parse::ExprKind::Pred(p, e1, e2) => Expr::mk_pred(p, Expr::from(e1), Expr::from(e2)),
            parse::ExprKind::App(e1, e2) => Expr::mk_app(Expr::from(e1), Expr::from(e2)),
            parse::ExprKind::And(e1, e2) => Expr::mk_and(Expr::from(e1), Expr::from(e2)),
            parse::ExprKind::Or(e1, e2) => Expr::mk_or(Expr::from(e1), Expr::from(e2)),
            parse::ExprKind::Univ(x, e) => Expr::mk_univ(x, Expr::from(e)),
            _ => panic!("not implemented"),
        }
    }
}


pub fn transform(vc: parse::Problem) -> hes::Problem {
    match vc {
        parse::Problem::NuHFLZValidityChecking(mut vc) => {
            let (formulas, toplevel) = typing(vc.formulas, vc.toplevel);
            unimplemented!()
        }
    }
}
