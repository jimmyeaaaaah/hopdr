use std::{collections::HashMap, error::Error, fmt, mem::uninitialized, unimplemented};





use super::alpha::alpha_renaming;
use super::transform::transform;
use super::typing::typing;
use crate::formula::hes;
use crate::formula::{OpKind, PredKind, Type as SimpleType};
use crate::parse;
use crate::util::{global_counter, Unique, P};

type Ident = String;

#[derive(Debug)]
pub enum ExprKind<Id> {
    Var(Id),
    Num(i64),
    True,
    False,
    Op(OpKind, Expr<Id>, Expr<Id>),
    Pred(PredKind, Expr<Id>, Expr<Id>),
    App(Expr<Id>, Expr<Id>),
    And(Expr<Id>, Expr<Id>),
    Or(Expr<Id>, Expr<Id>),
    Univ(Ident, Expr<Id>),
}
pub type Expr<Id> = Unique<ExprKind<Id>>;

impl <Id: fmt::Display> fmt::Display for Expr<Id> {
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

impl <Id>Expr<Id> {
    pub fn mk_var(x: Id) -> Expr<Id> {
        Expr::new(ExprKind::Var(x))
    }
    pub fn mk_num(x: i64) -> Expr<Id> {
        Expr::new(ExprKind::Num(x))
    }
    pub fn mk_true() -> Expr<Id> {
        Expr::new(ExprKind::True)
    }
    pub fn mk_false() -> Expr<Id> {
        Expr::new(ExprKind::False)
    }
    pub fn mk_op(op: OpKind, e1: Expr<Id>, e2: Expr<Id>) -> Expr<Id> {
        Expr::new(ExprKind::Op(op, e1, e2))
    }
    pub fn mk_pred(pred: PredKind, e1: Expr<Id>, e2: Expr<Id>) -> Expr<Id> {
        Expr::new(ExprKind::Pred(pred, e1, e2))
    }
    pub fn mk_app(e1: Expr<Id>, e2: Expr<Id>) -> Expr<Id> {
        Expr::new(ExprKind::App(e1, e2))
    }
    pub fn mk_and(e1: Expr<Id>, e2: Expr<Id>) -> Expr<Id> {
        Expr::new(ExprKind::And(e1, e2))
    }
    pub fn mk_or(e1: Expr<Id>, e2: Expr<Id>) -> Expr<Id> {
        Expr::new(ExprKind::Or(e1, e2))
    }
    pub fn mk_univ(id: Ident, e: Expr<Id>) -> Expr<Id> {
        Expr::new(ExprKind::Univ(id, e))
    }
}

#[derive(Clone, Debug)]
pub struct VariableS<Id, Ty> {
    pub id: Id,
    pub ty: Ty,
}
impl<Id: fmt::Display, Ty: fmt::Display> fmt::Display for VariableS<Id, Ty> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.id, self.ty)
    }
}

type Variable = VariableS<Ident, SimpleType>;

#[derive(Debug)]
pub struct Clause<Id, Ty> {
    pub id: VariableS<Id, Ty>,
    pub args: Vec<Ident>,
    pub expr: Expr<Id>,
}

#[derive(Debug)]
pub struct ValidityChecking<Id, Ty> {
    pub clauses: Vec<Clause<Id, Ty>>,
    pub toplevel: Expr<Id>,
}

impl<Id: fmt::Display, Ty: fmt::Display> fmt::Display for Clause<Id, Ty> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.id)?;
        for arg in self.args.iter() {
            write!(f, " {}", arg)?;
        }
        write!(f, " = {}", self.expr)
    }
}

impl <Id>Expr<Id> {
    pub fn from(e: parse::Expr) -> Expr<parse::Ident> {
        match e.into() {
            parse::ExprKind::Var(v) => Expr::mk_var(v),
            parse::ExprKind::Num(x) => Expr::mk_num(x),
            parse::ExprKind::True => Expr::mk_true(),
            parse::ExprKind::False => Expr::mk_false(),
            parse::ExprKind::Op(op, e1, e2) => Expr::mk_op(op, Expr::<parse::Ident>::from(e1), Expr::<parse::Ident>::from(e2)),
            parse::ExprKind::Pred(p, e1, e2) => Expr::mk_pred(p, Expr::<parse::Ident>::from(e1), Expr::<parse::Ident>::from(e2)),
            parse::ExprKind::App(e1, e2) => Expr::mk_app(Expr::<parse::Ident>::from(e1), Expr::<parse::Ident>::from(e2)),
            parse::ExprKind::And(e1, e2) => Expr::mk_and(Expr::<parse::Ident>::from(e1), Expr::<parse::Ident>::from(e2)),
            parse::ExprKind::Or(e1, e2) => Expr::mk_or(Expr::<parse::Ident>::from(e1), Expr::<parse::Ident>::from(e2)),
            parse::ExprKind::Univ(x, e) => Expr::mk_univ(x, Expr::<parse::Ident>::from(e)),
            _ => panic!("not implemented"),
        }
    }
}

pub fn preprocess(vc: parse::Problem) -> hes::Problem {
    match vc {
        parse::Problem::NuHFLZValidityChecking(vc) => {
            let problem = typing(vc.formulas, vc.toplevel);
            let problem = alpha_renaming(problem);
            transform(problem)
        }
    }
}
