use core::panic;

use super::{Type as SType, Variable};
use crate::formula::{Constraint, Ident, Op, Precedence, PrecedenceKind, PredKind, Subst};
use crate::util::P;

#[derive(Debug, Clone)]
pub enum ExprKind {
    Var(Ident),
    Constraint(Constraint),
    Or(Expr, Expr),
    And(Expr, Expr),
    App(Expr, Expr),
    IApp(Expr, Op),
    Fun { ident: Variable, body: Expr },
    If { cond: Expr, then: Expr, els: Expr },
    LetRand { ident: Ident, body: Expr },
    Raise,
    Unit,
    TryWith { body: Expr, handler: Expr },
    Assert(Expr),
    Sequential { lhs: Expr, rhs: Expr },
}
pub type Expr = P<ExprKind>;

impl Precedence for Expr {
    fn precedence(&self) -> PrecedenceKind {
        match self.kind() {
            ExprKind::Var(_) => PrecedenceKind::Atom,
            ExprKind::Constraint(c) => c.precedence(),
            ExprKind::Or(_, _) => PrecedenceKind::Disj,
            ExprKind::And(_, _) => PrecedenceKind::Conj,
            ExprKind::App(_, _) | ExprKind::IApp(_, _) => PrecedenceKind::App,
            ExprKind::Fun { .. } => PrecedenceKind::Abs,
            ExprKind::If { .. } => PrecedenceKind::If,
            ExprKind::LetRand { .. } => PrecedenceKind::Abs,
            ExprKind::Raise => PrecedenceKind::App,
            ExprKind::Unit => PrecedenceKind::Atom,
            ExprKind::TryWith { .. } => PrecedenceKind::If,
            ExprKind::Assert(_) => PrecedenceKind::App,
            ExprKind::Sequential { .. } => PrecedenceKind::Sequential,
        }
    }
}

impl Expr {
    pub fn mk_app(lhs: Expr, rhs: Expr) -> Self {
        P::new(ExprKind::App(lhs, rhs))
    }
    pub fn mk_iapp(lhs: Expr, rhs: Op) -> Self {
        P::new(ExprKind::IApp(lhs, rhs))
    }
    pub fn mk_fun(ident: Variable, body: Expr) -> Self {
        P::new(ExprKind::Fun { ident, body })
    }
    pub fn mk_var(ident: Ident) -> Self {
        P::new(ExprKind::Var(ident))
    }
    pub fn mk_or(lhs: Expr, rhs: Expr) -> Self {
        P::new(ExprKind::Or(lhs, rhs))
    }
    pub fn mk_and(lhs: Expr, rhs: Expr) -> Self {
        P::new(ExprKind::And(lhs, rhs))
    }
    pub fn mk_constraint(cond: Constraint) -> Self {
        P::new(ExprKind::Constraint(cond))
    }
    pub fn mk_if(cond: Expr, then: Expr, els: Expr) -> Self {
        P::new(ExprKind::If { cond, then, els })
    }
    pub fn mk_letrand(ident: Ident, body: Expr) -> Self {
        P::new(ExprKind::LetRand { ident, body })
    }
    pub fn mk_assert(cond: Expr) -> Self {
        P::new(ExprKind::Assert(cond))
    }
    pub fn mk_raise() -> Self {
        P::new(ExprKind::Raise)
    }
    pub fn mk_unit() -> Self {
        P::new(ExprKind::Unit)
    }
    pub fn mk_try_with(body: Expr, handler: Expr) -> Self {
        P::new(ExprKind::TryWith { body, handler })
    }
    pub fn mk_sequential(lhs: Expr, rhs: Expr) -> Self {
        P::new(ExprKind::Sequential { lhs, rhs })
    }
    pub fn subst(&self, ident: Ident, e: Expr) -> Self {
        match self.kind() {
            ExprKind::Var(x) if *x == ident => e,
            ExprKind::Var(_) => self.clone(),
            ExprKind::Constraint(_) => self.clone(),
            ExprKind::Or(lhs, rhs) => Expr::mk_or(lhs.subst(ident, e.clone()), rhs.subst(ident, e)),
            ExprKind::And(lhs, rhs) => {
                Expr::mk_and(lhs.subst(ident, e.clone()), rhs.subst(ident, e))
            }
            ExprKind::App(lhs, rhs) => {
                Expr::mk_app(lhs.subst(ident, e.clone()), rhs.subst(ident, e))
            }
            ExprKind::IApp(lhs, o) => Expr::mk_iapp(lhs.subst(ident, e.clone()), o.clone()),
            ExprKind::Fun { ident: x, body } => {
                if x.ident == ident {
                    Expr::mk_fun(x.clone(), body.clone())
                } else {
                    Expr::mk_fun(x.clone(), body.subst(ident, e))
                }
            }
            ExprKind::If { cond, then, els } => Expr::mk_if(
                cond.clone(),
                then.subst(ident, e.clone()),
                els.subst(ident, e),
            ),
            ExprKind::LetRand { ident: x, body } => {
                if *x == ident {
                    Expr::mk_letrand(x.clone(), body.clone())
                } else {
                    Expr::mk_letrand(x.clone(), body.subst(ident, e))
                }
            }
            ExprKind::Raise => self.clone(),
            ExprKind::Unit => self.clone(),
            ExprKind::TryWith { body, handler } => {
                Expr::mk_try_with(body.subst(ident, e.clone()), handler.subst(ident, e))
            }
            ExprKind::Assert(cond) => Expr::mk_assert(cond.subst(ident, e)),
            ExprKind::Sequential { lhs, rhs } => {
                Expr::mk_sequential(lhs.subst(ident, e.clone()), rhs.subst(ident, e))
            }
        }
    }
    pub fn isubst(&self, ident: Ident, e: Op) -> Self {
        match self.kind() {
            ExprKind::Var(x) if *x == ident => panic!("program error"),
            ExprKind::Var(_) => self.clone(),
            ExprKind::Constraint(c) => Expr::mk_constraint(c.subst(&ident, &e)),
            ExprKind::Or(lhs, rhs) => {
                Expr::mk_or(lhs.isubst(ident, e.clone()), rhs.isubst(ident, e))
            }
            ExprKind::And(lhs, rhs) => {
                Expr::mk_and(lhs.isubst(ident, e.clone()), rhs.isubst(ident, e))
            }
            ExprKind::App(lhs, rhs) => {
                Expr::mk_app(lhs.isubst(ident, e.clone()), rhs.isubst(ident, e))
            }
            ExprKind::IApp(lhs, o) => {
                Expr::mk_iapp(lhs.isubst(ident, e.clone()), o.subst(&ident, &e))
            }
            ExprKind::Fun { ident: x, body } => {
                if x.ident == ident {
                    Expr::mk_fun(x.clone(), body.clone())
                } else {
                    Expr::mk_fun(x.clone(), body.isubst(ident, e))
                }
            }
            ExprKind::If { cond, then, els } => Expr::mk_if(
                cond.isubst(ident, e.clone()),
                then.isubst(ident, e.clone()),
                els.isubst(ident, e),
            ),
            ExprKind::LetRand { ident: x, body } => {
                if *x == ident {
                    Expr::mk_letrand(x.clone(), body.clone())
                } else {
                    Expr::mk_letrand(x.clone(), body.isubst(ident, e))
                }
            }
            ExprKind::Raise => self.clone(),
            ExprKind::Unit => self.clone(),
            ExprKind::TryWith { body, handler } => {
                Expr::mk_try_with(body.isubst(ident, e.clone()), handler.isubst(ident, e))
            }
            ExprKind::Assert(cond) => Expr::mk_assert(cond.isubst(ident, e)),
            ExprKind::Sequential { lhs, rhs } => {
                Expr::mk_sequential(lhs.isubst(ident, e.clone()), rhs.isubst(ident, e))
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Function {
    pub name: Ident,
    pub ty: SType,
    pub body: Expr,
}

#[derive(Clone)]
pub struct Program<'a> {
    pub functions: Vec<Function>,
    pub main: Expr,
    pub ctx: &'a crate::preprocess::Context,
}
