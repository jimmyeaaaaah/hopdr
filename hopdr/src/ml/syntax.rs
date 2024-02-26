use core::panic;

use super::{Type as SType, Variable};
use crate::formula::{Constraint, Fv, Ident, Op, Precedence, PrecedenceKind, Subst};
use crate::util::P;

/// Represents a half-open interval [lb, ub).
///
/// lb or ub can be None, which means there is no ends.
/// For example, `Range{lb: None, ub: 5}` represents [-∞, 5).
#[derive(Debug, Clone, PartialEq)]
pub struct Range {
    pub lb: Option<i64>,
    pub ub: Option<i64>,
}

impl Range {
    pub fn new() -> Self {
        Range { lb: None, ub: None }
    }
    pub fn lb(self, lb: i64) -> Self {
        Self {
            lb: Some(lb),
            ..self
        }
    }
    pub fn ub(self, ub: i64) -> Self {
        Self {
            ub: Some(ub),
            ..self
        }
    }
    pub fn boolean() -> Self {
        Self {
            lb: Some(0),
            ub: Some(2),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    Var(Ident),
    Constraint(Constraint),
    Or(Expr, Expr),
    And(Expr, Expr),
    App(Expr, Expr),
    IApp(Expr, Op),
    Fun {
        ident: Variable,
        body: Expr,
    },
    If {
        cond: Expr,
        then: Expr,
        els: Expr,
    },
    LetRand {
        ident: Ident,
        range: Range,
        body: Expr,
    },
    Raise,
    Unit,
    TryWith {
        body: Expr,
        handler: Expr,
    },
    Assert(Expr),
    Sequential {
        lhs: Expr,
        rhs: Expr,
    },
    Tuple(Vec<Expr>),
    LetTuple {
        idents: Vec<Ident>,
        body: Expr,
        cont: Expr,
    },
    Op(Op),
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
            ExprKind::Tuple(_) => PrecedenceKind::Atom,
            ExprKind::LetTuple { .. } => PrecedenceKind::Abs,
            ExprKind::Op(o) => o.precedence(),
        }
    }
}

impl Fv for Expr {
    type Id = Ident;
    fn fv_with_vec(&self, fvs: &mut std::collections::HashSet<Self::Id>) {
        match self.kind() {
            ExprKind::Var(x) => {
                fvs.insert(x.clone());
            }
            ExprKind::Constraint(c) => {
                c.fv_with_vec(fvs);
            }
            ExprKind::Or(x, y) => {
                x.fv_with_vec(fvs);
                y.fv_with_vec(fvs);
            }
            ExprKind::And(x, y) => {
                x.fv_with_vec(fvs);
                y.fv_with_vec(fvs);
            }
            ExprKind::App(x, y) => {
                x.fv_with_vec(fvs);
                y.fv_with_vec(fvs);
            }
            ExprKind::IApp(x, o) => {
                x.fv_with_vec(fvs);
                o.fv_with_vec(fvs);
            }
            ExprKind::Fun { ident: x, body } => {
                let check = fvs.contains(&x.ident);
                body.fv_with_vec(fvs);
                if !check {
                    fvs.remove(&x.ident);
                }
            }
            ExprKind::If { cond, then, els } => {
                cond.fv_with_vec(fvs);
                then.fv_with_vec(fvs);
                els.fv_with_vec(fvs);
            }
            ExprKind::LetRand {
                ident: x,
                body,
                range: _,
            } => {
                let check = fvs.contains(&x);
                body.fv_with_vec(fvs);
                if !check {
                    fvs.remove(&x);
                }
            }
            ExprKind::Raise => {}
            ExprKind::Unit => {}
            ExprKind::TryWith { body, handler } => {
                body.fv_with_vec(fvs);
                handler.fv_with_vec(fvs);
            }
            ExprKind::Assert(cond) => {
                cond.fv_with_vec(fvs);
            }
            ExprKind::Sequential { lhs, rhs } => {
                lhs.fv_with_vec(fvs);
                rhs.fv_with_vec(fvs);
            }
            ExprKind::Tuple(args) => {
                for arg in args {
                    arg.fv_with_vec(fvs);
                }
            }
            ExprKind::LetTuple {
                idents: xs,
                body,
                cont,
            } => {
                let checks = xs.iter().map(|x| fvs.contains(x)).collect::<Vec<_>>();
                cont.fv_with_vec(fvs);
                for (check, x) in checks.iter().zip(xs.iter()) {
                    if !check {
                        fvs.remove(x);
                    }
                }
                body.fv_with_vec(fvs);
            }
            ExprKind::Op(o) => {
                o.fv_with_vec(fvs);
            }
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
    pub fn mk_letrand(ident: Ident, range: Range, body: Expr) -> Self {
        P::new(ExprKind::LetRand { ident, range, body })
    }
    pub fn mk_let_bool_rand(ident: Ident, body: Expr) -> Self {
        P::new(ExprKind::LetRand {
            ident,
            range: Range::boolean(),
            body,
        })
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
    pub fn mk_tuple(args: Vec<Expr>) -> Self {
        if args.len() == 0 {
            Self::mk_unit()
        } else {
            P::new(ExprKind::Tuple(args))
        }
    }
    pub fn mk_let_tuple(idents: Vec<Ident>, body: Expr, cont: Expr) -> Self {
        P::new(ExprKind::LetTuple { idents, body, cont })
    }
    pub fn mk_let(ident: Ident, body: Expr, cont: Expr) -> Self {
        P::new(ExprKind::LetTuple {
            idents: vec![ident],
            body,
            cont,
        })
    }
    pub fn mk_op(o: Op) -> Self {
        P::new(ExprKind::Op(o))
    }
    pub fn subst(&self, ident: Ident, e: Expr) -> Self {
        match self.kind() {
            ExprKind::Var(x) if *x == ident => e,
            ExprKind::Var(_) | ExprKind::Op(_) | ExprKind::Constraint(_) => self.clone(),
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
                cond.subst(ident, e.clone()),
                then.subst(ident, e.clone()),
                els.subst(ident, e),
            ),
            ExprKind::LetRand {
                ident: x,
                range,
                body,
            } => {
                if *x == ident {
                    Expr::mk_letrand(x.clone(), range.clone(), body.clone())
                } else {
                    Expr::mk_letrand(x.clone(), range.clone(), body.subst(ident, e))
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
            ExprKind::Tuple(args) => {
                Expr::mk_tuple(args.iter().map(|e2| e2.subst(ident, e.clone())).collect())
            }
            ExprKind::LetTuple { idents, body, cont } => {
                let body = body.subst(ident, e.clone());
                let cont = if idents.contains(&ident) {
                    cont.clone()
                } else {
                    cont.subst(ident, e)
                };
                Expr::mk_let_tuple(idents.clone(), body, cont)
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
            ExprKind::LetRand {
                ident: x,
                range,
                body,
            } => {
                if *x == ident {
                    Expr::mk_letrand(x.clone(), range.clone(), body.clone())
                } else {
                    Expr::mk_letrand(x.clone(), range.clone(), body.isubst(ident, e))
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
            ExprKind::Tuple(args) => {
                Expr::mk_tuple(args.iter().map(|e2| e2.isubst(ident, e.clone())).collect())
            }
            ExprKind::LetTuple { idents, body, cont } => {
                let body = body.isubst(ident, e.clone());
                let cont = if idents.contains(&ident) {
                    cont.clone()
                } else {
                    cont.isubst(ident, e)
                };
                Expr::mk_let_tuple(idents.clone(), body, cont)
            }
            ExprKind::Op(o) => Expr::mk_op(o.subst(&ident, &e)),
        }
    }
    /// checks if self is the expression of the form `if cond then raise True else ()`
    /// where cond is a constraint
    pub fn is_check_constraint(&self) -> Option<Constraint> {
        match self.kind() {
            ExprKind::If { cond, then, els }
                if matches!(then.kind(), ExprKind::Raise)
                    && matches!(els.kind(), ExprKind::Unit) =>
            {
                match cond.kind() {
                    ExprKind::Constraint(c) => Some(c.clone()),
                    _ => None,
                }
            }
            _ => None,
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
