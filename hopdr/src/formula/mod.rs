pub mod ty;
pub mod pcsp;

use std::fmt;
use std::{collections::HashMap, rc::Rc, unimplemented};
pub use crate::formula::ty::*;
pub use crate::util::P;
use crate::util::{global_counter};


#[derive(Clone, Copy, Debug)]
pub enum PredKind {
    Eq,
    Neq,
    Leq,
    Gt
}

impl fmt::Display for PredKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                PredKind::Leq => "<=",
                PredKind::Gt => ">",
                PredKind::Eq => "=",
                PredKind::Neq => "!=",
            }
        )
    }
}
#[derive(Clone, Copy, Debug)]
pub enum OpKind {
    Add,
    Sub,
    Mul,
    Div,
    Mod
}

impl fmt::Display for OpKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                OpKind::Add => "+",
                OpKind::Sub => "-",
                OpKind::Mul => "*",
                OpKind::Div => "/",
                OpKind::Mod => "%",
            }
        )
    }
}

#[derive(Debug)]
pub enum OpExpr {
    Op(OpKind, Op, Op),
    Var(Ident),
    Const(i64),
}

pub type Op = P<OpExpr>;

impl Op {
    fn mk_bin_op(op: OpKind, x: Op, y: Op) -> Op {
        Op::new(OpExpr::Op(op, x, y))
    }

    fn subst(&self, id: &Ident, v: &Op) -> Op {
        match &**self {
            OpExpr::Op(k, x, y) => 
                Op::mk_bin_op(*k, x.subst(id, v), y.subst(id, v)),
            
            OpExpr::Var(id2) if id == id2 => v.clone(),
            _ => self.clone(),
        }
    }
}

#[derive(Debug)]
pub enum ConstraintExpr {
    True,
    False,
    Pred(PredKind, Vec<Op>),
    Conj(Constraint, Constraint),
    Disj(Constraint, Constraint),
    Univ(Variable, Constraint),
}

pub type Constraint = P<ConstraintExpr>;

impl Constraint {
    pub fn mk_true() -> Constraint {
        Constraint::new(ConstraintExpr::True)
    }

    pub fn mk_false() -> Constraint {
        Constraint::new(ConstraintExpr::False)
    }

    pub fn mk_univ(v: Variable, c: Constraint) -> Constraint {
        Constraint::new(ConstraintExpr::Univ(v, c))
    }

    pub fn mk_conj(x: Constraint, y: Constraint) -> Constraint {
        Constraint::new(ConstraintExpr::Conj(x, y))
    }
    pub fn mk_disj(x: Constraint, y: Constraint) -> Constraint {
        Constraint::new(ConstraintExpr::Disj(x, y))
    }

    pub fn mk_pred(k: PredKind, v: Vec<Op>) -> Constraint {
        Constraint::new(ConstraintExpr::Pred(k, v))
    }

    // \theta[v/x]
    pub fn subst(&self, x: &Ident, v: &Op) -> Constraint {
        use ConstraintExpr::*;
        match &**self {
            True | False => self.clone(),
            Pred(k, ops) => {
                let mut new_ops = Vec::new();
                for op in ops.iter() {
                    new_ops.push(op.subst(x, v));
                }
                Constraint::mk_pred(*k, new_ops)
            },
            Conj(r, l) => Constraint::mk_conj(r.subst(x, v), l.subst(x, v)),
            Disj(r, l) => Constraint::mk_disj(r.subst(x, v), l.subst(x, v)),
            Univ(var, cstr) => 
                Constraint::mk_univ(var.clone(), cstr.subst(x, v)),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Ident {
    id: u64,
}

impl Ident {
    pub fn fresh() -> Ident {
        let id = global_counter();
        Ident { id }
    }
}

#[derive(Debug)]
pub struct VariableS {
    pub id: Ident,
    pub ty: Type,
}
pub type Variable = P<VariableS>;

#[derive(Clone, Debug)]
pub enum Fixpoint {
    Greatest,
    Least,
}
