pub mod ty;
pub mod pcsp;

use std::fmt;
use std::{collections::HashMap, rc::Rc, unimplemented};
pub use crate::formula::ty::*;
pub use crate::util::P;
use crate::util::{global_counter};


#[derive(Clone, Debug)]
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
#[derive(Clone, Debug)]
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
pub enum OpExpr{
    Op(OpKind, Op, Op),
}

pub type Op = P<OpExpr>;

impl Op {
    fn mk_bin_op(op: OpKind, x: Op, y: Op) -> Op {
        Op::new(OpExpr::Op(op, x, y))
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
