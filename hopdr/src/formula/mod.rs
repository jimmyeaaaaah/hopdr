pub mod ty;
pub mod pcsp;

use std::fmt;
pub use crate::formula::ty::*;
pub use crate::util::P;
use crate::util::{global_counter};

#[derive(Copy, Clone, Debug)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Mod
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Op::Add => "+",
                Op::Sub => "-",
                Op::Mul => "*",
                Op::Div => "/",
                Op::Mod => "%",
            }
        )
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Pred {
    Eq,
    Neq,
    Leq,
    Gt
}

impl fmt::Display for Pred {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Pred::Leq => "<=",
                Pred::Gt => ">",
                Pred::Eq => "=",
                Pred::Neq => "!=",
            }
        )
    }
}


#[derive(Clone, Debug)]
pub enum Constraint {
    True,
    False,
    Op(Op, P<Constraint>, P<Constraint>),
    Pred(Pred, P<Constraint>, P<Constraint>),
    Conj(P<Constraint>, P<Constraint>),
    Disj(P<Constraint>, P<Constraint>)
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

#[derive(Clone, Debug)]
pub struct Variable {
    pub id: Ident,
    pub ty: Type,
}

#[derive(Clone, Debug)]
pub enum Fixpoint {
    Greatest,
    Least,
}
