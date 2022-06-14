// We would like to merge this file to derivation.rs;
// however, to avoid a bug in rust-analyzer, we separate this part.

use super::rtype::{Refinement, TBot, Tau, TauKind, TypeEnvironment};
use crate::formula::hes::{Goal, GoalBase, Problem as ProblemBase};
use crate::formula::{self, Arithmetic, FirstOrderLogic};
use crate::formula::{
    chc, fofml, pcsp, Bot, Constraint, ConstraintBase, Ident, Logic, Negation, Op, OpBase, Rename,
    Subst, Top, Type as Sty, Variable,
};
use crate::solver;
use crate::title;

use rpds::{HashTrieMap, Stack};

use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Clone, Debug)]
pub(crate) struct OpTrace {}

impl fmt::Display for OpTrace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unimplemented!()
    }
}

impl OpTrace {
    pub(crate) fn new() -> Self {
        unimplemented!()
    }
}
// Op with trace
pub(crate) type OpWT = OpBase<OpTrace>;

impl From<Op> for OpWT {
    fn from(c: Op) -> Self {
        let trace = OpTrace::new();
        match c.kind() {
            formula::OpExpr::Op(o, x, y) => {
                Self::mk_bin_op_t(*o, x.clone().into(), y.clone().into(), trace)
            }
            formula::OpExpr::Var(x) => Self::mk_var_t(*x, trace),
            formula::OpExpr::Const(c) => Self::mk_const_t(*c, trace),
        }
    }
}
impl From<OpWT> for Op {
    fn from(c: OpWT) -> Self {
        match c.kind() {
            formula::OpExpr::Op(o, x, y) => Self::mk_bin_op(*o, x.clone().into(), y.clone().into()),
            formula::OpExpr::Var(x) => Self::mk_var(*x),
            formula::OpExpr::Const(c) => Self::mk_const(*c),
        }
    }
}
impl<C, T> From<GoalBase<C, T, OpWT>> for OpWT {
    fn from(g: GoalBase<C, T, OpWT>) -> Self {
        use formula::hes::GoalKind;
        match g.kind() {
            GoalKind::Op(o) => o.clone(),
            GoalKind::Var(x) => Op::mk_var(*x).into(),
            GoalKind::Constr(_)
            | GoalKind::Abs(_, _)
            | GoalKind::App(_, _)
            | GoalKind::Conj(_, _)
            | GoalKind::Disj(_, _)
            | GoalKind::Univ(_, _) => panic!("program error"),
        }
    }
}
impl From<ConstraintBase<Op>> for ConstraintBase<OpWT> {
    fn from(c: ConstraintBase<Op>) -> Self {
        match c.kind() {
            formula::ConstraintExpr::True => Self::mk_true(),
            formula::ConstraintExpr::False => Self::mk_false(),
            formula::ConstraintExpr::Pred(p, l) => {
                let l = l.iter().map(|o| o.clone().into()).collect();
                Self::mk_pred(*p, l)
            }
            formula::ConstraintExpr::Conj(x, y) => {
                Self::mk_conj(x.clone().into(), y.clone().into())
            }
            formula::ConstraintExpr::Disj(x, y) => {
                Self::mk_disj(x.clone().into(), y.clone().into())
            }
            formula::ConstraintExpr::Quantifier(q, v, c) => {
                Self::mk_quantifier(*q, v.clone(), c.clone().into())
            }
        }
    }
}

impl From<ConstraintBase<OpWT>> for ConstraintBase<Op> {
    fn from(c: ConstraintBase<OpWT>) -> Self {
        match c.kind() {
            formula::ConstraintExpr::True => Self::mk_true(),
            formula::ConstraintExpr::False => Self::mk_false(),
            formula::ConstraintExpr::Pred(p, l) => {
                let l = l.iter().map(|o| o.clone().into()).collect();
                Self::mk_pred(*p, l)
            }
            formula::ConstraintExpr::Conj(x, y) => {
                Self::mk_conj(x.clone().into(), y.clone().into())
            }
            formula::ConstraintExpr::Disj(x, y) => {
                Self::mk_disj(x.clone().into(), y.clone().into())
            }
            formula::ConstraintExpr::Quantifier(q, v, c) => {
                Self::mk_quantifier(*q, v.clone(), c.clone().into())
            }
        }
    }
}
