use super::mode::*;
use super::ProblemM;

use crate::formula::hes::{ClauseBase, GoalBase, GoalKind, ProblemBase};
use crate::formula::{Constraint, Fv, Ident, Logic, Negation, Op, PredKind, Type as HFLType};
use crate::util::P;

type Input = ProblemBase<Constraint, ()>;
type Output = ProblemBase<Constraint, super::Aux>;

#[derive(Clone, Debug)]
struct Aux {
    mode: Mode,
}

// data structure used for inferring mode
type Goal = GoalBase<Constraint, Aux>;
type Clause = ClauseBase<Constraint, Aux>;
type Problem = ProblemBase<Constraint, Aux>;

pub(super) fn infer(problem: Input) -> Output {
    unimplemented!()
}
