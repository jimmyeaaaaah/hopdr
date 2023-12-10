/// This pass removes the integer introduced for temporary variables.
/// For example, a formula ∀x. x != 0 \/ P(x, y) can be translated to P(0, y).
use super::TypedPreprocessor;
use crate::formula::hes::{self, GoalKind};
use crate::formula::{self, Ident, Negation, Op, Top};

use std::collections::{HashMap, HashSet};

pub struct RemoveTmpVarTransform {}

type Goal = hes::Goal<formula::Constraint>;

// main function for the transformation
fn f(g: &Goal, map: &mut HashMap<Ident, Op>, tmpvars: &mut HashSet<Ident>) -> Goal {}

impl TypedPreprocessor for RemoveTmpVarTransform {
    fn transform_goal(
        &self,
        goal: &formula::hes::Goal<formula::Constraint>,
        t: &formula::Type,
        env: &mut formula::TyEnv,
    ) -> formula::hes::Goal<formula::Constraint> {
        f(goal, &mut HashMap::new(), &mut HashSet::new())
    }
}
