use super::TypedPreprocessor;
use crate::formula::hes::{self};
use crate::formula::{self};

pub struct SimplifyConstrOpTransform {}

type Goal = hes::Goal<formula::Constraint>;

impl TypedPreprocessor for SimplifyConstrOpTransform {
    fn transform_goal(
        &self,
        goal: &Goal,
        t: &formula::Type,
        env: &mut formula::TyEnv,
    ) -> formula::hes::Goal<formula::Constraint> {
        match goal.kind() {
            hes::GoalKind::Var(_) => goal.clone(),
            hes::GoalKind::Constr(c) => Goal::mk_constr(c.simplify()),
            hes::GoalKind::Op(o) => Goal::mk_op(o.simplify()),
            hes::GoalKind::Abs(x, g) => {
                let g = self.transform_goal(g, t, env);
                hes::Goal::mk_abs(x.clone(), g)
            }
            hes::GoalKind::App(g1, g2) => {
                let g1 = self.transform_goal(g1, t, env);
                let g2 = self.transform_goal(g2, t, env);
                hes::Goal::mk_app(g1, g2)
            }
            hes::GoalKind::Conj(g1, g2) => {
                let g1 = self.transform_goal(g1, t, env);
                let g2 = self.transform_goal(g2, t, env);
                hes::Goal::mk_conj_opt(g1, g2)
            }
            hes::GoalKind::Disj(g1, g2) => {
                let g1 = self.transform_goal(g1, t, env);
                let g2 = self.transform_goal(g2, t, env);
                hes::Goal::mk_disj_opt(g1, g2)
            }
            hes::GoalKind::Univ(x, g) => {
                let g = self.transform_goal(g, t, env);
                hes::Goal::mk_univ_opt(x.clone(), g)
            }
        }
    }
}

#[allow(dead_code)]
pub fn transform(problem: hes::Problem<formula::Constraint>) -> hes::Problem<formula::Constraint> {
    let t = SimplifyConstrOpTransform {};
    t.transform(problem)
}

#[test]
fn test_reorder_conj() {}
