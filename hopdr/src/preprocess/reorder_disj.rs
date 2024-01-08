use super::TypedPreprocessor;
use crate::formula::hes::{self, GoalKind};
use crate::formula::{self, Bot, Logic};

pub struct ReorderDisjTransform {}

type Goal = hes::Goal<formula::Constraint>;

fn list_disj<'a>(g: &Goal, res: &mut Vec<Goal>) {
    match g.kind() {
        hes::GoalKind::Disj(g1, g2) => {
            list_disj(g1, res);
            list_disj(g2, res);
        }
        _ => res.push(g.clone()),
    }
}

impl TypedPreprocessor for ReorderDisjTransform {
    fn transform_goal(
        &self,
        goal: &Goal,
        t: &formula::Type,
        env: &mut formula::TyEnv,
    ) -> formula::hes::Goal<formula::Constraint> {
        match goal.kind() {
            hes::GoalKind::Constr(_) | hes::GoalKind::Op(_) | hes::GoalKind::Var(_) => goal.clone(),
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
                hes::Goal::mk_conj(g1, g2)
            }
            hes::GoalKind::Disj(_, _) => {
                let mut disjs = Vec::new();
                list_disj(goal, &mut disjs);
                disjs
                    .into_iter()
                    .rev()
                    .fold(Goal::mk_false(), |acc, g| Goal::mk_disj_opt(g, acc))
            }
            hes::GoalKind::Univ(x, g) => {
                let g = self.transform_goal(g, t, env);
                hes::Goal::mk_univ(x.clone(), g)
            }
            GoalKind::ITE(c, g1, g2) => {
                let c = c.clone();
                let g1 = self.transform_goal(g1, t, env);
                let g2 = self.transform_goal(g2, t, env);
                hes::Goal::mk_ite(c, g1, g2)
            }
        }
    }
}

pub fn transform(problem: hes::Problem<formula::Constraint>) -> hes::Problem<formula::Constraint> {
    let t = ReorderDisjTransform {};
    t.transform(problem)
}

#[test]
fn test_reorder_conj() {
    use crate::formula::*;
    // (x > 0 \/ P x \/ P (x + 1))
    let x = Ident::fresh();
    let p = Ident::fresh();

    let c = Constraint::mk_gt(Op::mk_var(x), Op::zero());
    let g1 = Goal::mk_constr(c);
    let p_x = Goal::mk_app(Goal::mk_var(p.clone()), Goal::mk_var(x.clone()));
    let px2 = Goal::mk_app(
        Goal::mk_var(p.clone()),
        Goal::mk_op(Op::mk_add(Op::mk_var(x), Op::one())),
    );

    let c = Goal::mk_disj(g1, p_x);
    let c = Goal::mk_disj(c, px2);

    let t = ReorderDisjTransform {};
    println!("c: {c}");
    let c2 = t.transform_goal(&c, &Type::mk_type_int(), &mut TyEnv::new());
    assert_ne!(c, c2);
    println!("c2: {c2}");
    let (g1, _) = c2.disj();
    assert!(matches!(g1.kind(), GoalKind::Constr(_)));
}
