use super::TypedPreprocessor;
use crate::formula::hes::{self, GoalKind};
use crate::formula::{self, Logic, Negation, Top};

pub struct ReorderConjTransform {}

type Goal = hes::Goal<formula::Constraint>;

fn conj_list<'a>(g: &Goal, res: &mut Vec<Goal>) {
    match g.kind() {
        hes::GoalKind::Conj(g1, g2) => {
            conj_list(g1, res);
            conj_list(g2, res);
        }
        _ => res.push(g.clone()),
    }
}

fn check_dual(g1: &Goal, g2: &Goal) -> bool {
    match (g1.kind(), g2.kind()) {
        (GoalKind::Disj(g11, g12), GoalKind::Disj(g21, g22)) => {
            let c1 = match (g11.kind(), g12.kind()) {
                (GoalKind::Constr(c), _) | (_, GoalKind::Constr(c)) => c,
                (_, _) => return false,
            };
            let c2 = match (g21.kind(), g22.kind()) {
                (GoalKind::Constr(c), _) | (_, GoalKind::Constr(c)) => c,
                (_, _) => return false,
            };
            return &c1.negate().unwrap() == c2;
        }
        (_, _) => false,
    }
}

impl TypedPreprocessor for ReorderConjTransform {
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
            hes::GoalKind::Conj(_, _) => {
                let mut conjs = Vec::new();
                conj_list(goal, &mut conjs);
                let mut res = hes::Goal::mk_true();
                while conjs.len() > 0 {
                    let g1 = conjs.pop().unwrap();
                    let i = match conjs.iter().enumerate().find_map(|(i, g2)| {
                        if check_dual(&g1, g2) {
                            Some((i, g2))
                        } else {
                            None
                        }
                    }) {
                        Some((i, g2)) => {
                            res = Goal::mk_conj_opt(res, Goal::mk_conj_opt(g1.clone(), g2.clone()));
                            i
                        }
                        None => {
                            res = Goal::mk_conj_opt(res, g1.clone());
                            continue;
                        }
                    };
                    conjs.remove(i);
                }
                res
            }
            hes::GoalKind::Disj(g1, g2) => {
                let g1 = self.transform_goal(g1, t, env);
                let g2 = self.transform_goal(g2, t, env);
                hes::Goal::mk_disj(g1, g2)
            }
            hes::GoalKind::Univ(x, g) => {
                let g = self.transform_goal(g, t, env);
                hes::Goal::mk_univ(x.clone(), g)
            }
        }
    }
}

pub fn transform(problem: hes::Problem<formula::Constraint>) -> hes::Problem<formula::Constraint> {
    let t = ReorderConjTransform {};
    t.transform(problem)
}

#[test]
fn test_reorder_conj() {
    use crate::formula::*;
    // (x = 1 /\ (x > 0 \/ P x)) /\ (x <= 0\/ P x)
    let x = Ident::fresh();
    let p = Ident::fresh();

    let c = Goal::mk_conj(
        Goal::mk_constr(Constraint::mk_eq(Op::mk_var(x.clone()), Op::one())),
        Goal::mk_disj(
            Goal::mk_constr(Constraint::mk_gt(Op::mk_var(x.clone()), Op::zero())),
            Goal::mk_app(Goal::mk_var(p), Goal::mk_op(Op::mk_var(x.clone()))),
        ),
    );
    let c2 = Goal::mk_disj(
        Goal::mk_constr(Constraint::mk_leq(Op::mk_var(x.clone()), Op::zero())),
        Goal::mk_app(Goal::mk_var(p), Goal::mk_op(Op::mk_var(x.clone()))),
    );
    let c = Goal::mk_conj(c, c2);

    let t = ReorderConjTransform {};
    println!("c: {c}");
    let c2 = t.transform_goal(&c, &Type::mk_type_int(), &mut TyEnv::new());
    println!("c2: {c2}");
    assert_ne!(c, c2);
}
