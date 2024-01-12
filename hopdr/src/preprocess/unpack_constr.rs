/// This function unfold constr's quantifier, disjunction and conjunction.
/// For example,
///   Goal::Constr(forall x. (x = 0 \/ x = 1) /\ (x = 1 \/ x = 2))
/// is transformed into
///   Goal::Univ(x, Goal::Conj(Goal::Disj(Goal::Constr(x = 0), Goal::Constr(x = 1)), Goal::Disj(Goal::Constr(x = 1), Goal::Constr(x = 2))))
use super::TypedPreprocessor;
use crate::formula::hes::{self, GoalKind};
use crate::formula::{self, Constraint, Logic};

pub struct UnpackConstrTransform {}

type Goal = hes::Goal<Constraint>;

fn transform_constr(c: &Constraint) -> Goal {
    match c.kind() {
        formula::ConstraintExpr::True
        | formula::ConstraintExpr::False
        | formula::ConstraintExpr::Pred(_, _) => Goal::mk_constr(c.clone()),
        formula::ConstraintExpr::Conj(c1, c2) => {
            let g1 = transform_constr(c1);
            let g2 = transform_constr(c2);
            Goal::mk_conj(g1, g2)
        }
        formula::ConstraintExpr::Disj(c1, c2) => {
            let g1 = transform_constr(c1);
            let g2 = transform_constr(c2);
            Goal::mk_disj(g1, g2)
        }
        formula::ConstraintExpr::Quantifier(q, v, c) => {
            assert!(q.is_universal());
            let g = transform_constr(c);
            Goal::mk_univ(v.clone(), g)
        }
    }
}

fn transform_goal(g: &Goal) -> Goal {
    match g.kind() {
        GoalKind::Constr(c) => transform_constr(c),
        GoalKind::Op(_) | GoalKind::Var(_) => g.clone(),
        GoalKind::Abs(x, g) => {
            let g = transform_goal(g);
            Goal::mk_abs(x.clone(), g)
        }
        GoalKind::App(g1, g2) => {
            let g1 = transform_goal(g1);
            let g2 = transform_goal(g2);
            Goal::mk_app(g1, g2)
        }
        GoalKind::Conj(g1, g2) => {
            let g1 = transform_goal(g1);
            let g2 = transform_goal(g2);
            Goal::mk_conj(g1, g2)
        }
        GoalKind::Disj(g1, g2) => {
            let g1 = transform_goal(g1);
            let g2 = transform_goal(g2);
            Goal::mk_disj(g1, g2)
        }
        GoalKind::Univ(x, g) => {
            let g = transform_goal(g);
            Goal::mk_univ(x.clone(), g)
        }
        GoalKind::ITE(c, g1, g2) => {
            let c = c.clone();
            let g1 = transform_goal(g1);
            let g2 = transform_goal(g2);
            Goal::mk_ite(c, g1, g2)
        }
    }
}

impl TypedPreprocessor for UnpackConstrTransform {
    fn transform_goal(
        &self,
        goal: &formula::hes::Goal<formula::Constraint>,
        _t: &formula::Type,
        _env: &mut formula::TyEnv,
    ) -> formula::hes::Goal<formula::Constraint> {
        debug!("transform_goal: {}", goal);
        let g = transform_goal(goal);
        debug!("transformed: {}", g);
        g
    }
}

pub fn transform(problem: hes::Problem<formula::Constraint>) -> hes::Problem<formula::Constraint> {
    crate::title!("unpack_constr");
    let t = UnpackConstrTransform {};
    t.transform(problem)
}

#[test]
fn test_transform() {
    use crate::formula::*;
    // Goal::Constr(forall x. (x = 0 \/ x = 1) /\ (x = 1 \/ x = 2))
    let x = Ident::fresh();
    let c1 = Constraint::mk_eq(Op::mk_var(x), Op::zero());
    let c2 = Constraint::mk_eq(Op::mk_var(x), Op::one());
    let c3 = Constraint::mk_eq(Op::mk_var(x), Op::mk_const(2));
    let c = Constraint::mk_conj(
        Constraint::mk_disj(c1.clone(), c2.clone()),
        Constraint::mk_disj(c2.clone(), c3.clone()),
    );
    let c = Constraint::mk_univ_int(x, c);
    let g = Goal::mk_constr(c);

    println!("before: {g}");
    let g2 = transform_goal(&g);
    println!("after: {g2}");
    assert_ne!(g, g2);
    assert_eq!(g.to_string(), g2.to_string());
}
