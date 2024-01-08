// Transform a non-linear clause to a linear clause taken from safety property
// problems. For example,
//    (x <= 0 /\ P(x, y)) \/ (x > 0 /\ Q(x, y))
// can be reduced to
//    (x <= 0 \/ Q(x, y)) /\ (x > 0 \/ P(x, y))

use crate::formula;
use crate::formula::hes;
use crate::formula::Logic;

fn transform_goal(goal: &hes::Goal<formula::Constraint>) -> hes::Goal<formula::Constraint> {
    use crate::formula::Negation;
    use hes::GoalKind;
    let f = transform_goal;

    type Goal = hes::Goal<formula::Constraint>;

    fn check_dual(g1: &Goal, g2: &Goal) -> bool {
        match (g1.kind(), g2.kind()) {
            (GoalKind::Constr(c1), GoalKind::Constr(c2)) => {
                let c2 = c2.negate().unwrap();
                c1 == &c2
            }
            _ => false,
        }
    }

    match goal.kind() {
        GoalKind::Disj(g1, g2) => match (g1.kind(), g2.kind()) {
            (GoalKind::Conj(g11, g12), GoalKind::Conj(g21, g22)) => {
                if check_dual(g11, g21) {
                    Goal::mk_conj(
                        Goal::mk_disj(g21.clone(), g12.clone()),
                        Goal::mk_disj(g11.clone(), g22.clone()),
                    )
                } else if check_dual(g11, g22) {
                    Goal::mk_conj(
                        Goal::mk_disj(g22.clone(), g12.clone()),
                        Goal::mk_disj(g11.clone(), g21.clone()),
                    )
                } else if check_dual(g12, g21) {
                    Goal::mk_conj(
                        Goal::mk_disj(g21.clone(), g11.clone()),
                        Goal::mk_disj(g12.clone(), g22.clone()),
                    )
                } else if check_dual(g12, g22) {
                    Goal::mk_conj(
                        Goal::mk_disj(g22.clone(), g11.clone()),
                        Goal::mk_disj(g12.clone(), g21.clone()),
                    )
                } else {
                    Goal::mk_disj(f(g1), f(g2))
                }
            }
            _ => Goal::mk_disj(f(g1), f(g2)),
        },
        GoalKind::Constr(_) | hes::GoalKind::Op(_) | GoalKind::Var(_) => goal.clone(),
        GoalKind::Abs(x, g) => Goal::mk_abs(x.clone(), f(g)),
        GoalKind::Univ(x, g) => Goal::mk_univ(x.clone(), f(g)),
        GoalKind::App(g1, g2) => Goal::mk_app(f(g1), f(g2)),
        GoalKind::Conj(g1, g2) => Goal::mk_conj(f(g1), f(g2)),
        GoalKind::ITE(c, g1, g2) => Goal::mk_ite(c.clone(), f(g1), f(g2)),
    }
}

fn transform_clause(clause: hes::Clause<formula::Constraint>) -> hes::Clause<formula::Constraint> {
    let body = transform_goal(&clause.body);
    hes::Clause { body, ..clause }
}

pub fn transform(problem: hes::Problem<formula::Constraint>) -> hes::Problem<formula::Constraint> {
    let clauses = problem.clauses.into_iter().map(transform_clause).collect();
    let top = transform_goal(&problem.top);
    hes::Problem { top, clauses }
}

#[test]
fn test_transform() {
    use crate::formula::{Constraint, Ident, Op, OpKind, Variable};
    use hes::Goal;
    // (x < 0 /\ F x) \/ (x >= 0 /\ F (0 - x))
    let xi = Ident::fresh();
    let x = Op::mk_var(xi);
    let zero = Op::mk_const(0);
    let f = Ident::fresh();

    let c1 = Constraint::mk_lt(x.clone(), zero.clone());
    let a11 = Goal::mk_constr(c1);
    let a12 = Goal::mk_app(Goal::mk_var(f), Goal::mk_var(xi));

    let c2 = Constraint::mk_geq(x.clone(), zero.clone());
    let a21 = Goal::mk_constr(c2);
    let o = Op::mk_bin_op(OpKind::Sub, zero.clone(), x.clone());
    let a22 = Goal::mk_app(Goal::mk_var(f), Goal::mk_op(o));

    let mut gs = Vec::new();

    let a1 = Goal::mk_conj(a11.clone(), a12.clone());
    let a2 = Goal::mk_conj(a21.clone(), a22.clone());
    let a = Goal::mk_disj(a1, a2);
    gs.push(a.clone());

    let a1 = Goal::mk_conj(a12.clone(), a11.clone());
    let a2 = Goal::mk_conj(a21.clone(), a22.clone());
    gs.push(Goal::mk_disj(a1, a2));

    let a1 = Goal::mk_conj(a12.clone(), a11.clone());
    let a2 = Goal::mk_conj(a22.clone(), a21.clone());
    gs.push(Goal::mk_disj(a1, a2));

    for g in gs {
        assert!(transform_goal(&g).is_conj());
    }

    let v = Variable::fresh_int();
    let g = Goal::mk_abs(v.clone(), a);
    let g = transform_goal(&g);
    match g.kind() {
        hes::GoalKind::Abs(v2, g) if &v == v2 => {
            assert!(g.is_conj())
        }
        _ => assert!(false),
    }
}
