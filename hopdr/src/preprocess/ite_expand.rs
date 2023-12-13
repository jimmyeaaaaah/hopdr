/// ## ite expand
/// Assumption: the input formula is eta-expanded.
/// This module expands if-then-else expressions in Op.
/// For example, `y = if x > 0 then 1 else 0` is expaneded to if x > 0 then y = 1 else y = 0.
use crate::formula;
use crate::formula::hes::Goal;
use crate::formula::Constraint;
use crate::formula::ExpandITEState;
use crate::formula::{hes, Logic, Negation};

use either::Either;

fn transform_goal(goal: &hes::Goal<formula::Constraint>) -> hes::Goal<formula::Constraint> {
    use hes::GoalKind;
    type Goal = hes::Goal<formula::Constraint>;
    fn translate(goal: &Goal) -> ExpandITEState<hes::Goal<formula::Constraint>> {
        match goal.kind() {
            GoalKind::Constr(c) => formula::expand_ite_constr_once(c).map(|c| Goal::mk_constr(c)),
            hes::GoalKind::Op(o) => match formula::expand_ite_op(o) {
                Some((c, o1, o2)) => {
                    return ExpandITEState::in_progress(c, Goal::mk_op(o1), Goal::mk_op(o2))
                }
                None => ExpandITEState::id(goal.clone()),
            },
            GoalKind::Var(_) => ExpandITEState::id(goal.clone()),
            GoalKind::Abs(x, g) => {
                let g = translate(g).finalize_goal();
                ExpandITEState::id(Goal::mk_abs(x.clone(), g))
            }
            GoalKind::App(g1, g2) => {
                let g1 = match translate(g1) {
                    ExpandITEState::Modified(g) | ExpandITEState::NotModified(g) => g,
                    _ => panic!("program error"),
                };
                let g2 = translate(g2).finalize_goal();
                ExpandITEState::id(Goal::mk_app(g1, g2))
            }
            GoalKind::Univ(x, g) => {
                let g = translate(g).finalize_goal();
                ExpandITEState::id(Goal::mk_univ(x.clone(), g))
            }
            GoalKind::Conj(g1, g2) => {
                ExpandITEState::handle_two(g1.clone(), g2.clone(), Goal::mk_conj, translate)
            }
            GoalKind::Disj(g1, g2) => {
                ExpandITEState::handle_two(g1.clone(), g2.clone(), Goal::mk_disj, translate)
            }
        }
    }
    debug!("transform_goal: {goal}");
    let g = translate(goal).finalize_goal();
    debug!("transform_goal: {g}");
    g
}

fn transform_clause(clause: hes::Clause<formula::Constraint>) -> hes::Clause<formula::Constraint> {
    let mut body = transform_goal(&clause.body);
    loop {
        let body_new = transform_goal(&body);
        if body == body_new {
            break;
        }
        body = body_new;
    }
    hes::Clause { body, ..clause }
}

#[allow(dead_code)]
pub fn transform(problem: hes::Problem<formula::Constraint>) -> hes::Problem<formula::Constraint> {
    crate::title!("remove_tmp_vars");
    let clauses = problem
        .clauses
        .into_iter()
        .map(|c| transform_clause(c))
        .collect();
    let top = transform_goal(&problem.top);
    hes::Problem { top, clauses }
}

#[test]
fn test_transform() {
    use crate::parse::parse_chc;

    let s = "(set-logic HORN)
(declare-fun inv (Int Int) Bool)
(assert (forall ((y0 Int) (x0 Int)) (=> (and (= x0 0) (= y0 5000)) (inv x0 y0))))
(assert (forall ((y1 Int) (x1 Int) (y0 Int) (x0 Int))
  (let ((a!1 (and (inv x0 y0)
                  (= x1 (+ x0 1))
                  (= y1 (ite (>= x0 5000) (+ y0 1) y0)))))
    (=> a!1 (inv x1 y1)))))
(assert (forall ((x0 Int) (y0 Int))
  (=> (and (inv x0 y0) (= x0 10000) (= y0 x0)) false)))
(check-sat)";
    let chcs = parse_chc(s).unwrap();
    let problem = crate::formula::chc::translate_to_hes(chcs);
    assert_eq!(problem.clauses.len(), 1);
    let c = problem.clauses[0].clone();
    println!("before: {c}");
    let c = transform_clause(c);
    println!("{c}");
}
