/// ## ite expand
/// Assumption: the input formula is eta-expanded.
/// This module expands if-then-else expressions in Op.
/// For example, `y = if x > 0 then 1 else 0` is expaneded to if x > 0 then y = 1 else y = 0.
use crate::formula;
use crate::formula::Constraint;
use crate::formula::{hes, Logic};

use either::Either;

fn transform_goal(goal: &hes::Goal<formula::Constraint>) -> hes::Goal<formula::Constraint> {
    use hes::GoalKind;
    type Goal = hes::Goal<formula::Constraint>;

    fn translate(goal: &Goal) -> Either<Goal, (Constraint, Goal, Goal)> {
        match goal.kind() {
            GoalKind::Constr(c) => {
                Either::Left(Goal::mk_constr(formula::expand_ite_constr(c.clone())))
            }
            hes::GoalKind::Op(_) => panic!("program error"),
            GoalKind::Var(_) => Either::Left(goal.clone()),
            GoalKind::Abs(x, g) => {
                let g = translate(g);
                match g {
                    Either::Left(g) => Either::Left(Goal::mk_abs(x.clone(), g)),
                    Either::Right((c, g1, g2)) => {
                        unimplemented!()
                    }
                }
            }
            GoalKind::App(g1, g2) => {
                let g1 = translate(g1).unwrap_left();
                let g2 = translate(g2);
                match g2 {
                    Either::Left(g2) => Either::Left(Goal::mk_app(g1, g2)),
                    Either::Right((c, g21, g22)) => {
                        unimplemented!()
                    }
                }
            }
            GoalKind::Univ(x, g) => {
                let g = translate(g);
                match g {
                    Either::Left(g) => Either::Left(Goal::mk_univ(x.clone(), g)),
                    Either::Right((c, g1, g2)) => {
                        unimplemented!()
                    }
                }
            }
            GoalKind::Conj(g1, g2) => {
                let g1 = translate(g1).unwrap_left();
                let g2 = translate(g2).unwrap_left();
                unimplemented!()
            }
            GoalKind::Disj(g1, g2) => {
                let g1 = translate(g1).unwrap_left();
                let g2 = translate(g2).unwrap_left();
                unimplemented!()
            }
        }
    }
    match translate(goal) {
        Either::Left(g) => g,
        Either::Right((c, g1, g2)) => {
            unimplemented!()
        }
    }
}

fn transform_clause(clause: hes::Clause<formula::Constraint>) -> hes::Clause<formula::Constraint> {
    let body = transform_goal(&clause.body);
    hes::Clause { body, ..clause }
}

pub fn transform(problem: hes::Problem<formula::Constraint>) -> hes::Problem<formula::Constraint> {
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
    use crate::parse::parse;
    use crate::parse::parse_chc;
    use crate::preprocess;

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
    let c = transform_clause(c);
}
