/// ## ite expand
/// This module expands if-then-else expressions in Op.
/// For example, `y = if x > 0 then 1 else 0` is expaneded to if x > 0 then y = 1 else y = 0.
use crate::formula;
use crate::formula::{hes, Logic};

fn transform_goal(goal: &hes::Goal<formula::Constraint>) -> hes::Goal<formula::Constraint> {
    use hes::GoalKind;

    type Goal = hes::Goal<formula::Constraint>;

    fn translate(goal: &Goal) -> Goal {
        match goal.kind() {
            GoalKind::Constr(c) => Goal::mk_constr(formula::expand_ite_constr_once(c)),
            hes::GoalKind::Op(_) => {
                unimplemented!()
            }
            GoalKind::Var(_) => goal.clone(),
            GoalKind::Abs(x, g) => {
                let g = translate(g);
                Goal::mk_abs(x.clone(), g)
            }
            GoalKind::App(g1, g2) => {
                let g1 = translate(g1);
                let g2 = translate(g2);
                Goal::mk_app(g1, g2)
            }
            GoalKind::Univ(x, g) => Goal::mk_univ(x.clone(), translate(g)),
            GoalKind::Conj(g1, g2) => Goal::mk_conj(translate(g1), translate(g2)),
            GoalKind::Disj(g1, g2) => Goal::mk_disj(translate(g1), translate(g2)),
        }
    }
    translate(goal)
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
