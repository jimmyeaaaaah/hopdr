/// add extra variables for hint
/// currently, we just add one variable.
// eta transformation
use crate::formula;
use crate::formula::hes;

fn transform_goal(goal: &hes::Goal<formula::Constraint>) -> hes::Goal<formula::Constraint> {
    type Goal = hes::Goal<formula::Constraint>;
    let x = formula::Ident::fresh();
    let t = formula::Type::mk_type_int();
    let v = formula::Variable::mk(x, t);
    Goal::mk_univ(v, goal.clone())
}

#[allow(dead_code)]
pub fn transform(problem: hes::Problem<formula::Constraint>) -> hes::Problem<formula::Constraint> {
    let top = transform_goal(&problem.top);
    hes::Problem { top, ..problem }
}

#[test]
fn test_transform() {
    use hes::Goal;
    let x = formula::Ident::fresh();
    let g = Goal::mk_disj(Goal::mk_var(x), Goal::mk_var(x));
    let g2 = transform_goal(&g);
    match g2.kind() {
        hes::GoalKind::Univ(_, g3) => {
            assert_eq!(&g, g3);
        }
        _ => assert!(false),
    }
}
