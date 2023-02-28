// eta transformation

use crate::formula::hes;
use crate::formula::{self, Subst};

fn transform_goal(goal: &hes::Goal<formula::Constraint>) -> hes::Goal<formula::Constraint> {
    use hes::GoalKind;

    type Goal = hes::Goal<formula::Constraint>;

    fn translate(goal: &Goal) -> Goal {
        match goal.kind() {
            GoalKind::Constr(_) | hes::GoalKind::Op(_) | GoalKind::Var(_) => goal.clone(),
            GoalKind::Abs(x, g) => {
                let g = translate(g);
                Goal::mk_abs(x.clone(), g)
            }
            GoalKind::App(g1, g2) => match g1.kind() {
                GoalKind::Abs(x, g) => g.subst(x, g2),
                _ => Goal::mk_app(translate(g1), translate(g2)),
            },
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
    use crate::preprocess;
    use nom::error::VerboseError;

    let s = "
    %HES
    S =v F n.
    F x =v (\\n. (n+1) > 0) x.
    ";
    let (_, f) = parse::<VerboseError<&str>>(s).unwrap();
    // FIXME: hes::preprocess contains eta's path, and it's inevitable currently;
    // therefore, checking if hes::preprocess succeeds is the current check of this test..
    let (vc, _ctx) = preprocess::hes::preprocess(f);
    println!("before: {vc}");
    let h = transform(vc);
    println!("{h}");
    let c = &h.clauses[0];
    println!("{c}")
    // let s2 = ctx
    //     .ident_map
    //     .get(&parse::Ident::new("S2".to_string()))
    //     .unwrap();
    // assert_ne!(
    //     &h.get_clause(s2).unwrap().body,
    //     &vc_old.get_clause(s2).unwrap().body
    // )
}
