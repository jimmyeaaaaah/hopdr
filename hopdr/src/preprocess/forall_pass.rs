// simplify some exprs in a peephole way
//  - flatten (\x. g) g2 -> [g2/x]g
//  - flatten (∀x. (x = 0 \/ g1) /\ (x != 0 \/ g2)) -> g1 /\ g2 when x ∉ fv(g1)∪fv(g2)

use crate::formula::{self, Constraint, Negation, Subst};
use crate::formula::{hes, Fv, Logic};

fn transform_goal(goal: &hes::Goal<formula::Constraint>) -> hes::Goal<formula::Constraint> {
    use hes::GoalKind;

    type Goal = hes::Goal<formula::Constraint>;

    fn divide_disj(g11: &Goal, g12: &Goal) -> Option<(Constraint, Goal)> {
        let c1: Option<Constraint> = g11.clone().into();
        match c1 {
            Some(c) => Some((c, g12.clone())),
            None => {
                let c2: Option<Constraint> = g12.clone().into();
                c2.map(|c| (c, g11.clone()))
            }
        }
    }

    fn flatten(goal: Goal) -> Goal {
        let (x, inner) = match goal.kind() {
            GoalKind::Univ(x, inner) => (x, inner.clone()),
            _ => return goal,
        };
        let (g1, g2) = match inner.kind() {
            GoalKind::Conj(g1, g2) => (g1, g2),
            _ => return goal,
        };
        let (c1, g1) = match g1.kind() {
            GoalKind::Disj(g11, g12) => match divide_disj(g11, g12) {
                Some(x) => x,
                None => return goal,
            },
            GoalKind::Constr(c) => match c.kind() {
                formula::ConstraintExpr::Disj(c1, c2) => (c1.clone(), Goal::mk_constr(c2.clone())),
                _ => return goal,
            },
            _ => return goal,
        };
        let (c2, g2) = match g2.kind() {
            GoalKind::Disj(left, right) => match divide_disj(left, right) {
                Some(x) => x,
                None => return goal,
            },
            GoalKind::Constr(c) => match c.kind() {
                formula::ConstraintExpr::Disj(c1, c2) => (c1.clone(), Goal::mk_constr(c2.clone())),
                _ => return goal,
            },
            _ => return goal,
        };
        if c1.negate().unwrap() == c2 && !g1.fv().contains(&x.id) && !g2.fv().contains(&x.id) {
            Goal::mk_conj(g1, g2)
        } else {
            goal
        }
    }

    fn translate(goal: &Goal) -> Goal {
        match goal.kind() {
            GoalKind::Constr(_) | hes::GoalKind::Op(_) | GoalKind::Var(_) => goal.clone(),
            GoalKind::Abs(x, g) => {
                let g = translate(g);
                Goal::mk_abs(x.clone(), g)
            }
            // flatten (\x. g) g2 -> [g2/x]g
            GoalKind::App(g1, g2) => match g1.kind() {
                GoalKind::Abs(x, g) => g.subst(x, g2),
                _ => Goal::mk_app(translate(g1), translate(g2)),
            },
            GoalKind::Univ(x, g) => flatten(Goal::mk_univ(x.clone(), translate(g))),
            GoalKind::Conj(g1, g2) => Goal::mk_conj(translate(g1), translate(g2)),
            GoalKind::Disj(g1, g2) => Goal::mk_disj(translate(g1), translate(g2)),
            GoalKind::ITE(c, g1, g2) => Goal::mk_ite(c.clone(), translate(g1), translate(g2)),
        }
    }
    translate(goal)
}

fn transform_clause(clause: hes::Clause<formula::Constraint>) -> hes::Clause<formula::Constraint> {
    let body = transform_goal(&clause.body);
    hes::Clause { body, ..clause }
}

pub fn transform(problem: hes::Problem<formula::Constraint>) -> hes::Problem<formula::Constraint> {
    crate::stat::preprocess::start_clock("forall_pass");

    let clauses = problem
        .clauses
        .into_iter()
        .map(|c| transform_clause(c))
        .collect();
    let top = transform_goal(&problem.top);
    crate::stat::preprocess::end_clock("forall_pass");
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
    F x =v ∀m. (m = 0 \\/ (\\n. (n+1) > 0) x) /\\ (m != 0 \\/ x > 0).
    ";
    let (_, f) = parse::<VerboseError<&str>>(s).unwrap();
    // FIXME: hes::preprocess contains eta's path, and it's inevitable currently;
    // therefore, checking if hes::preprocess succeeds is the current check of this test..
    let (vc, _ctx) = preprocess::hes::preprocess_with_default_config(f);
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
