use super::safety::check_dual;
/// This pass finds the pattern (c \/ g1) /\ (not c \/ g2) and replaces it with ite(not c, g1, g2).
/// For example, a formula ∀x. x != 0 \/ P(x, y) can be translated to P(0, y).
use super::TypedPreprocessor;
use crate::formula::hes::{self, GoalKind};
use crate::formula::{self, Bot, Constraint, FormulaSize, Fv, Logic, Negation, Top};

pub struct FindITETransform {}

type Goal = hes::Goal<Constraint>;

fn get_smaller_condition(c1: Constraint, c2: Constraint) -> Constraint {
    let c1 = c1.negate().unwrap();
    if c1.formula_size() < c2.formula_size() {
        c1
    } else {
        c2
    }
}

fn contains_same_fv(g: &Goal, g2: &Goal) -> bool {
    g.fv() == g2.fv()
}

fn find_match(gs: &Vec<Goal>, gs2: &Vec<Goal>) -> Option<(Constraint, Goal, Goal)> {
    fn aux(gs: &Vec<Goal>, idx: usize) -> Goal {
        gs.iter()
            .enumerate()
            .filter(|(k, _)| *k != idx)
            .fold(Goal::mk_false(), |acc, (_, g)| {
                Goal::mk_disj_opt(acc, g.clone())
            })
    }
    for (i, g1) in gs.iter().enumerate() {
        for (j, g2) in gs2.iter().enumerate() {
            if contains_same_fv(g1, g2) && check_dual(g1, g2) {
                let c = get_smaller_condition(g1.clone().into(), g2.clone().into());
                let g1 = aux(gs, i);
                let g2 = aux(gs2, j);
                return Some((c.clone(), g1, g2));
            }
        }
    }
    None
}

fn f(g: &Goal) -> Goal {
    debug!("target: {g}");
    match g.kind() {
        GoalKind::Constr(_) | GoalKind::Op(_) | GoalKind::Var(_) => g.clone(),
        GoalKind::Abs(x, g) => {
            let g = f(g);
            Goal::mk_abs(x.clone(), g)
        }
        GoalKind::App(g1, g2) => {
            let g1 = f(g1);
            let g2 = f(g2);
            Goal::mk_app(g1, g2)
        }
        GoalKind::Univ(x, g) => {
            let g = f(g);
            Goal::mk_univ(x.clone(), g)
        }
        GoalKind::ITE(c, g1, g2) => {
            let g1 = f(g1);
            let g2 = f(g2);
            Goal::mk_ite_opt(c.clone(), g1, g2)
        }
        GoalKind::Conj(_, _) => {
            let mut gs: Vec<_> = g
                .vec_of_conjs()
                .iter()
                .map(|g| f(g).vec_of_disjs().into_iter().cloned().collect())
                .collect();
            let mut gs2 = Vec::new();
            while let Some(g) = gs.pop() {
                let mut found = None;
                for (i, g2) in gs.iter().enumerate() {
                    if let Some((c, g, g2)) = find_match(&g, g2) {
                        found = Some((i, c, g, g2));
                        debug!("found");
                        break;
                    }
                }
                if let Some((i, c, g, g2)) = found {
                    gs.remove(i);
                    gs2.push(Goal::mk_ite_opt(c, g, g2));
                } else {
                    gs2.push(
                        g.into_iter()
                            .fold(Goal::mk_false(), |acc, g| Goal::mk_disj_opt(acc, g.clone())),
                    );
                }
            }
            gs2.into_iter()
                .fold(Goal::mk_true(), |acc, g| Goal::mk_conj_opt(acc, g))
        }
        GoalKind::Disj(g1, g2) => {
            let g1 = f(g1);
            let g2 = f(g2);
            Goal::mk_disj(g1, g2)
        }
    }
}

impl TypedPreprocessor for FindITETransform {
    const PASS_NAME: &'static str = "find ite";

    fn transform_goal(
        &self,
        goal: &formula::hes::Goal<formula::Constraint>,
        _t: &formula::Type,
        _env: &mut formula::TyEnv,
    ) -> formula::hes::Goal<formula::Constraint> {
        debug!("transform_goal: {goal}");
        let g = f(goal);
        debug!("translated: {g}");
        g
    }
}

pub fn transform(problem: hes::Problem<formula::Constraint>) -> hes::Problem<formula::Constraint> {
    crate::title!("find_ite");
    let t = FindITETransform {};
    t.transform(problem)
}

#[test]
fn test_transform() {
    use crate::formula::{Constraint, Ident, Op, OpKind, Variable};
    use hes::Goal;
    // (x < 0 \/ F x) /\ (x >= 0 \/ F (0 - x))
    let xi: Ident = Ident::fresh();
    let x = Op::mk_var(xi);
    let zero = Op::mk_const(0);
    let func = Ident::fresh();

    let c1 = Constraint::mk_lt(x.clone(), zero.clone());
    let a11 = Goal::mk_constr(c1);
    let a12 = Goal::mk_app(Goal::mk_var(func), Goal::mk_var(xi));

    let c2 = Constraint::mk_geq(x.clone(), zero.clone());
    let a21 = Goal::mk_constr(c2);
    let o = Op::mk_bin_op(OpKind::Sub, zero.clone(), x.clone());
    let a22 = Goal::mk_app(Goal::mk_var(func), Goal::mk_op(o));

    let mut gs = Vec::new();

    let a1 = Goal::mk_disj(a11.clone(), a12.clone());
    let a2 = Goal::mk_disj(a21.clone(), a22.clone());
    let a = Goal::mk_conj(a1, a2);
    gs.push(a.clone());

    let a1 = Goal::mk_disj(a12.clone(), a11.clone());
    let a2 = Goal::mk_disj(a21.clone(), a22.clone());
    gs.push(Goal::mk_conj(a1, a2));

    let a1 = Goal::mk_disj(a12.clone(), a11.clone());
    let a2 = Goal::mk_disj(a22.clone(), a21.clone());
    gs.push(Goal::mk_conj(a1, a2));

    for g in gs {
        println!("before: {g}");
        let g = f(&g);
        println!("after: {g}");
        assert!(g.is_ite());
    }

    let v = Variable::fresh_int();
    let g = Goal::mk_abs(v.clone(), a);
    println!("before: {g}");
    let g = f(&g);
    println!("after: {g}");
    match g.kind() {
        hes::GoalKind::Abs(v2, g) if &v == v2 => {
            assert!(g.is_ite())
        }
        _ => assert!(false),
    }
}
