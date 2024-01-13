use super::safety::check_dual;
/// This pass finds the pattern (c \/ g1) /\ (not c \/ g2) and replaces it with ite(not c, g1, g2).
/// For example, a formula ∀x. x != 0 \/ P(x, y) can be translated to P(0, y).
use super::TypedPreprocessor;
use crate::formula::hes::{self, GoalKind};
use crate::formula::{self, Constraint, FormulaSize, Logic, Negation};

pub struct FindITETransform {}

type Goal = hes::Goal<Constraint>;

fn get_smaller_condition(c1: Constraint, c2: Constraint) -> Constraint {
    let c2 = c2.negate().unwrap();
    if c1.formula_size() < c2.formula_size() {
        c1
    } else {
        c2
    }
}

fn get_ite_triple<'a>(
    g11: &'a Goal,
    g12: &'a Goal,
    g21: &'a Goal,
    g22: &'a Goal,
) -> Option<(Constraint, &'a Goal, &'a Goal)> {
    debug!("disjs: ({g11}) | ({g12}) vs ({g21}) | ({g22})");
    if check_dual(g11, g21) {
        let c = get_smaller_condition(g11.clone().into(), g21.clone().into());
        Some((c, g12, g22))
    } else if check_dual(g11, g22) {
        let c = get_smaller_condition(g11.clone().into(), g22.clone().into());
        Some((c, g12, g21))
    } else if check_dual(g12, g21) {
        let c = get_smaller_condition(g12.clone().into(), g21.clone().into());
        Some((c, g11, g22))
    } else if check_dual(g12, g22) {
        let c = get_smaller_condition(g12.clone().into(), g22.clone().into());
        Some((c, g11, g21))
    } else {
        return None;
    }
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
            Goal::mk_ite(c.clone(), g1, g2)
        }

        GoalKind::Conj(g1, g2) => {
            match (
                g1.unwrap_quantifiers().kind(),
                g2.unwrap_quantifiers().kind(),
            ) {
                (GoalKind::Disj(g11, g12), GoalKind::Disj(g21, g22)) => {
                    match get_ite_triple(g11, g12, g21, g22) {
                        Some((c, g1, g2)) => Goal::mk_ite(c, f(g1), f(g2)),
                        None => Goal::mk_conj(f(g1), f(g2)),
                    }
                }
                (GoalKind::Disj(g11, g12), GoalKind::Constr(c))
                | (GoalKind::Constr(c), GoalKind::Disj(g11, g12)) => match c.kind() {
                    formula::ConstraintExpr::Disj(c1, c2) => {
                        match get_ite_triple(
                            g11,
                            g12,
                            &Goal::mk_constr(c1.clone()),
                            &Goal::mk_constr(c2.clone()),
                        ) {
                            Some((c, g1, g2)) => Goal::mk_ite(c, f(g1), f(g2)),
                            None => Goal::mk_conj(f(g1), f(g2)),
                        }
                    }
                    _ => Goal::mk_conj(f(g1), f(g2)),
                },
                _ => Goal::mk_conj(f(g1), f(g2)),
            }
        }
        GoalKind::Disj(g1, g2) => {
            let g1 = f(g1);
            let g2 = f(g2);
            Goal::mk_disj(g1, g2)
        }
    }
}

impl TypedPreprocessor for FindITETransform {
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
    let xi = Ident::fresh();
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
        assert!(g.is_ite());
        println!("after: {g}");
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
