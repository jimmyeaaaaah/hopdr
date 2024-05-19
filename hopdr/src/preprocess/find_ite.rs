use super::safety::check_dual;
/// This pass finds the pattern (c \/ g1) /\ (not c \/ g2) and replaces it with ite(not c, g1, g2).
/// For example, a formula ∀x. x != 0 \/ P(x, y) can be translated to P(0, y).
use super::TypedPreprocessor;
use crate::formula::hes::{self, GoalKind};
use crate::formula::{self, Bot, Constraint, FormulaSize, Fv, Logic, Negation, Top};

pub struct FindITETransform {
    lightweight: bool,
}

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

impl FindITETransform {
    fn disj_except_for(gs: &Vec<Goal>, idx: usize) -> (Goal, Goal) {
        let g_aux = gs[idx].clone();
        let g = gs
            .iter()
            .enumerate()
            .filter(|(k, _)| *k != idx)
            .fold(Goal::mk_false(), |acc, (_, g)| {
                Goal::mk_disj_opt(acc, g.clone())
            });
        (g, g_aux)
    }
    // (c \/ g1) /\ (not c \/ g2) -> (c as constr, g1, g2, c, not c)
    fn find_match(
        &self,
        gs: &Vec<Goal>,
        gs2: &Vec<Goal>,
    ) -> Option<(Constraint, Goal, Goal, Goal, Goal)> {
        for (i, g1) in gs.iter().enumerate() {
            for (j, g2) in gs2.iter().enumerate() {
                if contains_same_fv(g1, g2) && check_dual(g1, g2, self.lightweight) {
                    let c = get_smaller_condition(g1.clone().into(), g2.clone().into());
                    let (g1, g1_aux) = Self::disj_except_for(gs, i);
                    let (g2, g2_aux) = Self::disj_except_for(gs2, j);
                    return Some((c.clone(), g1, g2, g1_aux, g2_aux));
                }
            }
        }
        None
    }
    fn f(&self, g: &Goal) -> Goal {
        debug!("target: {g}");
        match g.kind() {
            GoalKind::Constr(_) | GoalKind::Op(_) | GoalKind::Var(_) => g.clone(),
            GoalKind::Abs(x, g) => {
                let g = self.f(g);
                Goal::mk_abs(x.clone(), g)
            }
            GoalKind::App(g1, g2) => {
                let g1 = self.f(g1);
                let g2 = self.f(g2);
                Goal::mk_app(g1, g2)
            }
            GoalKind::Univ(x, g) => {
                let g = self.f(g);
                Goal::mk_univ(x.clone(), g)
            }
            GoalKind::ITE(c, g1, g2) => {
                let g1 = self.f(g1);
                let g2 = self.f(g2);
                Goal::mk_ite_opt(c.clone(), g1, g2)
            }
            GoalKind::Conj(_, _) => {
                let mut gs: Vec<_> = g
                    .vec_of_conjs()
                    .iter()
                    .map(|g| self.f(g).vec_of_disjs().into_iter().cloned().collect())
                    .collect();
                let mut gs2 = Vec::new();
                while let Some(g) = gs.pop() {
                    let mut found = None;
                    for (i, g2) in gs.iter().enumerate() {
                        if let Some((c, g, g2, g1_aux, g2_aux)) = self.find_match(&g, g2) {
                            found = Some((i, c, g, g2, g1_aux, g2_aux));
                            debug!("found");
                            break;
                        }
                    }
                    if let Some((i, c, mut g, mut g2, g1_aux, g2_aux)) = found {
                        gs.remove(i);
                        // handle (g1 \/ g2) /\ (not(g1) \/ g3) /\ (g1 \/ g4) /\ (not(g1) \/ g5)
                        // to if (not(g1)) (g2 /\ g4) else g3 /\ g5
                        let mut gs_new = Vec::new();
                        for g3 in gs {
                            let mut flag = 0;
                            let mut target = None;
                            for (i, c) in g3.iter().enumerate() {
                                if c == &g1_aux {
                                    flag = 1;
                                    target = Some(i);
                                    break;
                                } else if c == &g2_aux {
                                    flag = 2;
                                    target = Some(i);
                                    break;
                                }
                            }
                            if flag == 1 {
                                let (g3, _) = Self::disj_except_for(&g3, target.unwrap());
                                g = Goal::mk_conj_opt(g, g3)
                            } else if flag == 2 {
                                let (g3, _) = Self::disj_except_for(&g3, target.unwrap());
                                g2 = Goal::mk_conj_opt(g2, g3)
                            } else {
                                gs_new.push(g3)
                            }
                        }
                        gs = gs_new;
                        let g = self.f(&g);
                        let g2 = self.f(&g2);
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
                let g1 = self.f(g1);
                let g2 = self.f(g2);
                Goal::mk_disj(g1, g2)
            }
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
        let g = self.f(goal);
        debug!("translated: {g}");
        g
    }
}

pub fn transform(
    problem: hes::Problem<formula::Constraint>,
    lightweight: bool,
) -> hes::Problem<formula::Constraint> {
    crate::title!("find_ite");
    let t = FindITETransform { lightweight };
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

    let trans = FindITETransform { lightweight: false };

    for g in gs {
        println!("before: {g}");
        let g = trans.f(&g);
        println!("after: {g}");
        assert!(g.is_ite());
    }

    let v = Variable::fresh_int();
    let g = Goal::mk_abs(v.clone(), a);
    println!("before: {g}");
    let g = trans.f(&g);
    println!("after: {g}");
    match g.kind() {
        hes::GoalKind::Abs(v2, g) if &v == v2 => {
            assert!(g.is_ite())
        }
        _ => assert!(false),
    }
}

#[test]
fn test_nested_if() {
    use crate::formula::{Constraint, Ident, Op};
    use hes::Goal;
    // (x < 0 \/ F x) /\ (x >= 0 \/ x = 0 \/ y > 0) /\ (x >= 0 \/ x != 0 \/ y < 0)
    let xi: Ident = Ident::fresh();
    let x = Op::mk_var(xi);
    let yi: Ident = Ident::fresh();
    let y = Op::mk_var(yi);
    let zero = Op::mk_const(0);
    let func = Ident::fresh();

    let c1 = Constraint::mk_lt(x.clone(), zero.clone());
    let a11 = Goal::mk_constr(c1);
    let a12 = Goal::mk_app(Goal::mk_var(func), Goal::mk_var(xi));
    let g1 = Goal::mk_disj(a11.clone(), a12.clone());

    let c2 = Constraint::mk_geq(x.clone(), zero.clone());
    let c3 = Constraint::mk_eq(x.clone(), zero.clone());
    let c4 = Constraint::mk_gt(y.clone(), zero.clone());
    let a21 = Goal::mk_constr(c2);
    let a22 = Goal::mk_constr(c3);
    let a23 = Goal::mk_constr(c4);
    let g2 = Goal::mk_disj(a21.clone(), a22.clone());
    let g2 = Goal::mk_disj(g2, a23);

    let c5 = Constraint::mk_geq(x.clone(), zero.clone());
    let c6 = Constraint::mk_neq(x.clone(), zero.clone());
    let c7 = Constraint::mk_lt(y.clone(), zero.clone());
    let a31 = Goal::mk_constr(c5);
    let a32 = Goal::mk_constr(c6);
    let a33 = Goal::mk_constr(c7);
    let g3 = Goal::mk_disj(a31.clone(), a32.clone());
    let g3 = Goal::mk_disj(g3, a33);

    let a = Goal::mk_conj(g1, g2);
    let g = Goal::mk_conj(a, g3);

    let trans = FindITETransform { lightweight: false };

    println!("before: {g}");
    let g = trans.f(&g);
    println!("after: {g}");
    assert!(g.is_ite());
    let g = trans.f(&g);
    println!("after after: {g}");
    assert!(g.is_ite());
}
