/// This pass removes the integer introduced for temporary variables.
/// For example, a formula ∀x. x != 0 \/ P(x, y) can be translated to P(0, y).
use super::TypedPreprocessor;
use crate::formula::hes::{self, GoalKind};
use crate::formula::{self, Bot, Constraint, Fv, Ident, Logic, Op};

use std::collections::HashSet;

pub struct RemoveTmpVarTransform {}

type Goal = hes::Goal<Constraint>;

fn handle_constraint(
    c: &Constraint,
    eqs: &mut Vec<(Ident, Op)>,
    tmp_vars: &mut HashSet<Ident>,
    inner_disj: bool, // for the simplicity, we don't consider the nesting of disj (conj (disj)). So we have to track whether we have already encountered disj.
) -> Constraint {
    match c.kind() {
        formula::ConstraintExpr::True | formula::ConstraintExpr::False => c.clone(),
        formula::ConstraintExpr::Pred(p, l) if l.len() == 2 => match p {
            formula::PredKind::Neq => {
                let (x, y) = (&l[0], &l[1]);
                let mut fv = x.fv();
                y.fv_with_vec(&mut fv);
                for target in tmp_vars.iter() {
                    if fv.contains(target) {
                        match Op::solve_for(target, x, y) {
                            Some(o) => {
                                eqs.push((target.clone(), o));
                                return Constraint::mk_false();
                            }
                            None => (),
                        }
                    }
                }
                c.clone()
            }
            _ => c.clone(),
        },
        formula::ConstraintExpr::Pred(_, _) => c.clone(),
        formula::ConstraintExpr::Conj(c1, c2) => {
            let c1 = handle_constraint(c1, eqs, tmp_vars, inner_disj);
            let c2 = handle_constraint(c2, eqs, tmp_vars, inner_disj);
            Constraint::mk_conj(c1, c2)
        }
        formula::ConstraintExpr::Disj(c1, c2) => {
            if inner_disj {
                return c.clone();
            }
            let c1 = handle_constraint(c1, eqs, tmp_vars, true);
            let c2 = handle_constraint(c2, eqs, tmp_vars, true);
            Constraint::mk_disj(c1, c2)
        }
        formula::ConstraintExpr::Quantifier(_, _, _) => c.clone(),
    }
}

fn app_eqs(mut g: Goal, eqs: Vec<(Ident, Op)>) -> Goal {
    for (x, o) in eqs {
        g = g.isubst(&x, &o);
    }
    g
}

// main function for the transformation
fn f(g: &Goal, tmp_vars: &mut HashSet<Ident>) -> (Goal, Vec<(Ident, Op)>) {
    match g.kind() {
        GoalKind::Constr(_) | GoalKind::Op(_) | GoalKind::Var(_) => (g.clone(), Vec::new()),
        GoalKind::Abs(x, g) => {
            let (g, eqs) = f(g, tmp_vars);
            let g = app_eqs(g, eqs);
            (Goal::mk_abs(x.clone(), g), Vec::new())
        }
        GoalKind::App(g1, g2) => {
            let (g1, eqs) = f(g1, tmp_vars);
            let g1 = app_eqs(g1, eqs);
            let (g2, eqs) = f(g2, tmp_vars);
            let g2 = app_eqs(g2, eqs);
            (Goal::mk_app(g1, g2), Vec::new())
        }
        GoalKind::Conj(g1, g2) => {
            let (g1, eqs) = f(g1, tmp_vars);
            let g1 = app_eqs(g1, eqs);
            let (g2, eqs) = f(g2, tmp_vars);
            let g2 = app_eqs(g2, eqs);
            (Goal::mk_conj_opt(g1, g2), Vec::new())
        }
        GoalKind::Disj(_, _) => match g.disj_constr() {
            either::Either::Left((c, g)) => {
                let (g, mut eqs) = f(g, tmp_vars);
                let c = handle_constraint(c, &mut eqs, tmp_vars, false);
                (Goal::mk_disj_opt(Goal::mk_constr(c), g), eqs)
            }
            either::Either::Right((g1, g2)) => {
                let (g1, eqs1) = f(g1, tmp_vars);
                let (g2, eqs2) = f(g2, tmp_vars);
                let mut eqs = Vec::new();
                eqs.extend(eqs1);
                eqs.extend(eqs2);
                (Goal::mk_disj_opt(g1, g2), eqs)
            }
        },
        GoalKind::Univ(x, g) => {
            let flag = tmp_vars.insert(x.id);
            let (g, eqs) = f(g, tmp_vars);
            let g = app_eqs(g, eqs);
            if !flag {
                tmp_vars.remove(&x.id);
            }
            if g.fv().contains(&x.id) {
                (Goal::mk_univ(x.clone(), g), Vec::new())
            } else {
                (g, Vec::new())
            }
        }
    }
}

impl TypedPreprocessor for RemoveTmpVarTransform {
    fn transform_goal(
        &self,
        goal: &formula::hes::Goal<formula::Constraint>,
        _t: &formula::Type,
        _env: &mut formula::TyEnv,
    ) -> formula::hes::Goal<formula::Constraint> {
        let (g, eqs) = f(goal, &mut HashSet::new());
        app_eqs(g, eqs)
    }
}

pub fn transform(problem: hes::Problem<formula::Constraint>) -> hes::Problem<formula::Constraint> {
    let t = RemoveTmpVarTransform {};
    t.transform(problem)
}

#[test]
fn test_remove_tmp_var() {
    use formula::Variable;
    // goal: ∀x. x != 0 \/ P(x, y)
    let x = Ident::fresh();
    let xv = Variable::mk(x, formula::Type::mk_type_int());
    let y = Ident::fresh();
    let p = Ident::fresh();
    let c = Goal::mk_constr(Constraint::mk_neq(Op::mk_var(x.clone()), Op::zero()));
    let g = Goal::mk_app(
        Goal::mk_app(Goal::mk_var(p.clone()), Goal::mk_op(Op::mk_var(x.clone()))),
        Goal::mk_op(Op::mk_var(y.clone())),
    );
    let g = Goal::mk_disj(c, g);
    let g = Goal::mk_univ(xv, g);
    println!("target: {g}");
    let tr = RemoveTmpVarTransform {};
    let g = tr.transform_goal(
        &g,
        &formula::Type::mk_type_prop(),
        &mut formula::TyEnv::new(),
    );
    println!("translated: {g}");
}
