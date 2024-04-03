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
) -> Constraint {
    match c.kind() {
        formula::ConstraintExpr::Pred(p, l) if l.len() == 2 => match p {
            formula::PredKind::Neq => {
                let (x, y) = (&l[0], &l[1]);
                let mut fv = x.fv();
                y.fv_with_vec(&mut fv);
                for target in tmp_vars.iter() {
                    if fv.contains(target) {
                        match Op::solve_for(target, x, y) {
                            Some(o) => {
                                let o = o.simplify();
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
        formula::ConstraintExpr::Disj(c1, c2) => {
            let c1 = handle_constraint(c1, eqs, tmp_vars);
            let c2 = handle_constraint(c2, eqs, tmp_vars);
            Constraint::mk_disj(c1, c2)
        }
        formula::ConstraintExpr::True
        | formula::ConstraintExpr::False
        | formula::ConstraintExpr::Pred(_, _)
        | formula::ConstraintExpr::Conj(_, _)
        | formula::ConstraintExpr::Quantifier(_, _, _) => c.clone(),
    }
}

fn app_eqs(g: &Goal, eqs: &Vec<(Ident, Op)>) -> Goal {
    let mut g = g.clone();
    for (x, o) in eqs {
        g = g.isubst(x, o);
    }
    g
}

// main function for the transformation
fn f(g: &Goal, tmp_vars: &mut HashSet<Ident>) -> Goal {
    match g.kind() {
        GoalKind::Constr(_) | GoalKind::Op(_) | GoalKind::Var(_) => g.clone(),
        GoalKind::Abs(x, g) => {
            let g = f(g, tmp_vars);
            Goal::mk_abs(x.clone(), g)
        }
        GoalKind::App(g1, g2) => {
            let g1 = f(g1, tmp_vars);
            let g2 = f(g2, tmp_vars);
            Goal::mk_app(g1, g2)
        }
        GoalKind::Conj(g1, g2) => {
            let g1 = f(g1, tmp_vars);
            let g2 = f(g2, tmp_vars);
            Goal::mk_conj_opt(g1, g2)
        }
        GoalKind::Disj(_, _) => {
            let mut disjs: Vec<_> = g.vec_of_disjs().into_iter().cloned().collect();
            let mut r = Goal::mk_false();
            while let Some(g) = disjs.pop() {
                let g = match g.kind() {
                    GoalKind::Constr(c) => {
                        let mut eqs = Vec::new();
                        let g = handle_constraint(c, &mut eqs, tmp_vars);
                        r = app_eqs(&r, &eqs);
                        disjs.iter_mut().for_each(|g| {
                            *g = app_eqs(g, &eqs);
                        });
                        Goal::mk_constr(g)
                    }
                    _ => g.clone(),
                };
                r = Goal::mk_disj_opt(r, g);
            }
            r
        }
        GoalKind::Univ(x, g) => {
            let flag = tmp_vars.insert(x.id);
            let g = f(g, tmp_vars);
            if !flag {
                tmp_vars.remove(&x.id);
            }
            if g.fv().contains(&x.id) {
                Goal::mk_univ_opt(x.clone(), g)
            } else {
                g
            }
        }
        GoalKind::ITE(c, g1, g2) => {
            let g1 = f(g1, tmp_vars);
            let g2 = f(g2, tmp_vars);
            Goal::mk_ite_opt(c.clone(), g1, g2)
        }
    }
}

impl TypedPreprocessor for RemoveTmpVarTransform {
    const PASS_NAME: &'static str = "remove tmp var";

    fn transform_goal(
        &self,
        goal: &formula::hes::Goal<formula::Constraint>,
        _t: &formula::Type,
        _env: &mut formula::TyEnv,
    ) -> formula::hes::Goal<formula::Constraint> {
        debug!("transform_goal: {goal}");
        let g = f(goal, &mut HashSet::new());
        debug!("translated: {g}");
        g
    }
}

pub fn transform(problem: hes::Problem<formula::Constraint>) -> hes::Problem<formula::Constraint> {
    crate::title!("remove_tmp_vars");
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
