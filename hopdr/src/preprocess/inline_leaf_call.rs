use super::TypedPreprocessor;
use crate::formula::hes::{self, GoalKind, Problem};
use crate::formula::{self, Constraint, TyEnv, Type};

pub struct InlineLeafCallTransform {
    pub original: Problem<Constraint>,
}

type Goal = hes::Goal<formula::Constraint>;

impl<'a> InlineLeafCallTransform {
    fn handle_app(&self, goal: &Goal) -> Goal {
        let old = &goal;
        let mut pred = goal.clone();
        let mut args = Vec::new();
        loop {
            match pred.kind() {
                GoalKind::App(g1, g2) => {
                    args.push(self.f(g2));
                    pred = self.f(g1);
                }
                _ => {
                    break;
                }
            }
        }
        match pred.kind() {
            GoalKind::Var(x) => {
                if let Some(c) = self.original.get_clause(x) {
                    if c.head.ty.arity() == args.len() {
                        // app args to pred
                        let mut pred = c.body.clone();
                        for arg in args.iter().rev() {
                            pred = Goal::mk_app(pred, arg.clone());
                        }
                        // if the result was trivial, then return the result
                        let pred = pred.simplify();
                        if pred.is_false() || pred.is_true() || pred.is_constr() {
                            debug!("simplified by inline leaf call: {old} -> {pred}");
                            return pred;
                        }
                    }
                }
            }
            _ => (),
        }
        for arg in args.iter().rev() {
            pred = Goal::mk_app(pred, arg.clone());
        }
        pred
    }
    fn f(&self, goal: &Goal) -> Goal {
        match goal.kind() {
            GoalKind::Constr(_) | GoalKind::Op(_) | GoalKind::Var(_) => goal.clone(),
            GoalKind::Abs(x, g) => {
                let g = self.f(g);
                Goal::mk_abs(x.clone(), g)
            }
            GoalKind::App(_, _) => self.handle_app(goal),
            GoalKind::Conj(g1, g2) => {
                let g1 = self.f(g1);
                let g2 = self.f(g2);
                Goal::mk_conj_opt(g1, g2)
            }
            GoalKind::Disj(g1, g2) => {
                let g1 = self.f(g1);
                let g2 = self.f(g2);
                Goal::mk_disj_opt(g1, g2)
            }
            GoalKind::Univ(x, g) => {
                let g = self.f(g);
                Goal::mk_univ_opt(x.clone(), g)
            }
            GoalKind::ITE(c, g1, g2) => {
                let g1 = self.f(g1);
                let g2 = self.f(g2);
                Goal::mk_ite_opt(c.clone(), g1, g2)
            }
        }
    }
}

impl TypedPreprocessor for InlineLeafCallTransform {
    const PASS_NAME: &'static str = "inline leaf call";

    fn transform_goal(&self, goal: &Goal, _t: &Type, _env: &mut TyEnv) -> Goal {
        debug!("transform_goal: {}", goal);
        self.f(goal)
    }
}

pub fn transform(problem: hes::Problem<formula::Constraint>) -> hes::Problem<formula::Constraint> {
    debug!("inline leaf call transform");
    let t = InlineLeafCallTransform {
        original: problem.clone(),
    };
    t.transform(problem)
}

#[test]
fn test_inline_leaf_call() {
    use crate::formula::hes::*;
    use crate::formula::*;
    // F x y = y != 0 /\ (F (x - 1) 0 \/ F (x - 1) y)
    let x = Ident::fresh();
    let y = Ident::fresh();
    let f = Ident::fresh();

    let f_ty = Type::mk_type_arrow(
        Type::mk_type_int(),
        Type::mk_type_arrow(Type::mk_type_int(), Type::mk_type_prop()),
    );
    let fv = Variable::mk(f.clone(), f_ty.clone());
    let x_ty = Type::mk_type_int();
    let xv = Variable::mk(x.clone(), x_ty.clone());
    let y_ty = Type::mk_type_int();
    let yv = Variable::mk(y.clone(), y_ty.clone());
    let c1 = Constraint::mk_neq(Op::mk_var(y.clone()), Op::zero());
    let g0 = Goal::mk_constr(c1);
    let g2 = Goal::mk_app(
        Goal::mk_app(
            Goal::mk_var(f.clone()),
            Goal::mk_op(Op::mk_sub(Op::mk_var(x.clone()), Op::one())),
        ),
        Goal::mk_var(y.clone()),
    );
    let g1 = Goal::mk_app(
        Goal::mk_app(
            Goal::mk_var(f.clone()),
            Goal::mk_op(Op::mk_sub(Op::mk_var(x.clone()), Op::one())),
        ),
        Goal::mk_op(Op::zero()),
    );
    let g3 = Goal::mk_disj(g1, g2.clone());
    let g = Goal::mk_conj(g0, g3);
    let g = Goal::mk_abs(xv, Goal::mk_abs(yv, g));
    let c = Clause { head: fv, body: g };
    let problem = Problem {
        top: Goal::mk_true(),
        clauses: vec![c],
    };
    println!("{problem}");
    let problem = transform(problem);
    let c = &problem.clauses[0];
    let g = c.body.abs().1.abs().1.conj().1;
    println!("{problem}");
    assert_eq!(g, &g2);
}
