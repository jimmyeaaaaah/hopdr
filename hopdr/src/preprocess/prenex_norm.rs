/// This pass finds the pattern (c \/ g1) /\ (not c \/ g2) and replaces it with ite(not c, g1, g2).
/// For example, a formula ∀x. x != 0 \/ P(x, y) can be translated to P(0, y).
use super::TypedPreprocessor;
use crate::formula::hes::{self, GoalKind};
use crate::formula::{self, Constraint, Logic, QuantifierKind, Type, Variable};

pub struct PrenexNormTransform {}

type Goal = hes::Goal<Constraint>;

fn append_quantifiers(quantifiers: Vec<(QuantifierKind, Variable)>, g: Goal) -> Goal {
    quantifiers.into_iter().rev().fold(g, |g, (q, x)| match q {
        QuantifierKind::Universal => Goal::mk_univ(x, g),
        QuantifierKind::Existential => panic!("program error"),
    })
}

fn conjoin(
    mut v1: Vec<(QuantifierKind, Variable)>,
    mut v2: Vec<(QuantifierKind, Variable)>,
) -> Vec<(QuantifierKind, Variable)> {
    assert!(!v1.iter().any(|(_, x)| v2.iter().any(|(_, y)| x == y)));
    v1.append(&mut v2);
    v1
}

fn f(g: &Goal, mut env: formula::TyEnv) -> (Type, Vec<(QuantifierKind, Variable)>, Goal) {
    debug!("target: {g}");
    match g.kind() {
        GoalKind::Constr(c) => {
            let (v, c) = c.to_pnf_raw();
            (Type::mk_type_int(), v, Goal::mk_constr(c))
        }
        GoalKind::Op(_) => (Type::mk_type_int(), Vec::new(), g.clone()),
        GoalKind::Var(x) => (env.get(x).unwrap().clone(), Vec::new(), g.clone()),
        GoalKind::Abs(x, g) => {
            env.add(x.id.clone(), x.ty.clone());
            let (ty, v, g) = f(g, env);
            let g = append_quantifiers(v, g);
            (
                Type::mk_type_arrow(x.ty.clone(), ty),
                Vec::new(),
                Goal::mk_abs(x.clone(), g),
            )
        }
        GoalKind::App(g1, g2) => {
            let (ty1, v1, g1) = f(g1, env.clone());
            let g1 = append_quantifiers(v1, g1);
            let (_, ty) = ty1.arrow();

            let (_, v2, g2) = f(g2, env.clone());
            let g2 = append_quantifiers(v2, g2);

            (ty.clone(), Vec::new(), Goal::mk_app(g1, g2))
        }
        GoalKind::Univ(x, g) => {
            env.add(x.id, x.ty.clone());
            let (_, mut v, g) = f(g, env);
            v.push((QuantifierKind::Universal, x.clone()));
            (Type::mk_type_prop(), v, g)
        }
        GoalKind::Conj(g1, g2) => {
            let (_, v1, g1) = f(g1, env.clone());
            let (_, v2, g2) = f(g2, env);
            (Type::mk_type_prop(), conjoin(v1, v2), Goal::mk_conj(g1, g2))
        }
        GoalKind::Disj(g1, g2) => {
            let (_, v1, g1) = f(g1, env.clone());
            let (_, v2, g2) = f(g2, env);
            (Type::mk_type_prop(), conjoin(v1, v2), Goal::mk_disj(g1, g2))
        }
        GoalKind::ITE(c, g1, g2) => {
            let (v, c) = c.to_pnf_raw();
            let (_, v1, g1) = f(g1, env.clone());
            let (_, v2, g2) = f(g2, env);
            let v = conjoin(v, conjoin(v1, v2));
            (Type::mk_type_prop(), v, Goal::mk_ite(c.clone(), g1, g2))
        }
    }
}

impl TypedPreprocessor for PrenexNormTransform {
    const PASS_NAME: &'static str = "prenex normal form";

    fn transform_goal(
        &self,
        goal: &formula::hes::Goal<formula::Constraint>,
        _t: &formula::Type,
        env: &mut formula::TyEnv,
    ) -> formula::hes::Goal<formula::Constraint> {
        debug!("transform_goal: {goal}");
        let (_, v, g) = f(goal, env.clone());
        let g = append_quantifiers(v, g);
        debug!("translated: {g}");
        g
    }
}

pub fn transform(problem: hes::Problem<formula::Constraint>) -> hes::Problem<formula::Constraint> {
    crate::title!("prenex norm");
    let t = PrenexNormTransform {};
    t.transform(problem)
}

#[test]
fn test_transform() {
    use crate::formula::{Constraint, Ident, Op, OpKind, Variable};
    use hes::Goal;
    // \forall x. (x < 0 \/ F x) /\ (\forall z. z >= 0 \/ F (0 - z))
    let xi = Ident::fresh();
    let zi = Ident::fresh();
    let x = Op::mk_var(xi);
    let z = Op::mk_var(zi);
    let zero = Op::mk_const(0);
    let func = Ident::fresh();

    let c1 = Constraint::mk_lt(x.clone(), zero.clone());
    let a11 = Goal::mk_constr(c1);
    let a12 = Goal::mk_app(Goal::mk_var(func), Goal::mk_var(xi));

    let c2 = Constraint::mk_geq(x.clone(), zero.clone());
    let a21 = Goal::mk_constr(c2);
    let o = Op::mk_bin_op(OpKind::Sub, zero.clone(), z.clone());
    let a22 = Goal::mk_app(Goal::mk_var(func), Goal::mk_op(o));

    let a1 = Goal::mk_disj(a11.clone(), a12.clone());
    let a2 = Goal::mk_disj(a21.clone(), a22.clone());
    let a2 = Goal::mk_univ(Variable::mk(zi, Type::mk_type_int()), a2);
    let a = Goal::mk_conj(a1, a2);
    let a = Goal::mk_univ(Variable::mk(xi, Type::mk_type_int()), a);

    let mut env = formula::TyEnv::new();
    env.add(
        func,
        Type::mk_type_arrow(Type::mk_type_int(), Type::mk_type_prop()),
    );

    let (_, v, g) = f(&a, env);
    let g = append_quantifiers(v, g);
    println!("{}", g);
}
