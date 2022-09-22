// eta transformation

use crate::formula;
use crate::formula::hes;

fn transform_goal(
    goal: &hes::Goal<formula::Constraint>,
    t: &formula::Type,
    env: &mut formula::TyEnv,
) -> hes::Goal<formula::Constraint> {
    use hes::GoalKind;
    let f = translate;

    type Goal = hes::Goal<formula::Constraint>;
    use formula::{TyEnv, Type};

    fn handle_abs(g: &Goal, env: &mut TyEnv) -> (Type, Goal) {
        match g.kind() {
            GoalKind::Constr(_) => (Type::mk_type_prop(), g.clone()),
            GoalKind::Op(_) => (Type::mk_type_int(), g.clone()),
            GoalKind::Conj(g1, g2) => {
                let t = &Type::mk_type_prop();
                let g1 = translate(g1, t, env);
                let g2 = translate(g2, t, env);
                (Type::mk_type_prop(), Goal::mk_conj(g1, g2))
            }
            GoalKind::Disj(g1, g2) => {
                let t = &Type::mk_type_prop();
                let g1 = translate(g1, t, env);
                let g2 = translate(g2, t, env);
                (Type::mk_type_prop(), Goal::mk_disj(g1, g2))
            }
            GoalKind::Univ(x, g) => {
                env.add(x.id, x.ty.clone());
                let g = translate(g, &Type::mk_type_prop(), env);
                env.del(&x.id);
                (Type::mk_type_prop(), Goal::mk_univ(x.clone(), g))
            }
            GoalKind::Var(x) => {
                let t = env.get(x).unwrap();
                (t, g.clone())
            }
            GoalKind::Abs(x, g) => {
                env.add(x.id, x.ty.clone());
                let (t, g) = handle_abs(g, env);
                env.del(&x.id);
                (
                    Type::mk_type_arrow(x.ty.clone(), t),
                    Goal::mk_abs(x.clone(), g),
                )
            }
            GoalKind::App(g1, g2) => {
                let (t, g1) = handle_abs(g1, env);
                let (s, t) = match t.kind() {
                    formula::TypeKind::Arrow(s, t) => (s, t),
                    formula::TypeKind::Proposition | formula::TypeKind::Integer => {
                        panic!("program error")
                    }
                };
                let g2 = translate(g2, t, env);
                (t.clone(), Goal::mk_app(g1, g2))
            }
        }
    }

    fn append_args(g: Goal, t: &formula::Type) -> Goal {
        match t.kind() {
            formula::TypeKind::Proposition | formula::TypeKind::Integer => g,
            formula::TypeKind::Arrow(s, t) => {
                let x = formula::Ident::fresh();
                let g = Goal::mk_app(g, Goal::mk_var(x));
                let g = append_args(g, t);
                let v = formula::Variable::mk(x, s.clone());
                Goal::mk_abs(v, g)
            }
        }
    }

    fn translate(goal: &Goal, t: &formula::Type, env: &mut TyEnv) -> Goal {
        match goal.kind() {
            GoalKind::Constr(_) | hes::GoalKind::Op(_) | GoalKind::Var(_) => goal.clone(),
            GoalKind::Abs(x, g) => {
                let t = match t.kind() {
                    formula::TypeKind::Arrow(_, t) => t,
                    _ => panic!("program error"),
                };
                Goal::mk_abs(x.clone(), translate(g, t, env))
            }
            GoalKind::App(g1, g2) => {
                let (s, g1) = handle_abs(g1, env);
                let g2 = match t.kind() {
                    formula::TypeKind::Arrow(t, _) => translate(g2, &s, env),
                    formula::TypeKind::Proposition | formula::TypeKind::Integer => todo!(),
                };
                let g_app = Goal::mk_app(g1, g2);
                append_args(g_app, &s)
            }
            GoalKind::Univ(x, g) => Goal::mk_univ(x.clone(), translate(g, t, env)),
            GoalKind::Conj(g1, g2) => Goal::mk_conj(translate(g1, t, env), translate(g2, t, env)),
            GoalKind::Disj(g1, g2) => Goal::mk_disj(translate(g1, t, env), translate(g2, t, env)),
        }
    }
    translate(goal, t, env)
}

fn transform_clause(
    clause: hes::Clause<formula::Constraint>,
    env: &mut formula::TyEnv,
) -> hes::Clause<formula::Constraint> {
    let body = transform_goal(&clause.body, &clause.head.ty, env);
    hes::Clause { body, ..clause }
}

pub fn transform(problem: hes::Problem<formula::Constraint>) -> hes::Problem<formula::Constraint> {
    let mut env = formula::generate_global_environment(&problem.clauses);
    let clauses = problem
        .clauses
        .into_iter()
        .map(|c| transform_clause(c, &mut env))
        .collect();
    let top = transform_goal(&problem.top, &formula::Type::mk_type_prop(), &mut env);
    hes::Problem { top, clauses }
}
