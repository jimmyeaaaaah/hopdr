// eta transformation

use super::TypedPreprocessor;
use crate::formula;
use crate::formula::hes;
use crate::formula::Logic;

struct EtaTransform {}

impl TypedPreprocessor for EtaTransform {
    fn transform_goal(
        &self,
        goal: &hes::Goal<formula::Constraint>,
        t: &formula::Type,
        env: &mut formula::TyEnv,
    ) -> hes::Goal<formula::Constraint> {
        use formula::Op;
        use hes::GoalKind;

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
                    let t = env.get(x).unwrap_or_else(|| panic!("cannot find {}", x));
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
                    let g2 = translate(g2, s, env);
                    (t.clone(), Goal::mk_app(g1, g2))
                }
            }
        }

        fn append_args(g: Goal, t: &formula::Type) -> Goal {
            match t.kind() {
                formula::TypeKind::Proposition | formula::TypeKind::Integer => g,
                formula::TypeKind::Arrow(s, t) => {
                    let x = formula::Ident::fresh();
                    let arg = match s.kind() {
                        formula::TypeKind::Integer => Goal::mk_op(Op::mk_var(x)),
                        formula::TypeKind::Proposition | formula::TypeKind::Arrow(_, _) => {
                            Goal::mk_var(x)
                        }
                    };
                    let g = Goal::mk_app(g, arg);
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
                    env.add(x.id, x.ty.clone());
                    let g = translate(g, t, env);
                    env.del(&x.id);
                    Goal::mk_abs(x.clone(), g)
                }
                GoalKind::App(g1, g2) => {
                    let (s, g1) = handle_abs(g1, env);
                    let g2 = match s.kind() {
                        formula::TypeKind::Arrow(t1, _) => translate(g2, t1, env),
                        formula::TypeKind::Proposition | formula::TypeKind::Integer => {
                            panic!("program error")
                        }
                    };
                    let g_app = Goal::mk_app(g1, g2);
                    append_args(g_app, t)
                }
                GoalKind::Univ(x, g) => Goal::mk_univ(x.clone(), translate(g, t, env)),
                GoalKind::Conj(g1, g2) => {
                    Goal::mk_conj(translate(g1, t, env), translate(g2, t, env))
                }
                GoalKind::Disj(g1, g2) => {
                    Goal::mk_disj(translate(g1, t, env), translate(g2, t, env))
                }
            }
        }
        translate(goal, t, env)
    }
}

pub fn transform(problem: hes::Problem<formula::Constraint>) -> hes::Problem<formula::Constraint> {
    let t = EtaTransform {};
    t.transform(problem)
}

#[test]
fn test_transform() {
    use crate::parse::parse;
    use crate::preprocess;
    use nom::error::VerboseError;

    let s = "
    %HES
    S =v S2 n.
    S2 z =v F z (H z).
    F x g =v g (x+1).
    H z y =v y > z.";
    let (_, f) = parse::<VerboseError<&str>>(s).unwrap();
    // FIXME: hes::preprocess contains eta's path, and it's inevitable currently;
    // therefore, checking if hes::preprocess succeeds is the current check of this test..
    let (_vc, _ctx) = preprocess::hes::preprocess(f);
    // println!("before: {vc}");
    // let vc_old = vc.clone();
    // let h = transform(vc);
    // println!("{h}");
    // let s2 = ctx
    //     .ident_map
    //     .get(&parse::Ident::new("S2".to_string()))
    //     .unwrap();
    // assert_ne!(
    //     &h.get_clause(s2).unwrap().body,
    //     &vc_old.get_clause(s2).unwrap().body
    // )
}
