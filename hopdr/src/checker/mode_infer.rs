/// Mode inference
/// Algorithm
/// 1. First set all the integer variables as `in`
/// 2. Then, for each clause, tries to infer a better mode so that we can remove
/// the temporary variable introduced by universal quantifiers
use super::mode::*;
use super::Aux;
use super::ProblemM;

use crate::formula::hes::{ClauseBase, GoalBase, GoalKind, ProblemBase};
use crate::formula::{
    generate_global_environment, Constraint, Fv, Ident, Logic, Negation, Op, PredKind, TyEnv,
    Type as HFLType, Variable,
};

use std::collections::HashMap;

type Input = ProblemBase<Constraint, ()>;
type Output = ProblemBase<Constraint, super::Aux>;

// data structure used for inferring mode
type Goal = GoalBase<Constraint, Aux>;

struct Clause {
    head: Variable,
    mode: Mode,
    body: Goal,
}
struct Problem {
    clauses: Vec<Clause>,
    top: Goal,
}

fn translate_to_goal(goal: &GoalBase<Constraint, ()>, env: ModeEnv) -> Goal {
    match goal.kind() {
        GoalKind::Constr(c) => GoalBase::mk_constr_t(c.clone(), Aux::mk_prop(env.clone())),
        GoalKind::Op(x) => GoalBase::mk_op_t(x.clone(), Aux::new(env.clone(), Mode::mk_in())),

        GoalKind::Var(x) => {
            let mode = env.get(x).unwrap();
            GoalBase::mk_var_t(x.clone(), Aux::new(env.clone(), mode.clone()))
        }
        GoalKind::Abs(v, g) => {
            let mode = Mode::from_hflty(&v.ty);
            let g = translate_to_goal(g, env.insert(v.id, mode.clone()));
            let ret_mode = g.aux.mode.clone();

            let abs_mode = Mode::mk_fun(mode.clone(), ret_mode);
            GoalBase::mk_abs_t(v.clone(), g, Aux::new(env.clone(), abs_mode.clone()))
        }
        GoalKind::App(g1, g2) => {
            let g1 = translate_to_goal(g1, env.clone());
            let g2 = translate_to_goal(g2, env.clone());
            let ret_mode = g1.aux.mode.is_fun().1.clone();
            GoalBase::mk_app_t(g1, g2, Aux::new(env.clone(), ret_mode))
        }
        GoalKind::Conj(g1, g2) => {
            let g1 = translate_to_goal(g1, env.clone());
            let g2 = translate_to_goal(g2, env.clone());
            GoalBase::mk_conj_t(g1, g2, Aux::mk_prop(env.clone()))
        }
        GoalKind::Disj(g1, g2) => {
            let g1 = translate_to_goal(g1, env.clone());
            let g2 = translate_to_goal(g2, env.clone());
            GoalBase::mk_disj_t(g1, g2, Aux::new_disj(env.clone()))
        }
        GoalKind::Univ(x, g) => {
            let mode = Mode::from_hflty(&x.ty);
            let g = translate_to_goal(g, env.insert(x.id, mode.clone()));
            GoalBase::mk_univ_t(x.clone(), g, Aux::new_univ(env.clone(), mode))
        }
        GoalKind::ITE(c, g1, g2) => {
            let g1 = translate_to_goal(g1, env.clone());
            let g2 = translate_to_goal(g2, env.clone());
            GoalBase::mk_ite_t(c.clone(), g1, g2, Aux::mk_prop(env.clone()))
        }
    }
}

fn translate_to_clause(clause: ClauseBase<Constraint, ()>, env: ModeEnv) -> Clause {
    let ClauseBase { head, body } = clause;
    let body = translate_to_goal(&body, env.clone());
    let mode = Mode::from_hflty(&head.ty);
    Clause { head, mode, body }
}

/// translates the given problem to the intermediate representation for mode inference
fn translate_to_problem(problem: Input) -> Problem {
    let mut env = ModeEnv::new();
    let env: ModeEnv = crate::formula::generate_global_environment(&problem.clauses)
        .to_hash_map()
        .into_iter()
        .map(|(x, y)| (x, Mode::from_hflty(&y)))
        .collect();

    let clauses = problem
        .clauses
        .into_iter()
        .map(|c| translate_to_clause(c, env.clone()))
        .collect();
    let top = translate_to_goal(&problem.top, env);
    Problem { clauses, top }
}

fn output_problem(problem: Problem) -> Output {
    let Problem { clauses, top } = problem;
    let clauses = clauses
        .into_iter()
        .map(|c| ClauseBase {
            head: c.head,
            body: c.body,
        })
        .collect();
    ProblemBase { clauses, top }
}

fn template_from_mode(mode: &Mode) -> Mode {
    match mode.kind() {
        ModeKind::Prop => Mode::mk_prop(),
        ModeKind::In | ModeKind::Out | ModeKind::Var(_) => Mode::new_var(),
        ModeKind::Fun(t1, t2) => Mode::mk_fun(template_from_mode(t1), template_from_mode(t2)),
        _ => panic!("program error: {}", mode),
    }
}

fn handle_op(o: &Op, env: ModeEnv) -> Mode {
    match o.kind() {
        crate::formula::OpExpr::Var(x) => env.get(x).unwrap().clone(),
        _ => Mode::mk_in(),
    }
}

pub struct ModeConstraint {
    left: Op,
    right: Op,
}

impl std::fmt::Display for ModeConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.left, self.right)
    }
}

impl ModeConstraint {
    fn new(left: Op, right: Op) -> Self {
        Self { left, right }
    }
    fn mode_in(x: Ident) -> Self {
        Self::new(Op::mk_var(x), Op::zero())
    }
}

fn gen_op_template(o: &Op, env: ModeEnv, constraints: &mut Vec<ModeConstraint>) -> Mode {
    match o.kind() {
        crate::formula::OpExpr::Var(x) => env.get(x).unwrap().clone(),
        crate::formula::OpExpr::Const(_) => Mode::mk_in(),
        _ => {
            for v in o.fv() {
                constraints.push(ModeConstraint::mode_in(v.clone()));
            }
            Mode::mk_in()
        }
    }
}

/// aux function for handling disjunction case
fn gen_new_env(g: &Goal, env: &ModeEnv) -> ModeEnv {
    let fv = g.fv();
    let env: ModeEnv = env
        .iter()
        .filter(|(x, _)| fv.contains(x))
        .map(|(x, m)| (*x, template_from_mode(m)))
        .collect();
    env
}

fn mode_to_op(mode: &Mode) -> Op {
    match mode.kind() {
        ModeKind::In => Op::zero(),
        ModeKind::Out => Op::one(),
        ModeKind::Prop | ModeKind::Fun(_, _) | ModeKind::InOut => panic!("program error: {}", mode),
        ModeKind::Var(x) => Op::mk_var(*x),
    }
}

fn gen_template_goal(
    g: &Goal,
    env: ModeEnv,
    constraints: &mut Vec<ModeConstraint>,
    coarse: bool,
) -> Goal {
    let f = |mode| Aux::new(env.clone(), mode);
    match g.kind() {
        GoalKind::Constr(c) => GoalBase::mk_constr_t(c.clone(), f(Mode::mk_prop())),
        GoalKind::Op(x) => {
            let mode = gen_op_template(x, env.clone(), constraints);
            GoalBase::mk_op_t(x.clone(), f(mode))
        }
        GoalKind::Var(x) => {
            let mode = env.get(x).unwrap().clone();
            GoalBase::mk_var_t(x.clone(), f(mode))
        }
        GoalKind::Abs(v, g) => {
            let mode = Mode::from_hflty(&v.ty);
            let g = gen_template_goal(g, env.insert(v.id, mode.clone()), constraints, coarse);
            let ret_mode = g.aux.mode.clone();

            let abs_mode = Mode::mk_fun(mode.clone(), ret_mode);
            GoalBase::mk_abs_t(v.clone(), g, f(abs_mode))
        }
        GoalKind::App(g1, g2) => {
            let g1 = gen_template_goal(g1, env.clone(), constraints, coarse);
            let g2 = gen_template_goal(g2, env.clone(), constraints, coarse);
            let ret_mode = g1.aux.mode.is_fun().1.clone();
            GoalBase::mk_app_t(g1, g2, f(ret_mode))
        }
        GoalKind::Conj(g1, g2) => {
            let g1 = gen_template_goal(g1, env.clone(), constraints, coarse);
            let g2 = gen_template_goal(g2, env.clone(), constraints, coarse);
            GoalBase::mk_conj_t(g1, g2, f(Mode::mk_prop()))
        }
        GoalKind::Disj(g1, g2) => {
            // 1. introduce a new variable
            let g1_env = gen_new_env(g1, &env);
            let g2_env = gen_new_env(g2, &env);
            // 2. add a constraint
            for (x, m) in env.iter() {
                if matches!(m.kind(), ModeKind::Fun(_, _)) {
                    continue;
                }
                let lhs = mode_to_op(m);
                match (g1_env.get(x), g2_env.get(x)) {
                    (Some(m1), Some(m2)) => {
                        let o1 = mode_to_op(m1);
                        let o2 = mode_to_op(m2);
                        let rhs = Op::mk_add(o1, o2);
                        constraints.push(ModeConstraint::new(lhs, rhs));
                    }
                    (Some(m), None) | (None, Some(m)) => {
                        let rhs = mode_to_op(m);
                        constraints.push(ModeConstraint::new(lhs, rhs));
                    }
                    (None, None) => {}
                }
            }
            let g1 = gen_template_goal(g1, g1_env.clone(), constraints, coarse);
            let g2 = gen_template_goal(g2, g2_env.clone(), constraints, coarse);
            GoalBase::mk_disj_t(g1, g2, f(Mode::mk_prop()))
        }
        GoalKind::Univ(x, g) => {
            let mode = if coarse {
                Mode::mk_out()
            } else {
                Mode::from_hflty(&x.ty)
            };
            let g = gen_template_goal(g, env.insert(x.id, mode.clone()), constraints, coarse);
            GoalBase::mk_univ_t(x.clone(), g, f(mode))
        }
        GoalKind::ITE(c, g1, g2) => {
            let g1 = gen_template_goal(g1, env.clone(), constraints, coarse);
            let g2 = gen_template_goal(g2, env.clone(), constraints, coarse);
            GoalBase::mk_ite_t(c.clone(), g1, g2, f(Mode::mk_prop()))
        }
    }
}

fn gen_template_clause(
    c: &Clause,
    env: ModeEnv,
    mode: Mode,
    constraints: &mut Vec<ModeConstraint>,
    coarse: bool,
) -> Clause {
    let Clause {
        head,
        body,
        mode: _,
    } = c;
    let body = gen_template_goal(body, env, constraints, coarse);
    Clause {
        head: head.clone(),
        body,
        mode,
    }
}

fn gen_template_problem(p: &Problem, target: Ident) -> (Problem, Vec<ModeConstraint>) {
    let env: ModeEnv = p
        .clauses
        .iter()
        .map(|c| (c.head.id, template_from_mode(&c.mode)))
        .collect();
    let mut constraints = Vec::new();
    let clauses = p
        .clauses
        .iter()
        .map(|c| {
            gen_template_clause(
                c,
                env.clone(),
                env.get(&c.head.id).unwrap().clone(),
                &mut constraints,
                target == c.head.id,
            )
        })
        .collect();
    let top = gen_template_goal(&p.top, env, &mut constraints, false);
    (Problem { clauses, top }, constraints)
}

fn solve(constraint: Vec<ModeConstraint>) -> Option<HashMap<Ident, Mode>> {
    unimplemented!()
}

fn apply_model(problem: Problem, model: HashMap<Ident, Mode>) -> Problem {
    unimplemented!()
}

// 1. pick a clause
// 2. set all the univ variables' mode as var
// 3. gen templates for all the clauses

pub(super) fn infer(problem: Input) -> Output {
    let clause_names: Vec<Ident> = problem
        .clauses
        .iter()
        .map(|c| c.head.id)
        .into_iter()
        .collect();
    let mut problem = translate_to_problem(problem);
    for name in clause_names {
        let (new_problem, constraint) = gen_template_problem(&problem, name);
        match solve(constraint) {
            Some(model) => {
                problem = apply_model(new_problem, model);
            }
            None => {}
        }
    }
    output_problem(problem)
}

#[test]
fn test_generate_template() {
    // P = \x. \y. ∀w. (x < 101 \/ y != x - 10) /\ (x >= 101 \/ (P (x+11) w \/ P w y)).
    use crate::formula::hes::Goal as G;

    // clause P
    let x = Ident::fresh();
    let y = Ident::fresh();
    let w = Ident::fresh();
    let p = Ident::fresh();
    let c = Constraint::mk_geq(Op::mk_var(x), Op::mk_const(101));
    let c2 = Constraint::mk_neq(Op::mk_var(x), Op::mk_sub(Op::mk_var(x), Op::mk_const(10)));
    let g1 = G::mk_app(
        G::mk_app(
            G::mk_var(p),
            G::mk_op(Op::mk_add(Op::mk_var(x), Op::mk_const(11))),
        ),
        G::mk_var(w),
    );
    let g2 = G::mk_app(G::mk_app(G::mk_var(p), G::mk_var(w)), G::mk_var(y));
    let g3 = G::mk_disj(g1, g2);
    let g4 = G::mk_ite(c, G::mk_constr(c2), g3);
    let g = G::mk_univ(Variable::mk(w, HFLType::mk_type_int()), g4);
    let g = G::mk_abs(
        Variable::mk(x, HFLType::mk_type_int()),
        G::mk_abs(Variable::mk(y, HFLType::mk_type_int()), g),
    );
    let clause = ClauseBase {
        head: Variable::mk(
            p,
            HFLType::mk_type_arrow(
                HFLType::mk_type_int(),
                HFLType::mk_type_arrow(HFLType::mk_type_int(), HFLType::mk_type_prop()),
            ),
        ),
        body: g,
    };

    // top: ∀x. ∀y. x = 91 \/ y > 101 \/ P y x.

    let x = Ident::fresh();
    let y = Ident::fresh();
    let c = Constraint::mk_eq(Op::mk_var(x), Op::mk_const(91));
    let c2 = Constraint::mk_gt(Op::mk_var(y), Op::mk_const(101));
    let g1 = G::mk_app(G::mk_app(G::mk_var(p), G::mk_var(y)), G::mk_var(x));
    let g2 = G::mk_disj(G::mk_constr(c), G::mk_constr(c2));
    let top = G::mk_univ(
        Variable::mk(x, HFLType::mk_type_int()),
        G::mk_univ(Variable::mk(y, HFLType::mk_type_int()), G::mk_disj(g1, g2)),
    );

    let problem = ProblemBase {
        clauses: vec![clause],
        top,
    };

    let problem = translate_to_problem(problem);
    let (new_problem, constraint) = gen_template_problem(&problem, p);
    for c in constraint {
        println!("{c}");
    }
}
