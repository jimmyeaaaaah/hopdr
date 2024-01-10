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
    Type as HFLType,
};

type Input = ProblemBase<Constraint, ()>;
type Output = ProblemBase<Constraint, super::Aux>;

// data structure used for inferring mode
type Goal = GoalBase<Constraint, Aux>;
type Clause = ClauseBase<Constraint, Aux>;
type Problem = ProblemBase<Constraint, Aux>;

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
    ClauseBase { head, body }
}

/// translates the given problem to the intermediate representation for mode inference
fn translate_to_problem(problem: Input) -> Problem {
    let mut env = ModeEnv::new();
    for (x, mode) in crate::formula::generate_global_environment(&problem.clauses)
        .to_hash_map()
        .into_iter()
        .map(|(x, y)| (x, Mode::from_hflty(&y)))
    {
        env = env.insert(x, mode)
    }

    let clauses = problem
        .clauses
        .into_iter()
        .map(|c| translate_to_clause(c, env.clone()))
        .collect();
    let top = translate_to_goal(&problem.top, env);
    Problem { clauses, top }
}

//fn template_from_mode(mode: &Mode) -> Mode {
//    match mode.kind() {
//        ModeKind::Prop => Mode::mk_prop(),
//        ModeKind::In => Mode::mk_in(),
//        ModeKind::Out => Mode::mk_out(),
//        ModeKind::Var(_) => Mode::new_var(),
//        ModeKind::Fun(t1, t2) => Mode::mk_fun(template_from_mode(t1), template_from_mode(t2)),
//    }
//}
//
//fn generate_template(c: &Clause) -> Mode {
//
//}

pub(super) fn infer(problem: Input) -> Output {
    let problem = translate_to_problem(problem);

    unimplemented!()
}
