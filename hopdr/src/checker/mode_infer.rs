/// Mode inference
/// Algorithm
/// 1. First set all the integer variables as `in`
/// 2. Then, for each clause, tries to infer a better mode so that we can remove
/// the temporary variable introduced by universal quantifiers
use super::mode::*;
use super::ProblemM;

use crate::formula::hes::{ClauseBase, GoalBase, GoalKind, ProblemBase};
use crate::formula::{
    generate_global_environment, Constraint, Fv, Ident, Logic, Negation, Op, PredKind, TyEnv,
    Type as HFLType,
};
use crate::util::P;

use std::collections::HashMap;

type Input = ProblemBase<Constraint, ()>;
type Output = ProblemBase<Constraint, super::Aux>;

#[derive(Clone, Debug)]
struct Aux {
    mode: Mode,
    // used for handling mode for variable introduced by universal quantifiers
    univ_introduced: Option<Mode>,
}

impl Aux {
    fn new(mode: Mode) -> Self {
        Self {
            mode,
            univ_introduced: None,
        }
    }
    fn new_univ() -> Self {
        Self {
            mode: Mode::mk_prop(),
            univ_introduced: Some(Mode::new_var()),
        }
    }
    fn mk_prop() -> Self {
        Self::new(Mode::mk_prop())
    }
}

// data structure used for inferring mode
type Goal = GoalBase<Constraint, Aux>;
type Clause = ClauseBase<Constraint, Aux>;
type Problem = ProblemBase<Constraint, Aux>;

fn translate_to_goal(
    goal: &GoalBase<Constraint, ()>,
    env: &mut HashMap<Ident, HFLType>,
) -> (Goal, HFLType) {
    match goal.kind() {
        GoalKind::Constr(c) => (
            GoalBase::mk_constr_t(c.clone(), Aux::mk_prop()),
            HFLType::mk_type_prop(),
        ),
        GoalKind::Op(x) => (
            GoalBase::mk_op_t(x.clone(), Aux::mk_prop()),
            HFLType::mk_type_int(),
        ),
        GoalKind::Var(x) => {
            let ty = env.get(x).unwrap();
            let mode = Mode::from_hflty(ty);
            (GoalBase::mk_var_t(x.clone(), Aux::new(mode)), ty.clone())
        }
        GoalKind::Abs(v, g) => {
            let old = env.insert(v.id, v.ty.clone());
            let (g, ret_ty) = translate_to_goal(g, env);
            match old {
                Some(ty) => {
                    env.insert(v.id, ty);
                }
                None => {
                    env.remove(&v.id);
                }
            }
            let mode = Mode::from_hflty(&v.ty);
            (
                GoalBase::mk_abs_t(v.clone(), g, Aux::new(mode)),
                HFLType::mk_type_arrow(v.ty.clone(), ret_ty),
            )
        }
        GoalKind::App(g1, g2) => {
            let (g1, pred_ty) = translate_to_goal(g1, env);
            let (g2, _) = translate_to_goal(g2, env);
            let ret_ty = pred_ty.arrow().1;
            let mode = Mode::from_hflty(ret_ty);
            (GoalBase::mk_app_t(g1, g2, Aux::new(mode)), ret_ty.clone())
        }
        GoalKind::Conj(g1, g2) => {
            let (g1, _) = translate_to_goal(g1, env);
            let (g2, _) = translate_to_goal(g2, env);
            (
                GoalBase::mk_conj_t(g1, g2, Aux::mk_prop()),
                HFLType::mk_type_prop(),
            )
        }
        GoalKind::Disj(g1, g2) => {
            let (g1, _) = translate_to_goal(g1, env);
            let (g2, _) = translate_to_goal(g2, env);
            (
                GoalBase::mk_disj_t(g1, g2, Aux::mk_prop()),
                HFLType::mk_type_prop(),
            )
        }
        GoalKind::Univ(x, g) => {
            let old = env.insert(x.id, x.ty.clone());
            let (g, _) = translate_to_goal(g, env);
            match old {
                Some(ty) => {
                    env.insert(x.id, ty);
                }
                None => {
                    env.remove(&x.id);
                }
            }
            let mode = Mode::from_hflty(&x.ty);
            (
                GoalBase::mk_univ_t(x.clone(), g, Aux::new_univ()),
                HFLType::mk_type_prop(),
            )
        }
        GoalKind::ITE(c, g1, g2) => {
            let (g1, _) = translate_to_goal(g1, env);
            let (g2, _) = translate_to_goal(g2, env);
            (
                GoalBase::mk_ite_t(c.clone(), g1, g2, Aux::mk_prop()),
                HFLType::mk_type_prop(),
            )
        }
    }
}

fn translate_to_clause(
    clause: ClauseBase<Constraint, ()>,
    env: &mut HashMap<Ident, HFLType>,
) -> Clause {
    let ClauseBase { head, body } = clause;
    let (body, _) = translate_to_goal(&body, env);
    ClauseBase { head, body }
}

/// translates the given problem to the intermediate representation for mode inference
fn translate_to_problem(problem: Input) -> Problem {
    let mut env = crate::formula::generate_global_environment(&problem.clauses).to_hash_map();
    let clauses = problem
        .clauses
        .into_iter()
        .map(|c| translate_to_clause(c, &mut env))
        .collect();
    let (top, _) = translate_to_goal(&problem.top, &mut env);
    Problem { clauses, top }
}

pub(super) fn infer(problem: Input) -> Output {
    let problem = translate_to_problem(problem);
    unimplemented!()
}
