mod alpha;
mod boolean_expand;
pub mod chc;
mod eta;
mod extravar;
mod find_ite;
mod forall_pass;
pub mod hes;
pub mod hfl_preprocessor;
mod ite_expand;
mod prenex_norm;
mod remove_tmp_var;
mod reorder_conj;
mod reorder_disj;
mod safety;
mod simplify_constr_op;
mod transform;
mod typing;
mod unpack_constr;
use crate::formula;
use crate::formula::Type as SimpleType;
use crate::parse;
use hes::ValidityChecking;
use std::collections::HashMap;

type IdentMap = HashMap<parse::Ident, formula::Ident>;
pub struct Context {
    pub ident_map: IdentMap,
    pub inverse_map: HashMap<formula::Ident, parse::Ident>,
    pub original: Option<ValidityChecking<parse::Ident, SimpleType>>,
}

impl Context {
    fn new(ident_map: IdentMap, original: ValidityChecking<parse::Ident, SimpleType>) -> Context {
        let inverse_map = ident_map
            .iter()
            .map(|(x, y)| (y.clone(), x.clone()))
            .collect();
        Context {
            ident_map,
            inverse_map,
            original: Some(original),
        }
    }
    pub fn empty() -> Context {
        Context {
            ident_map: IdentMap::new(),
            inverse_map: HashMap::new(),
            original: None,
        }
    }
}

pub trait TypedPreprocessor {
    const PASS_NAME: &'static str;
    /// API for transforming a goal
    fn transform_goal(
        &self,
        goal: &formula::hes::Goal<formula::Constraint>,
        t: &formula::Type,
        env: &mut formula::TyEnv,
    ) -> formula::hes::Goal<formula::Constraint>;

    fn transform_clause(
        &self,
        clause: formula::hes::Clause<formula::Constraint>,
        env: &mut formula::TyEnv,
    ) -> formula::hes::Clause<formula::Constraint> {
        let body = self.transform_goal(&clause.body, &clause.head.ty, env);
        formula::hes::Clause { body, ..clause }
    }

    /// API for transforming a problem
    fn transform_internal(
        &self,
        problem: formula::hes::Problem<formula::Constraint>,
    ) -> formula::hes::Problem<formula::Constraint> {
        let mut env = formula::generate_global_environment(&problem.clauses);
        let clauses = problem
            .clauses
            .into_iter()
            .map(|c| self.transform_clause(c, &mut env))
            .collect();
        let top = self.transform_goal(&problem.top, &formula::Type::mk_type_prop(), &mut env);
        formula::hes::Problem { top, clauses }
    }

    fn transform(
        &self,
        problem: formula::hes::Problem<formula::Constraint>,
    ) -> formula::hes::Problem<formula::Constraint> {
        info!("preprocessing: {}", Self::PASS_NAME);
        crate::stat::preprocess::start_clock(Self::PASS_NAME);
        let p = self.transform_internal(problem.clone());
        crate::stat::preprocess::end_clock(Self::PASS_NAME);

        if problem != p {
            info!("{}", problem);
            info!("translated result: ");
            info!("{}", p);
        }
        p
    }
}
