use super::fml;
use super::fml::{env_models_constraint, Env};
use super::rtype::{Tau, TyEnv, TypeEnvironment};
use crate::formula;
use crate::formula::hes::{Goal, Problem as ProblemBase};
use crate::formula::{fofml, Ident, Logic, Op};
use crate::util::P;

use std::collections::HashSet;
use std::fmt;

type Problem = ProblemBase<fofml::Atom>;
type Candidate = Goal<fofml::Atom>;
type TemplateType = Tau<fofml::Atom>;
type TemplateEnv = TypeEnvironment<TemplateType>;

enum TypeKind {
    Proposition,
    IArrow(Type), // int -> τ
    Arrow(Vec<Type>, Type),
}
type Type = P<TypeKind>;
type ITEnv = TypeEnvironment<Type>;

// impls for Type

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TypeKind::Proposition => write!(f, "bool"),
            TypeKind::IArrow(t) => write!(f, "integer -> {}", t),
            TypeKind::Arrow(v, y) => {
                write!(f, "(")?;
                if v.len() == 0 {
                    write!(f, "T")?;
                } else {
                    write!(f, "{}", v[0])?;
                    for t in &v[1..] {
                        write!(f, "/\\ {}", t)?;
                    }
                }
                write!(f, " -> {})", y)
            }
        }
    }
}

impl Type {
    fn mk_prop() -> Type {
        Type::new(TypeKind::Proposition)
    }
    fn mk_iarrow(t: Type) -> Type {
        Type::new(TypeKind::IArrow(t))
    }
    fn mk_arrow(ts: Vec<Type>, t2: Type) -> Type {
        Type::new(TypeKind::Arrow(ts, t2))
    }
    fn generate_template(&self, env: &mut HashSet<Ident>) -> TemplateType {
        match self.kind() {
            TypeKind::Proposition => {
                let args: Vec<Op> = env.iter().map(|x| x.clone().into()).collect();
                let p = fofml::Atom::mk_fresh_pred(args);
                TemplateType::mk_prop_ty(p)
            }
            TypeKind::IArrow(t) => {
                let arg = Ident::fresh();
                let not_already_exists = env.insert(arg);
                debug_assert!(not_already_exists);
                let t = t.generate_template(env);
                let exists = env.remove(&arg);
                debug_assert!(exists);
                TemplateType::mk_iarrow(arg, t)
            }
            TypeKind::Arrow(xs, y) => {
                let v = xs.iter().map(|t| t.generate_template(env)).collect();
                let t = y.generate_template(env);
                TemplateType::mk_arrow(v, t)
            }
        }
    }
}

impl From<formula::Type> for Type {
    fn from(t: formula::Type) -> Self {
        match t.kind() {
            formula::TypeKind::Proposition => Type::mk_prop(),
            // integers are handled in Arrow(Integer, ...)
            formula::TypeKind::Integer => panic!("program errror"),
            formula::TypeKind::Arrow(t1, t2) => match t1.kind() {
                formula::TypeKind::Integer => Type::mk_iarrow(t2.clone().into()),
                formula::TypeKind::Proposition | formula::TypeKind::Arrow(_, _) => {
                    Type::mk_arrow(vec![t1.clone().into()], t2.clone().into())
                }
            },
        }
    }
}

// impls for ITEnv

impl ITEnv {
    fn generate_template(&self) -> TemplateEnv {
        let mut env = TemplateEnv::new();
        for (k, ts) in self.map.iter() {
            for t in ts {
                let mut set = HashSet::new();
                env.add(*k, t.generate_template(&mut set));
            }
        }
        env
    }
}

fn infer_intersection(problem: &Problem, _cex: &Candidate) -> ITEnv {
    // TODO: variable expansion
    // The current method is an approximation of the actual intersection type
    // just by counting the occurrence of each higher-order predicate

    // 1. first check the order.
    // if the order is less than 3, intersection types are not required, so just
    // returns the intersection type equivalent to the simple type for problem
    if problem.order() < 3 {
        let mut env = ITEnv::new();
        for c in problem.clauses.iter() {
            let t = c.head.ty.clone().into();
            env.add(c.head.id, t);
        }
        return env;
    }

    // 2.
    unimplemented!()
}

// Type inference in `Conflict`
// Input:
//   1. problem: validity checking problem
//   2. env_i(Γᵢ): Type Environment such that
//   2. env_i1(Γᵢ₊₁): Type Environment that is not able to refute cex currently
//   3. cex(ψ): Target candidate such that ℱ(Γᵢ) ⊨ ψ
// Output: Type Environment Γ such that
//   1. Γ ⋃ Γᵢ₊₁ ⊨ ψ
//   2. ℱ(⌊Γᵢ⌋) ↑ Γ
pub(super) fn infer(
    problem: &Problem,
    env_i: &TemplateEnv,
    env_i1: &TemplateEnv,
    cex: &Candidate,
) -> Option<TyEnv> {
    // 1. prepare unwound formulas
    // 2. infer intersection types
    let ienv = infer_intersection(problem, cex);
    // 2. prepare template
    let tenv = ienv.generate_template();
    // 3. calculate constraints

    // 3.1 calculate constraint `c` ℱ(⌊Γᵢ⌋) ↑ Γ
    let env_i = fml::Env::from_type_environment(env_i);

    let translated = problem.transform(&env_i); // ℱ(⌊Γᵢ⌋)
    let c = fml::env_types(&translated, &tenv);

    debug!("ℱ(⌊Γᵢ⌋) ↑ Γ");
    debug!("{}", c);

    // 3.2 calculate constraint `c2` from Γ ⋃ Γᵢ₊₁ ⊨ ψ

    let tenv_merged = TypeEnvironment::merge(&tenv, env_i1); // Γᵢ₊₁ ∪ Γ

    let tenv_merged_floored = Env::from_type_environment(&tenv_merged); // ⌊Γᵢ₊₁ ∪ Γ⌋
    let c2 = env_models_constraint(&tenv_merged_floored, cex);
    debug!("Γ ⋃ Γᵢ₊₁ ⊨ ψ");
    debug!("{}", c2);

    let constraint = fofml::Atom::mk_conj(c, c2);
    debug!("generated constraint: {}", constraint);
    // 4. solve constraints by CHC (or a template-based method)
    constraint.check_satisfiability().map(|model| {
        let mut result_env = TypeEnvironment::new();
        for (k, ts) in tenv.map.iter() {
            for t in ts {
                result_env.add(*k, t.assign(&model));
            }
        }
        result_env
    })
}
