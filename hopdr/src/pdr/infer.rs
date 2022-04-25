use super::fml;
use super::fml::{env_models_constraint, Env};
use super::rtype::{Tau, TyEnv, TypeEnvironment};
use crate::formula::hes::{Goal, Problem as ProblemBase};
use crate::formula::{chc, fofml, pcsp, Bot, Constraint, Ident, Logic, Op, Top};
use crate::solver;
use crate::util::P;
use crate::{formula, title};

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

    // 2. temporarily do the same thing
    let mut env = ITEnv::new();
    for c in problem.clauses.iter() {
        let t = c.head.ty.clone().into();
        env.add(c.head.id, t);
    }
    return env;
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

    title!("Γᵢ");
    debug!("{}", env_i);
    // 3.1 calculate constraint `c` ℱ(⌊Γᵢ⌋) ↑ Γ
    let env_i = fml::Env::from_type_environment(env_i);

    title!("⌊Γᵢ⌋");
    debug!("{}", env_i);
    let translated = problem.transform(&env_i); // ℱ(⌊Γᵢ⌋)
    title!("ℱ⌊Γᵢ⌋");
    debug!("{}", translated);

    let c = fml::env_types(&translated, &tenv);
    title!("ℱ(⌊Γᵢ⌋) ↑ Γ");
    debug!("{}", c);

    // 3.2 calculate constraint `c2` from Γ ⋃ Γᵢ₊₁ ⊨ ψ

    let tenv_merged = TypeEnvironment::merge(&tenv, env_i1); // Γᵢ₊₁ ∪ Γ

    let tenv_merged_floored = Env::from_type_environment(&tenv_merged); // ⌊Γᵢ₊₁ ∪ Γ⌋
    let c2 = env_models_constraint(&tenv_merged_floored, cex);
    title!("Γ ⋃ Γᵢ₊₁ ⊨ ψ");
    debug!("{}", c2);

    let constraint = fofml::Atom::mk_conj(c, c2);
    title!("generated constraint");
    debug!("{}", constraint);

    // 4. solve constraints by CHC (or a template-based method)
    // 4.1 translate constraint to CHC or extended chc
    let constraint = constraint.reduce_not();
    let (quantifiers, pnf) = constraint.prenex_normal_form_raw(&mut HashSet::new());
    let mut ienv = HashSet::new();
    for (q, x) in quantifiers {
        match q {
            formula::QuantifierKind::Universal => {
                ienv.insert(x);
            }
            formula::QuantifierKind::Existential => panic!("program error"),
        }
    }
    let cnf = pnf.to_cnf();
    let mut is_chc = true;
    let mut clauses = Vec::new();
    title!("PNF");
    debug!("{}", pnf);
    title!("CNF");
    for c in cnf.iter() {
        debug!("{}", c);
    }

    for c in cnf {
        let dnf = c.to_dnf();
        let mut body = pcsp::Atom::mk_true();
        let mut head = pcsp::Atom::mk_false();
        for atom in dnf {
            match atom.kind() {
                fofml::AtomKind::True | fofml::AtomKind::Constraint(_) => {
                    body = pcsp::Atom::mk_conj(atom.negate().into(), body);
                }
                fofml::AtomKind::Predicate(_, _) => {
                    if !head.is_false() {
                        is_chc = false;
                    }
                    head = pcsp::Atom::mk_disj(atom.clone().into(), head);
                }
                fofml::AtomKind::Not(a) => {
                    match a.kind() {
                        fofml::AtomKind::Predicate(_, _) => {
                            body = pcsp::Atom::mk_conj(a.clone().into(), body)
                        }
                        _ => debug_assert!(false),
                    };
                }
                fofml::AtomKind::Quantifier(_, _, _)
                | fofml::AtomKind::Conj(_, _)
                | fofml::AtomKind::Disj(_, _) => {
                    panic!("program error")
                }
            }
        }
        clauses.push(pcsp::PCSP::new(body, head));
    }
    if is_chc {
        let clauses = clauses.into_iter().map(|c| {
            let head = match c.head.kind() {
                pcsp::AtomKind::Predicate(p, l) => {
                    chc::CHCHead::Predicate(chc::Atom::new(*p, l.clone()))
                }
                _ if c.head.is_false() => chc::CHCHead::Constraint(Constraint::mk_false()),
                _ => panic!("program error"),
            };
            (c.body, head)
        });
        let clauses = chc::generate_chcs(clauses);
        //debug!("{}", "[generated CHC]".bold());
        title!("generated CHC");
        for c in clauses.iter() {
            debug!("{}", c);
        }
        //let clauses: Vec<chc::CHC<pcsp::Atom>> =
        //    clauses.iter().map(|x| x.to_trivial_recursive()).collect();
        //for c in clauses.iter() {
        //    debug!("{}", c);
        //}

        let m = match solver::chc::default_solver().solve(&clauses) {
            solver::chc::CHCResult::Sat(m) => m,
            solver::chc::CHCResult::Unsat => return None,
            solver::chc::CHCResult::Unknown => panic!(
                "PDR fails to infer a refinement type due to the background CHC solver's error"
            ),
            solver::chc::CHCResult::Timeout => panic!(
                "PDR fails to infer a refinement type due to timeout of the background CHC solver"
            ),
        };

        title!("model from CHC solver");
        // TODO: Display model
        debug!("{}", m);
        let m = solver::interpolation::solve(&clauses);
        debug!("interpolated:");
        debug!("{}", m);
        let model = m.model;
        let mut result_env = TypeEnvironment::new();
        for (k, ts) in tenv.map.iter() {
            for t in ts {
                result_env.add(*k, t.assign(&model));
            }
        }
        Some(result_env)
    } else {
        debug!("uouo");
        for c in &clauses {
            debug!("{}", c);
        }
        assert!(false);
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
}
