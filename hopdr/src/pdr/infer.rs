use super::rtype::{TyEnv, TypeEnvironment};
#[allow(unused_imports)]
use super::{fml, rtype};
use crate::formula;
#[allow(unused_imports)]
use crate::formula::hes::{Goal, Problem as ProblemBase};
#[allow(unused_imports)]
use crate::formula::{fofml, hes, Constraint};
use crate::util::P;
use std::fmt;

type Problem = ProblemBase<Constraint>;
type Candidate = Goal<Constraint>;

enum TypeKind {
    Proposition,
    Integer,
    Arrow(Type, Type),
    Intersection(Vec<Type>),
}
type Type = P<TypeKind>;
type ITEnv = TypeEnvironment<Type>;

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TypeKind::Proposition => write!(f, "bool"),
            TypeKind::Integer => write!(f, "integer"),
            TypeKind::Arrow(x, y) => write!(f, "({} -> {})", x, y),
            TypeKind::Intersection(v) => {
                if v.len() == 0 {
                    write!(f, "T")
                } else {
                    write!(f, "{}", v[0])?;
                    for t in &v[1..] {
                        write!(f, "/\\ {}", t)?;
                    }
                    Ok(())
                }
            }
        }
    }
}

impl Type {
    fn mk_prop() -> Type {
        Type::new(TypeKind::Proposition)
    }
    fn mk_int() -> Type {
        Type::new(TypeKind::Integer)
    }
    fn mk_arrow(t1: Type, t2: Type) -> Type {
        Type::new(TypeKind::Arrow(t1, t2))
    }
    #[allow(dead_code)]
    fn mk_intersection(ts: Vec<Type>) -> Type {
        Type::new(TypeKind::Intersection(ts))
    }
}

impl From<formula::Type> for Type {
    fn from(t: formula::Type) -> Self {
        match t.kind() {
            formula::TypeKind::Proposition => Type::mk_prop(),
            formula::TypeKind::Integer => Type::mk_int(),
            formula::TypeKind::Arrow(t1, t2) => {
                Type::mk_arrow(t1.clone().into(), t2.clone().into())
            }
        }
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

pub(super) fn infer(problem: &Problem, _env: &rtype::TyEnv, cex: &Candidate) -> Option<TyEnv> {
    // 1. prepare unwound formulas
    // 2. infer intersection types
    let ienv = infer_intersection(problem, cex);
    // 2. prepare template
    // 3. calculate constraints
    // 4. solve constraints by CHC (or a template-based method)
    // 5. return type environment
    None
}
