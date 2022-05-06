use super::rtype::{Tau, TyEnv, TypeEnvironment};
use crate::formula::hes::{Goal, Problem as ProblemBase};
use crate::formula;
use crate::formula::{chc, fofml, pcsp, Bot, Constraint, Ident, Logic, Op, Top, Rename, Variable, Type as Sty};

use rpds::Stack;

use std::collections::HashSet;

type Atom = fofml::Atom;
type Candidate = Goal<Atom>;
type Ty = Tau<Atom>;
type TemplateEnv = TypeEnvironment<Ty>;
type Problem = ProblemBase<Atom>;

type ITy = Stack<Ty>;

impl Into<ITy> for Ty {
    fn into(self) -> ITy {
        let mut s = Stack::new();
        s.push_mut(self);
        s
    }
}

impl Sty {
    fn generate_template(ity: &Sty, env: &mut HashSet<Ident>) -> Ty {
        match ity.kind() {
            formula::TypeKind::Proposition => {
                let args: Vec<Op> = env.iter().map(|x| x.clone().into()).collect();
                let p = fofml::Atom::mk_fresh_pred(args);
                Ty::mk_prop_ty(p)
            }
            formula::TypeKind::Arrow(s, t) if s.is_int() => {
                let arg = Ident::fresh();
                env.insert(arg);
                let t = t.generate_template(env);
                let exists = env.remove(&arg);
                debug_assert!(exists);
                Ty::mk_iarrow(arg, t)
            },
            formula::TypeKind::Arrow(t1, t2) => {
                let v = xs.iter().map(|t| t.generate_template(env)).collect();
                let t = y.generate_template(env);
                Ty::mk_arrow(v, t)
            },
            formula::TypeKind::Integer => panic!("program error")
        }
    }
}

fn vec2ity(v: &[Ty]) -> ITy {
    let mut s = ITy::new();
    for t in v {
        s.push(t.clone());
    }
    s
}

/// calculates the required
/// where A := X | a | θ | A₁ A₂ |
/// (a: arithmetic terms, θ: constraints, X: variables)
///
/// Γ ⊢ ℛψ : •〈θ〉
/// tenv: Γ
/// term: ψ
/// constraint: θ
fn derive(tenv: &mut TemplateEnv, term: Candidate, constraint: Constraint, problem: &Problem) {
    fn go(
        tenv: &mut TemplateEnv,
        term: Candidate,
        constraint: Constraint,
        problem: &Problem,
    ) -> ITy {
        match term.kind() {
            crate::formula::hes::GoalKind::Constr(theta) => {
                Ty::mk_prop_ty(theta.clone().into()).into()
            }
            crate::formula::hes::GoalKind::Op(_) => {
                panic!("program error")
            }
            crate::formula::hes::GoalKind::Var(i) => vec2ity(tenv.get(i).unwrap()),
            crate::formula::hes::GoalKind::Abs(x, g) => {
                let (g, v) = if tenv.exists(&x.id) {
                    let new_id = Ident::fresh();
                    (g.rename(&x.id, &new_id), Variable::mk(new_id, x.ty.clone()))
                } else {
                    (g.clone(), x.clone())
                };
                tenv.add(&v.id, )
                go(tenv)
            },
            crate::formula::hes::GoalKind::App(_, _) => todo!(),
            crate::formula::hes::GoalKind::Conj(_, _) => todo!(),
            crate::formula::hes::GoalKind::Disj(_, _) => todo!(),
            crate::formula::hes::GoalKind::Univ(_, _) => todo!(),
        }
    }
}
