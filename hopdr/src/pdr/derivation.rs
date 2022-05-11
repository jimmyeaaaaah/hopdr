use super::rtype::{Tau, TyEnv, TypeEnvironment};
use crate::formula;
use crate::formula::hes::{Goal, Problem as ProblemBase};
use crate::formula::{
    chc, fofml, pcsp, Bot, Constraint, Ident, Logic, Op, Rename, Top, Type as Sty, Variable,
};

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
    fn generate_template(&self, env: &mut HashSet<Ident>) -> Ty {
        match self.kind() {
            formula::TypeKind::Proposition => {
                let args: Vec<Op> = env.iter().map(|x| x.clone().into()).collect();
                let p = fofml::Atom::mk_fresh_pred(args);
                Ty::mk_prop_ty(p)
            }
            formula::TypeKind::Arrow(s, t) if s.is_int() => {
                let arg = Ident::fresh();
                env.insert(arg);
                let t = self.generate_template(env);
                let exists = env.remove(&arg);
                debug_assert!(exists);
                Ty::mk_iarrow(arg, t)
            }
            formula::TypeKind::Arrow(t1, t2) => {
                let v = vec![t1.generate_template(env)];
                let t = t2.generate_template(env);
                Ty::mk_arrow(v, t)
            }
            formula::TypeKind::Integer => panic!("program error"),
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
