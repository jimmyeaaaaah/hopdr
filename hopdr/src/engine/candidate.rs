use std::collections::HashSet;

use super::rtype;
use super::rtype::{Environment, TypeEnvironment};
use crate::formula::fofml;
use crate::formula::hes;
use crate::formula::pcsp;
use crate::formula::{
    Bot, Conjunctive, Constraint, Fv, Ident, IntegerEnvironment, Op, QuantifierKind, Rename, Subst,
    Top,
};

#[derive(Debug)]
pub struct Negative {}
pub type Sty = rtype::Tau<Negative, Constraint>;

fn consistent(s: &Sty, t: &rtype::Tau<rtype::Positive, pcsp::Atom>) -> fofml::Atom {
    use fofml::Atom;
    use rtype::TauKind::*;
    match (s.kind(), t.kind()) {
        (Proposition(x), Proposition(y)) => {
            Atom::mk_not(Atom::mk_conj(x.clone().into(), y.clone().into()))
        }
        (IArrow(x, s), IArrow(y, t)) => {
            let t = t.rename(y, x);
            let c = consistent(s, &t);
            Atom::mk_univq(x.clone(), c)
        }
        (Arrow(s1, s2), Arrow(t1, t2)) => {
            let c1 = Atom::mk_not(consistent(s1, t1));
            let c2 = consistent(s2, t2);
            Atom::mk_disj(c1, c2)
        }
        _ => panic!("program error"),
    }
}

fn types(
    env: &rtype::PosEnvironment,
    cl: &hes::Clause,
    rty: rtype::Tau<rtype::Positive, pcsp::Atom>,
) -> fofml::Atom {
    let mut env = Environment::from_type_environment(env.into());
    let t = env.add_arg_types(&cl.args, rty.into());
    let c = match t.kind() {
        rtype::TauKind::Proposition(c) => c,
        _ => panic!("program error"),
    };
    let c2 = rtype::type_check_goal(&cl.body, &mut env).unwrap();
    let p = pcsp::PCSP::new(c.clone(), c2.clone());
    p.into()
}

impl Sty {
    pub fn is_refutable(self, clause: &hes::Clause, env: rtype::PosEnvironment) {
        let mut new_idents = HashSet::new();
        let ty = self.clone_with_template(IntegerEnvironment::new(), &mut new_idents);
        let fml = consistent(&self, &ty);
        let fml2 = types(&env, clause, ty);
        let fml = fofml::Atom::mk_conj(fml, fml2);
        match fml.check_satisfiability() {
            Some(model) => unimplemented!(),
            None => unimplemented!(),
        }
    }
}
