use std::collections::HashMap;
use std::collections::HashSet;

use super::rtype;
use super::rtype::Environment;
use super::rtype::PosEnvironment;
use crate::formula::chc;
use crate::formula::fofml;
use crate::formula::hes;
use crate::formula::hes::{Goal, GoalKind};
use crate::formula::pcsp;
use crate::formula::{
    Bot, Conjunctive, Constraint, Fv, IntegerEnvironment, QuantifierKind, Rename, Top,
};

#[derive(Debug)]
pub struct Negative {}
pub type Sty = rtype::Tau<Negative, Constraint>;
pub type NegEnvironment = rtype::TypeEnvironment<Sty>;

fn consistent(
    s: &rtype::Tau<Negative, pcsp::Atom>,
    t: &rtype::Tau<rtype::Positive, pcsp::Atom>,
) -> fofml::Atom {
    use fofml::Atom;
    use rtype::TauKind::*;
    match (s.kind(), t.kind()) {
        (Proposition(x), Proposition(y)) => {
            Atom::mk_not(Atom::mk_conj(x.clone().into(), y.clone().into()))
        }
        (IArrow(x, s), IArrow(y, t)) => {
            let t = t.rename(y, x);
            let c = consistent(s, &t);
            Atom::mk_univq(*x, c)
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
    let t = env.add_arg_types(&cl.args, rty);
    let c = match t.kind() {
        rtype::TauKind::Proposition(c) => c,
        _ => panic!("program error"),
    };
    let c2 = rtype::type_check_goal(&cl.body, &mut env).unwrap();
    let p = pcsp::PCSP::new(c.clone(), c2);
    p.into()
}

fn types_negative(
    env: &rtype::TypeEnvironment<rtype::Tau<Negative, pcsp::Atom>>,
    cl: &hes::Clause,
    sty: rtype::Tau<Negative, pcsp::Atom>,
) -> fofml::Atom {
    let mut env = Environment::from_type_environment(env.clone());
    let t = env.add_arg_types(&cl.args, sty);
    let c = match t.kind() {
        rtype::TauKind::Proposition(c) => c,
        _ => panic!("program error"),
    };
    let c2 = type_check_goal(&cl.body, &mut env).unwrap();
    let p = pcsp::PCSP::new(c.clone(), c2);
    p.into()
}

fn env_consistent(
    env: &PosEnvironment,
    nenv: &rtype::TypeEnvironment<rtype::Tau<Negative, pcsp::Atom>>,
) -> fofml::Atom {
    let mut result = fofml::Atom::mk_true();
    for (i, v) in env.map.iter() {
        let mut tmp = fofml::Atom::mk_false();
        let w = nenv.get(i).unwrap();
        for x in w {
            let x = x.clone().into();
            for y in v {
                let y = y.clone().into();
                let fml = consistent(&x, &y);
                tmp = fofml::Atom::mk_disj(tmp, fml);
            }
        }
        result = fofml::Atom::mk_conj(result, tmp);
    }
    result
}

impl Sty {
    pub fn is_cex_available_top(
        &self,
        g: &hes::Goal,
        env: &rtype::PosEnvironment,
    ) -> Option<NegEnvironment> {
        // assert if self is prop sty
        match self.kind() {
            rtype::TauKind::Proposition(_) => (),
            rtype::TauKind::IArrow(_, _) | rtype::TauKind::Arrow(_, _) => panic!("program error"),
        };
        let dummy_clause = hes::Clause::new_top_clause(g.clone());
        self.is_cex_available(&dummy_clause, env)
    }

    /// returns Some(Δ) s.t. Δ |- clause: self iff cex is avalable
    pub fn is_cex_available(
        &self,
        clause: &hes::Clause,
        env: &rtype::PosEnvironment,
    ) -> Option<NegEnvironment> {
        let mut new_idents = HashMap::new();
        let template_env: rtype::TypeEnvironment<rtype::Tau<Negative, pcsp::Atom>> =
            env.clone_with_template(&mut new_idents);
        // generate_constraint
        let fml2 = env_consistent(env, &template_env);
        let fml = types_negative(&template_env, clause, self.clone().into());
        let fml = fofml::Atom::mk_conj(fml, fml2);
        // check_sat
        match fml.check_satisfiability(&new_idents) {
            Some(model) => {
                let mut result_env = rtype::TypeEnvironment::new();
                for (i, v) in template_env.map {
                    for x in v {
                        result_env.add(i, x.assign(&model));
                    }
                }
                Some(result_env)
            }
            None => None,
        }
    }
    pub fn is_refutable_top(
        &self,
        g: &hes::Goal,
        env: &rtype::PosEnvironment,
    ) -> Result<rtype::Ty, NegEnvironment> {
        match self.kind() {
            rtype::TauKind::Proposition(_) => (),
            rtype::TauKind::IArrow(_, _) | rtype::TauKind::Arrow(_, _) => panic!("program error"),
        };
        let dummy_clause = hes::Clause::new_top_clause(g.clone());
        self.is_refutable(&dummy_clause, env)
    }
    /// returns Ok(positive type) when this candidate is refutable
    /// otherwise, Err(NegEnvironmet) where NegEnvironment is a negative type environment Δ
    /// such that Δ |- clause: self
    pub fn is_refutable(
        &self,
        clause: &hes::Clause,
        env: &rtype::PosEnvironment,
    ) -> Result<rtype::Ty, NegEnvironment> {
        let mut new_idents = HashMap::new();
        let ty = self.clone_with_template(IntegerEnvironment::new(), &mut new_idents);
        let fml = consistent(&self.clone().into(), &ty);
        let fml2 = types(env, clause, ty.clone());
        let fml = fofml::Atom::mk_conj(fml, fml2);
        match fml.check_satisfiability(&new_idents) {
            Some(model) => Ok(ty.assign(&model)),
            None => Err(self.is_cex_available(clause, env).unwrap()),
        }
    }
}

pub fn type_check_goal<'a>(
    goal: &Goal,
    tenv: &mut Environment<rtype::Tau<Negative, pcsp::Atom>>,
) -> Result<pcsp::Atom, rtype::Error> {
    debug!("type_check_goal(negative) start: {}", goal);
    let f = type_check_goal;
    use rtype::{type_check_atom, TauKind};
    use GoalKind::*;
    let r = match goal.kind() {
        Atom(atom) => {
            let ts = type_check_atom(atom, tenv)?;
            for (t, constraints) in ts.iter() {
                debug!("- type: {}", t);
                for c in constraints.iter() {
                    debug!("-- constraint: {}", c)
                }
            }

            // TODO: here calculate greatest type
            let mut ret_constr = pcsp::Atom::mk_false();
            for (t, constraints) in ts {
                let mut targets = HashSet::new();
                t.fv_with_vec(&mut targets);
                match t.kind() {
                    TauKind::Proposition(_) => {
                        let c = chc::resolve_target(constraints, &targets).unwrap();
                        debug!("final constraint: {}", c);
                        ret_constr = pcsp::Atom::mk_disj(ret_constr, c.clone());
                    }
                    _ => panic!("program error. The result type of atom must be prop."),
                }
            }
            ret_constr
        }
        Constr(c) => c.clone().negate().unwrap().into(),
        Conj(x, y) => pcsp::Atom::mk_disj(f(x, tenv)?, f(y, tenv)?),
        Disj(x, y) => pcsp::Atom::mk_conj(f(x, tenv)?, f(y, tenv)?),
        Univ(v, x) => {
            if v.ty.is_int() {
                tenv.iadd(v.id);
                pcsp::Atom::mk_quantifier(QuantifierKind::Existential, v.id, f(x, tenv)?)
            } else {
                unimplemented!()
            }
        }
    };
    debug!("type_check_goal(negative): {} has type {} ", goal, r);
    Ok(r)
}
