use std::collections::{HashMap, HashSet};
use std::fmt::Display;

use crate::formula::fofml;
use crate::formula::hes::{Clause, Goal, GoalKind};
use crate::formula::Constraint;
use crate::formula::Ident;
use crate::formula::{Bot, Conjunctive, Subst, Top};
use crate::pdr::rtype::{least_fml, TyEnv};
use crate::solver::smt;

pub type Formula = Goal<fofml::Atom>;

impl From<Goal<Constraint>> for Goal<fofml::Atom> {
    fn from(g: Goal<Constraint>) -> Self {
        match g.kind() {
            GoalKind::Constr(c) => Goal::mk_constr(c.clone().into()),
            GoalKind::Op(o) => Goal::mk_op(o.clone()),
            GoalKind::Var(v) => Goal::mk_var(*v),
            GoalKind::Abs(x, y) => Goal::mk_abs(x.clone(), y.clone().into()),
            GoalKind::App(x, y) => Goal::mk_app(x.clone().into(), y.clone().into()),
            GoalKind::Conj(x, y) => Goal::mk_conj(x.clone().into(), y.clone().into()),
            GoalKind::Disj(x, y) => Goal::mk_disj(x.clone().into(), y.clone().into()),
            GoalKind::Univ(x, y) => Goal::mk_univ(x.clone(), y.clone().into()),
        }
    }
}

impl From<Formula> for fofml::Atom {
    // Assumption: the frm formula has type *
    fn from(frm: Formula) -> Self {
        match frm.kind() {
            GoalKind::Constr(c) => c.clone(),
            GoalKind::Conj(g1, g2) => {
                let c1 = g1.clone().into();
                let c2 = g2.clone().into();
                fofml::Atom::mk_conj(c1, c2)
            }
            GoalKind::Disj(g1, g2) => {
                let c1 = g1.clone().into();
                let c2 = g2.clone().into();
                fofml::Atom::mk_conj(c1, c2)
            }
            GoalKind::Univ(x, g) => fofml::Atom::mk_univq(x.id, g.clone().into()),
            // the following must not happen
            GoalKind::Abs(_, _) | GoalKind::App(_, _) | GoalKind::Var(_) | GoalKind::Op(_) => {
                panic!("impossible to transform: {}", frm)
            }
        }
    }
}

impl Formula {
    fn reduce_inner(&self) -> Formula {
        println!("reduce_inner: {}", self);
        match self.kind() {
            GoalKind::Constr(_) => self.clone(),
            GoalKind::App(g, arg) => {
                // g must be have form \x. phi
                let g = g.reduce_inner();
                let arg = arg.reduce_inner();
                println!("app\n- {}\n- {}", g, arg);
                match g.kind() {
                    GoalKind::Abs(x, g) => g.clone().subst(&x.id, &arg),
                    _ => Goal::mk_app(g, arg),
                }
            }
            GoalKind::Conj(g1, g2) => {
                let g1 = g1.reduce_inner();
                let g2 = g2.reduce_inner();
                Goal::mk_conj(g1, g2)
            }
            GoalKind::Disj(g1, g2) => {
                let g1 = g1.reduce_inner();
                let g2 = g2.reduce_inner();
                Goal::mk_disj(g1, g2)
            }
            GoalKind::Univ(x, g) => {
                let g = g.reduce_inner();
                Goal::mk_univ(x.clone(), g)
            }
            GoalKind::Abs(x, g) => {
                let g = g.reduce_inner();
                Goal::mk_abs(x.clone(), g)
            }
            GoalKind::Var(_) | GoalKind::Op(_) => self.clone(),
        }
    }
    pub fn reduce(&self) -> fofml::Atom {
        // first reduces the formula to a formula of type *
        // then traslates it to a fofml::Atom constraint.
        println!("to be reduced: {}", &self);
        let g = self.reduce_inner();
        println!("reduced: {}", &g);
        g.into()
    }
}

// Formula Environment Σ
pub struct Env {
    map: HashMap<Ident, Formula>,
}

impl Display for Env {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (k, fml) in self.map.iter() {
            writeln!(f, "{}: {}\n", k, fml)?;
        }
        Ok(())
    }
}

impl Env {
    // ⌊Γ⌋
    pub fn from_type_environment(tenv: &TyEnv) -> Env {
        let mut map = HashMap::new();
        for (key, ts) in tenv.map.iter() {
            let fmls = ts.iter().map(|t| least_fml(t.clone()));
            map.insert(*key, Formula::mk_ho_disj(fmls, ts[0].to_sty()));
        }
        Env { map }
    }

    // ℱ(Σ)
    pub fn transform(&self, env: &Env) -> Env {
        let mut map = HashMap::new();
        for (key, goal) in env.map.iter() {
            map.insert(*key, env.eval(goal.clone()));
        }
        Env { map }
    }

    pub fn eval(&self, g: Formula) -> Formula {
        println!("eval: {}", g);
        match g.kind() {
            GoalKind::Var(x) => match self.map.get(x) {
                Some(f) => f.clone(),
                None => Formula::mk_var(*x),
            },
            GoalKind::Abs(x, y) => Formula::mk_abs(x.clone(), self.eval(y.clone())),
            GoalKind::App(x, y) => Formula::mk_app(self.eval(x.clone()), self.eval(y.clone())),
            GoalKind::Conj(x, y) => Formula::mk_conj(self.eval(x.clone()), self.eval(y.clone())),
            GoalKind::Disj(x, y) => Formula::mk_disj(self.eval(x.clone()), self.eval(y.clone())),
            GoalKind::Univ(x, y) => Formula::mk_univ(x.clone(), self.eval(y.clone())),
            GoalKind::Constr(_) | GoalKind::Op(_) => g.clone(),
        }
    }
}

// Γ ⊧ g ⇔ ⊧ θ where Γ(g) → θ
pub fn env_models(env: &Env, g: &Formula) -> bool {
    println!("env_models env: {}", env);
    let f = env.eval(g.clone());
    println!("env_models g: {}", f);
    let cnstr: fofml::Atom = f.reduce().into();
    let cnstr = cnstr.into();
    match smt::default_solver().solve(&cnstr, &HashSet::new()) {
        smt::SMTResult::Sat => true,
        smt::SMTResult::Unsat => false,
        smt::SMTResult::Timeout | smt::SMTResult::Unknown => panic!("smt check fail.."),
    }
}
