use std::collections::HashMap;

use crate::formula::fofml;
use crate::formula::hes::{Clause, Goal, GoalKind};
use crate::formula::Constraint;
use crate::formula::Ident;
use crate::pdr::rtype::{least_fml, TyEnv};

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

// Formula Environment Σ
pub struct Env {
    map: HashMap<Ident, Formula>,
}

impl Env {
    // ⌊Γ⌋
    pub fn from_type_environment(tenv: TyEnv) -> Env {
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
        match g.kind() {
            GoalKind::Var(x) => match self.map.get(x) {
                Some(f) => f.clone(),
                None => Formula::mk_var(*x),
            },
            GoalKind::Abs(x, y) => Formula::mk_abs(x.clone(), y.clone()),
            GoalKind::App(x, y) => Formula::mk_app(x.clone(), y.clone()),
            GoalKind::Conj(x, y) => Formula::mk_conj(x.clone(), y.clone()),
            GoalKind::Disj(x, y) => Formula::mk_disj(x.clone(), y.clone()),
            GoalKind::Univ(x, y) => Formula::mk_univ(x.clone(), y.clone()),
            GoalKind::Constr(_) | GoalKind::Op(_) => g.clone(),
        }
    }
}
