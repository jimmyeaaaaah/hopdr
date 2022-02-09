use std::collections::HashMap;

use crate::formula::fofml;
use crate::formula::hes::{Clause, Goal, GoalKind};
use crate::formula::Constraint;
use crate::formula::Ident;
use crate::pdr::rtype::TyEnv;

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
    fn from_type_environment(tenv: TyEnv) -> Env {
        unimplemented!()
    }

    // ℱ(Σ)
    fn transform(&self) -> Env {
        unimplemented!()
    }

    fn eval(&self, g: Formula) -> Formula {
        unimplemented!()
    }
}
