use std::collections::HashMap;

use crate::formula::fofml;
use crate::formula::hes::{Clause, Goal, GoalKind};
use crate::formula::Ident;
use crate::pdr::rtype::TyEnv;

pub type Formula = Goal<fofml::Atom>;

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
