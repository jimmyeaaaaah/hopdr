use std::{collections::HashMap, unimplemented};

use crate::formula::{Constraint};
use crate::util::P;

type Ident = u64;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Variable {
    id: Ident,
}

pub enum Sigma {
    Integer(Variable),
    Tau(Tau),
}

pub enum Tau {
    Proposition(Constraint),
    Intersection(P<Tau>, P<Tau>),
    Arrow(P<Sigma>, P<Tau>)
}

pub struct Environment{
    map: HashMap<Variable, Tau>
}

impl Environment {
    fn merge(&mut self, env: &Environment) {
        unimplemented!()
    }
}