use std::{collections::HashMap, rc::Rc, unimplemented};

use crate::formula::{Constraint, Type as SType};
use crate::util::{global_counter, P};

type Ident = u64;
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Variable {
    id: Ident,
}

impl Variable {
    fn fresh() -> Variable {
        let id = global_counter();
        Variable{ id }
    }
}

pub enum TauKind {
    Proposition(Constraint),
    Intersection(Tau, Tau),
    IArrow(Variable, Tau),
    Arrow(Tau, Tau)
}

pub type Tau = Rc<TauKind>;

impl TauKind {
    fn new_top(st: &SType) -> TauKind {
        match st {
            SType::Proposition => TauKind::Proposition(Constraint::True),
            SType::Arrow(x, y) if **x == SType::Integer => 
                TauKind::IArrow(Variable::fresh(), Tau::new(TauKind::new_top(y))),
            SType::Arrow(x, y) => 
                TauKind::Arrow(Tau::new(TauKind::new_bot(x)), Tau::new(TauKind::new_top(y))),
            SType::Integer => panic!("integer occurs at the result position"),
        }
    }

    fn new_bot(st: &SType) -> TauKind {
        match st {
            SType::Proposition => TauKind::Proposition(Constraint::True),
            SType::Arrow(x, y) if **x == SType::Integer => 
                TauKind::IArrow(Variable::fresh(), Tau::new(TauKind::new_top(y))),
            SType::Arrow(x, y) => 
                TauKind::Arrow(Tau::new(TauKind::new_top(x)), Tau::new(TauKind::new_top(y))),
            SType::Integer => panic!("integer occurs at the result position"),
        }
    }
}

pub struct Environment{
    map: HashMap<Variable, Tau>
}


impl Environment {
    fn merge(&mut self, env: &Environment) {
        unimplemented!()
    }

    fn new() -> Environment {
        Environment{map: HashMap::new()}
    }

    fn add(&mut self, v: Variable, t: TauKind) {
        self.map.insert(v, Tau::new(t));
    }

    fn add_top(&mut self, v: Variable, st: &SType) {
        self.add(v, TauKind::new_top(st));
    }

}