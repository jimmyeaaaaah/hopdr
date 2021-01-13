use std::{collections::HashMap, rc::Rc, unimplemented};

use crate::formula::{Constraint, Ident, P, Type as SType, TypeKind as StypeKind};
use super::{Clause, Goal, GoalExpr, Atom};

#[derive(Debug)]
pub enum TauKind {
    Proposition(Constraint),
    Intersection(Tau, Tau),
    IArrow(Ident, Tau),
    Arrow(Tau, Tau)
}

pub type Tau = P<TauKind>;

impl Tau {
    fn mk_prop_ty(c: &Constraint) -> Tau {
        Tau::new(TauKind::Proposition(c.clone()))
    }

    fn mk_conj_ty(x: &Tau, y: &Tau) -> Tau {
        unimplemented!()
    }
}

impl TauKind {
    fn new_top(st: &SType) -> TauKind {
        use StypeKind::*;
        match &**st {
            Proposition => TauKind::Proposition(Constraint::mk_true()),
            Arrow(x, y) if **x == Integer => 
                TauKind::IArrow(Ident::fresh(), Tau::new(TauKind::new_top(y))),
            Arrow(x, y) => 
                TauKind::Arrow(Tau::new(TauKind::new_bot(x)), Tau::new(TauKind::new_top(y))),
            Integer => panic!("integer occurs at the result position"),
        }
    }

    fn new_bot(st: &SType) -> TauKind {
        use StypeKind::*;
        match &**st {
            Proposition => TauKind::Proposition(Constraint::mk_true()),
            Arrow(x, y) if **x == Integer => 
                TauKind::IArrow(Ident::fresh(), Tau::new(TauKind::new_top(y))),
            Arrow(x, y) => 
                TauKind::Arrow(Tau::new(TauKind::new_top(x)), Tau::new(TauKind::new_top(y))),
            Integer => panic!("integer occurs at the result position"),
        }
    }
}

pub struct Environment{
    // Vector: an instant intersection
    map: HashMap<Ident, Vec<Tau>>
}


impl Environment {
    pub fn merge(&mut self, _env: &Environment) {
        unimplemented!()
    }

    pub fn new() -> Environment {
        Environment{map: HashMap::new()}
    }

    fn add_(&mut self, v: Ident, t: Tau) {
        match self.map.get_mut(&v) {
            Some(v) => {v.push(t);},
            None => {self.map.insert(v, vec![t]);}
        }
    }

    pub fn add(&mut self, v: Ident, t: TauKind) {
        self.add_(v, Tau::new(t))
    }

    pub fn add_top(&mut self, v: Ident, st: &SType) {
        self.add(v, TauKind::new_top(st));
    }
}

pub enum Error {
    TypeError,
}

fn type_check_atom(atom: &Atom, env: &Environment) -> Tau {
    unimplemented!()
}

fn type_check_goal(goal: &Goal, tenv: &Environment) -> Constraint {
    use GoalExpr::*;
    let f = type_check_goal;
    match &**goal {
        Atom(atom) => unimplemented!(),
        Constr(c) => c.clone(),
        Conj(x, y) => Constraint::mk_conj(f(x, tenv), f(y, tenv)),
        Disj(x, y) => Constraint::mk_disj(f(x, tenv), f(y, tenv)),
        Univ(v, x) => Constraint::mk_univ(v.clone(), f(x, tenv))
    }
}

fn type_check_clause(clause: &Clause, rty: Tau, env: &Environment) {
}