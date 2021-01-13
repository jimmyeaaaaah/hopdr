use std::{collections::HashMap, ffi::FromBytesWithNulError, rc::Rc, unimplemented};

use crate::formula::{Constraint, Ident, P, Type as SType, TypeKind as StypeKind, Variable, Op};
use super::{Clause, Goal, GoalExpr, Atom, AtomKind, ConstKind};

#[derive(Debug)]
pub enum TauKind {
    Proposition(Constraint),
    Intersection(Tau, Tau),
    IArrow(Ident, Tau),
    Arrow(Tau, Tau)
}

pub type Tau = P<TauKind>;

impl Tau {
    fn mk_prop_ty(c: Constraint) -> Tau {
        Tau::new(TauKind::Proposition(c))
    }

    fn mk_intersection(x: Tau, y: Tau) -> Tau {
        Tau::new(TauKind::Intersection(x, y))
    }

    fn mk_iarrow(id: Ident, t: Tau) -> Tau {
        Tau::new(TauKind::IArrow(id, t))
    }

    fn mk_arrow(t: Tau, s: Tau) -> Tau {
        Tau::new(TauKind::Arrow(t, s))
    }

    fn app(&self, v: &Op) -> Tau {
        match &**self {
            TauKind::IArrow(x, t) => t.subst(x, v),
            _ => panic!("program error: tried to app integer to non-integer arrow type"),
        }
    }

    // \tau[v/x]
    fn subst(&self, x: &Ident, v: &Op) -> Tau {
        match &**self {
            TauKind::Proposition(c) => Tau::mk_prop_ty(c.subst(x, v)),
            TauKind::Intersection(r, l) => 
                Tau::mk_intersection(r.subst(x, v), l.subst(x, v)),
            TauKind::IArrow(id, body) if id == x => self.clone(),
            TauKind::IArrow(id, body) => 
                Tau::mk_iarrow(*id, body.subst(x, v)),
            TauKind::Arrow(l, r) => 
                Tau::mk_arrow(l.subst(x, v), r.subst(x, v))
        }
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
    map: HashMap<Ident, Tau>
}


impl Environment {
    pub fn merge(&mut self, _env: &Environment) {
        unimplemented!()
    }

    pub fn new() -> Environment {
        Environment{map: HashMap::new()}
    }

    fn add_(&mut self, v: Ident, t: Tau) {
        match self.map.get(&v) {
            Some(s) => {
                let t = Tau::mk_intersection(s.clone(), t.clone());
                self.map.insert(v, t)
            },
            None => self.map.insert(v, t)
        };
    }

    pub fn add(&mut self, v: Ident, t: TauKind) {
        self.add_(v, Tau::new(t))
    }

    pub fn add_top(&mut self, v: Ident, st: &SType) {
        self.add(v, TauKind::new_top(st));
    }

    pub fn get(&self, v: &Variable) -> Option<Tau> {
        self.map.get(&v.id).map(|v| v.clone())
    }
}

pub enum Error {
    TypeError,
}

fn type_check_atom(atom: &Atom, env: &Environment) -> Tau {
    use AtomKind::*;
    use ConstKind::*;
    unimplemented!()
    //match &**atom {
    //    Var(v) => env.get(v).unwrap(),
    //    App(x, Const(Int(x))) => {
    //        let t = type_check_atom(x, env);
    //        t.app(x)
    //    }
    //    Abs(_, _) => {}
    //    Const(c) => panic!("program error")
    //}
}

fn type_check_goal(goal: &Goal, tenv: &Environment) -> Constraint {
    use GoalExpr::*;
    let f = type_check_goal;
    match &**goal {
        Atom(atom) => {
            let t = type_check_atom(atom, tenv);
            match &*t {
                TauKind::Proposition(c) => c.clone(),
                _ => panic!("program error. The result type of atom must be prop.")
            }
        },
        Constr(c) => c.clone(),
        Conj(x, y) => Constraint::mk_conj(f(x, tenv), f(y, tenv)),
        Disj(x, y) => Constraint::mk_disj(f(x, tenv), f(y, tenv)),
        Univ(v, x) => Constraint::mk_univ(v.clone(), f(x, tenv))
    }
}

fn type_check_clause(clause: &Clause, rty: Tau, env: &Environment) {

}