use std::{collections::{HashMap, HashSet}, ffi::FromBytesWithNulError, rc::Rc, unimplemented};

use crate::formula::{Constraint, Ident, P, Type as SType, TypeKind as StypeKind, Variable, Op, IntegerEnvironment};
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
    // Assumption: all variables are alpha-renamed.
    map: HashMap<Ident, Tau>,
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

    pub fn get(&self, v: &Ident) -> Option<Tau> {
        self.map.get(v).map(|v| v.clone())
    }

    pub fn exists(&self, v: &Ident) -> bool {
        match self.map.get(v) {
            Some(_) => true,
            None => false,
        }
    }
}


pub enum Error {
    TypeError,
}

fn int_expr(atom: &Atom, env: &Environment) -> Option<Op> {
    use AtomKind::*;
    use ConstKind::*;
    match &**atom {
        Const(c) =>  {
            match &**c {
                Int(x) => Some(Op::mk_const(*x)),
                _ => None,
            }
        },
        // the given refinement type must be well-refined. That is,
        // if variable `v` is not in `env`, then it must be a variable 
        // of type Integer.
        Var(v) if !env.exists(v) => Some(Op::mk_var(v.clone())),
        _ => None,
    }
}

fn type_check_atom(atom: &Atom, env: &Environment) -> Tau {
    use AtomKind::*;
    match &**atom {
        App(x, arg) => {
            let ie = int_expr(arg, env);
            let t = type_check_atom(x, env);
            match ie {
                Some(op) => {
                    t.app(&op)
                },
                None => {
                    // subtyping
                    unimplemented!()
                }
            }
        },
        Var(v) => env.get(v).unwrap(),
        Const(c) => panic!("program error"),
    }
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
    unimplemented!()
}