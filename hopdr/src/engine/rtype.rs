use std::{collections::{HashMap, HashSet}, ffi::FromBytesWithNulError, rc::Rc, unimplemented};

use crate::formula::{Constraint, Ident, P, Type as SType, TypeKind as StypeKind, Op, IntegerEnvironment};
use super::{Clause, Goal, GoalExpr, Atom, AtomKind, ConstKind};

#[derive(Debug)]
pub enum TauKind {
    Proposition(Constraint),
    IArrow(Ident, Tau),
    Arrow(Tau, Tau),
}

pub type Tau = P<TauKind>;

impl Tau {
    fn mk_prop_ty(c: Constraint) -> Tau {
        Tau::new(TauKind::Proposition(c))
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
            TauKind::IArrow(id, _body) if id == x => self.clone(),
            TauKind::IArrow(id, body) => 
                Tau::mk_iarrow(*id, body.subst(x, v)),
            TauKind::Arrow(l, r) => 
                Tau::mk_arrow(l.subst(x, v), r.subst(x, v))
        }
    }

    fn arrow_unwrap(&self) -> (Tau, Tau) {
        match &**self {
            TauKind::Arrow(x, y) => (x.clone(), y.clone()),
            _ => panic!("unwrap fail")
        }
    }

    // infer the greatest refinement type t such that
    //   arrow_type <= arg_t -> t 
    fn infer_greatest_type(_arrow_type: &Tau, _arg_t: &Tau) {
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
            Proposition => TauKind::Proposition(Constraint::mk_false()),
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
    map: HashMap<Ident, Vec<Tau>>,
    imap: IntegerEnvironment,
}


impl Environment {
    pub fn merge(&mut self, _env: &Environment) {
        unimplemented!()
    }

    pub fn new() -> Environment {
        Environment{map: HashMap::new(), imap: IntegerEnvironment::new()}
    }

    fn add_(&mut self, v: Ident, t: Tau) {
        match self.map.get_mut(&v) {
            Some(s) => {
                s.push(t);
            },
            None => {
                self.map.insert(v, vec![t]);
            },
        }
    }

    pub fn tadd(&mut self, v: Ident, t: TauKind) {
        self.add_(v, Tau::new(t))
    }

    pub fn add_top(&mut self, v: Ident, st: &SType) {
        self.tadd(v, TauKind::new_top(st));
    }

    pub fn texists(&self, v: &Ident) -> bool {
        self.map.get(v).is_some()
    }

    pub fn iexists(&self, v: &Ident) -> bool {
        self.imap.exists(v)
    }

    pub fn tget<'a>(&'a self, v: &Ident) -> Option<&'a Vec<Tau>> {
        self.map.get(v)
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
        Var(v) if env.iexists(v) => Some(Op::mk_var(v.clone())),
        _ => None,
    }
}

fn type_check_atom(atom: &Atom, env: &Environment) -> Vec<Tau> {
    use AtomKind::*;
    match &**atom {
        App(x, arg) => {
            let ie = int_expr(arg, env);
            let ts = type_check_atom(x, env);
            match ie {
                Some(op) => {
                    ts.into_iter().map(|t| t.app(&op)).collect()
                },
                None => {
                    let ss = type_check_atom(arg, env);
                    let result_ts = Vec::new();
                    for t in ts.iter() {
                        for s in ss.iter() {
                            let _result_t = Tau::infer_greatest_type(t, s);
                            unimplemented!()
                        }
                    }
                    result_ts
                }
            }
        },
        Var(v) => env.tget(v).unwrap().clone(),
        Const(_c) => panic!("program error"),
    }
}

fn type_check_goal(goal: &Goal, tenv: &Environment) -> Constraint {
    use GoalExpr::*;
    let f = type_check_goal;
    match &**goal {
        Atom(atom) => {
            let ts = type_check_atom(atom, tenv);
            let mut ret_constr = Constraint::mk_false();
            for t in ts.iter() {
                match &**t {
                    TauKind::Proposition(c) => {
                        ret_constr = Constraint::mk_disj(ret_constr, c.clone())
                    },
                    _ => panic!("program error. The result type of atom must be prop.")
                }
            }
            ret_constr
        },
        Constr(c) => c.clone(),
        Conj(x, y) => Constraint::mk_conj(f(x, tenv), f(y, tenv)),
        Disj(x, y) => Constraint::mk_disj(f(x, tenv), f(y, tenv)),
        Univ(v, x) => Constraint::mk_univ(v.clone(), f(x, tenv))
    }
}

fn type_check_clause(_clause: &Clause, _rty: Tau, _env: &Environment) {
    unimplemented!()
}