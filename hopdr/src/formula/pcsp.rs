use std::unimplemented;

use super::{Conjunctive, Constraint, Top, Subst, Ident, Op, Variable};
use crate::util::P;


#[derive(Debug)]
pub enum AtomKind {
    True, // equivalent to Constraint(True). just for optimization purpose
    Constraint(Constraint),
    Predicate(Ident, Vec<Ident>),
    Conj(Atom, Atom),
}
pub type Atom = P<AtomKind>;

impl Atom {
    pub fn mk_pred(ident: Ident, args: Vec<Ident>) -> Atom {
        Atom::new(AtomKind::Predicate(ident, args))
    }
    pub fn fresh_pred(args: Vec<Ident>) -> Atom {
        let ident = Ident::fresh();
        Atom::mk_pred(ident, args)
    }
}

impl Atom {
    // auxiliary function for generating constraint
    pub fn mk_constraint(c: Constraint) -> Atom {
        Atom::new(AtomKind::Constraint(c))
    }
}

impl From<Constraint> for Atom {
    fn from(from: Constraint) -> Atom {
        Atom::mk_constraint(from)
    }
}


impl Top for Atom {
    fn mk_true() -> Self {
        Atom::new(AtomKind::True)
    }
}

impl Conjunctive for Atom {
    fn mk_conj(x: Self, y: Self) -> Atom {
        use AtomKind::*;
        match (&*x, &*y) {
            (True, _) => y.clone(),
            (_, True) => x.clone(),
            _ => Atom::new(Conj(x.clone(), y.clone()))
        }
    }
}

impl Subst for Atom {
    fn subst(&self, _x: &Ident, _v: &super::Op) -> Self {
        unimplemented!()
    }
}


#[derive(Debug)]
pub struct PCSP {
    body: Atom,
    head: Atom,
}

impl PCSP {
    pub fn new(body: &Atom, head: &Atom) -> PCSP {
        PCSP { body: body.clone(), head: head.clone() }
    }
}