use super::{Constraint, Ident};
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
    pub fn mk_true() -> Atom {
        Atom::new(AtomKind::True)
    }
    pub fn mk_conj(x: &Atom, y: &Atom) -> Atom {
        use AtomKind::*;
        match (&**x, &**y) {
            (True, _) => y.clone(),
            (_, True) => x.clone(),
            _ => Atom::new(Conj(x.clone(), y.clone()))
        }
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