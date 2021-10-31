use std::collections::{HashMap, HashSet};
use std::fmt;

use super::pcsp;
use super::{Bot, Conjunctive, Constraint, Fv, Ident, Op, PredKind, QuantifierKind, Subst, Top};
use crate::util::P;

#[derive(Debug)]
pub enum AtomKind {
    True, // equivalent to Constraint(True). just for optimization purpose
    Constraint(Constraint),
    Predicate(Ident, Vec<Ident>),
    Conj(Atom, Atom),
    Disj(Atom, Atom),
    Not(Atom),
    Quantifier(QuantifierKind, Ident, Atom),
}
pub type Atom = P<AtomKind>;

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            AtomKind::True => write!(f, "true"),
            AtomKind::Constraint(c) => write!(f, "{}", c),
            AtomKind::Predicate(id, ops) => {
                write!(f, "{}(", id)?;
                for op in ops.iter() {
                    write!(f, "{},", op)?;
                }
                write!(f, ")")
            }
            AtomKind::Conj(x, y) => write!(f, "({} & {})", x, y),
            AtomKind::Disj(x, y) => write!(f, "({} & {})", x, y),
            AtomKind::Not(x) => write!(f, "not({})", x),
            AtomKind::Quantifier(q, x, c) => write!(f, "{} {}. {}", q, x, c),
        }
    }
}

impl Atom {
    pub fn check_satisfiability(&self) -> Option<HashMap<Ident, Constraint>> {
        unimplemented!()
    }
    pub fn mk_disj(x: Self, y: Self) -> Atom {
        use AtomKind::*;
        match (&*x, &*y) {
            (True, _) => y.clone(),
            (_, True) => x.clone(),
            _ => Atom::new(Conj(x.clone(), y.clone())),
        }
    }
    pub fn mk_false() -> Atom {
        Atom::mk_constraint(Constraint::mk_false())
    }
    pub fn mk_not(x: Self) -> Atom {
        Atom::new(AtomKind::Not(x))
    }
    // auxiliary function for generating constraint
    pub fn mk_constraint(c: Constraint) -> Atom {
        Atom::new(AtomKind::Constraint(c))
    }
    pub fn mk_pred(p: Ident, l: Vec<Ident>) -> Atom {
        Atom::new(AtomKind::Predicate(p, l))
    }
    pub fn mk_univq(x: Ident, c: Atom) -> Atom {
        Atom::new(AtomKind::Quantifier(QuantifierKind::Universal, x, c))
    }
}

impl Fv for Atom {
    type Id = Ident;
    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>) {
        match self.kind() {
            AtomKind::True | AtomKind::Constraint(_) => (),
            AtomKind::Predicate(ident, _) => {
                fvs.insert(*ident);
            }
            AtomKind::Conj(x, y) | AtomKind::Disj(x, y) => {
                x.fv_with_vec(fvs);
                y.fv_with_vec(fvs);
            }
            AtomKind::Not(x) => {
                x.fv_with_vec(fvs);
            }
            AtomKind::Quantifier(_, x, c) => {
                c.fv_with_vec(fvs);
                fvs.remove(x);
            }
        }
    }
}

impl From<Constraint> for Atom {
    fn from(from: Constraint) -> Atom {
        Atom::mk_constraint(from)
    }
}

impl From<pcsp::Atom> for Atom {
    fn from(from: pcsp::Atom) -> Atom {
        match from.kind() {
            pcsp::AtomKind::True => Atom::mk_true(),
            pcsp::AtomKind::Constraint(c) => Atom::mk_constraint(c.clone()),
            pcsp::AtomKind::Predicate(p, l) => Atom::mk_pred(*p, l.clone()),
            pcsp::AtomKind::Conj(x, y) => Atom::mk_conj(x.clone().into(), y.clone().into()),
            pcsp::AtomKind::Disj(x, y) => Atom::mk_disj(x.clone().into(), y.clone().into()),
            pcsp::AtomKind::Quantifier(q, x, c) if *q == QuantifierKind::Universal => {
                Atom::mk_univq(*x, c.clone().into())
            }
            pcsp::AtomKind::Quantifier(_q, _x, _c) => panic!("fail"),
        }
    }
}

impl From<pcsp::PCSP<pcsp::Atom>> for Atom {
    fn from(from: pcsp::PCSP<pcsp::Atom>) -> Atom {
        Atom::mk_disj(Atom::mk_not(from.body.into()), from.head.into())
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
            _ => Atom::new(Conj(x.clone(), y.clone())),
        }
    }
}

impl Subst for Atom {
    fn subst(&self, x: &Ident, v: &super::Op) -> Self {
        let eq = vec![Op::mk_var(*x), v.clone()];
        let c = Atom::mk_constraint(Constraint::mk_pred(PredKind::Eq, eq));
        Atom::mk_conj(c, self.clone())
    }
}
