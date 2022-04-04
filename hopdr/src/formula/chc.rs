use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;

use std::vec;

use crate::pdr::rtype::Refinement;

use super::pcsp;
use super::Bot;
use super::Negation;
use super::Subst;
use super::{Constraint, Fv, Ident, Logic, Op, Rename, Top};

#[derive(Debug, Clone)]
pub struct Atom {
    pub predicate: Ident,
    pub args: Vec<Op>,
}

pub trait TConstraint:
    Clone
    + Top
    + Bot
    + Negation
    + Logic
    + Subst<Id = Ident, Item = Op>
    + Fv<Id = Ident>
    + PartialEq
    + Rename
    + fmt::Display
{
}
impl<T> TConstraint for T where
    T: Clone
        + Top
        + Bot
        + Negation
        + Logic
        + Subst<Id = Ident, Item = Op>
        + Fv<Id = Ident>
        + PartialEq
        + Rename
        + fmt::Display
{
}

#[derive(Debug, Clone)]
pub enum CHCHead<C> {
    Constraint(C),
    Predicate(Atom),
}

#[derive(Debug, Clone)]
pub struct CHCBody<C> {
    pub predicates: Vec<Atom>,
    pub constraint: C,
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(", self.predicate)?;
        if !self.args.is_empty() {
            write!(f, "{}", self.args[0])?;
        }
        for arg in self.args[1..].iter() {
            write!(f, ",{}", arg)?;
        }
        write!(f, ")")
    }
}

impl<C: fmt::Display> fmt::Display for CHCHead<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CHCHead::Constraint(c) => write!(f, "{}", c),
            CHCHead::Predicate(a) => {
                write!(f, "{}", a)
            }
        }
    }
}
impl Atom {
    pub fn new(predicate: Ident, args: Vec<Op>) -> Atom {
        Atom { predicate, args }
    }
}

impl<C: TConstraint> CHCHead<C> {
    pub fn mk_true() -> CHCHead<C> {
        CHCHead::Constraint(C::mk_true())
    }
    pub fn mk_constraint(c: C) -> CHCHead<C> {
        CHCHead::Constraint(c)
    }
    pub fn mk_predicate(predicate: Ident, args: Vec<Op>) -> CHCHead<C> {
        CHCHead::Predicate(Atom { predicate, args })
    }
}
impl Rename for Atom {
    fn rename(&self, x: &Ident, y: &Ident) -> Self {
        let args = self.args.iter().map(|o| o.rename(x, y)).collect();
        Atom {
            args,
            predicate: self.predicate,
        }
    }
}
impl<C: Rename> Rename for CHCHead<C> {
    fn rename(&self, x: &Ident, y: &Ident) -> Self {
        match self {
            CHCHead::Constraint(c) => CHCHead::Constraint(c.rename(x, y)),
            CHCHead::Predicate(a) => CHCHead::Predicate(a.rename(x, y)),
        }
    }
}
impl<C: Rename> Rename for CHCBody<C> {
    fn rename(&self, x: &Ident, y: &Ident) -> Self {
        let constraint = self.constraint.rename(x, y);
        let predicates = self.predicates.iter().map(|a| a.rename(x, y)).collect();
        CHCBody {
            constraint,
            predicates,
        }
    }
}

#[derive(Debug, Clone)]
pub struct CHC<C> {
    pub body: CHCBody<C>,
    pub head: CHCHead<C>,
}

impl<C: Refinement> Rename for CHC<C> {
    fn rename(&self, x: &Ident, y: &Ident) -> Self {
        let body = self.body.rename(x, y);
        let head = self.head.rename(x, y);
        CHC { head, body }
    }
}

impl<C: Rename + Fv> CHCBody<C> {}

impl<C: Rename + Fv<Id = Ident> + Clone> CHC<C> {
    pub fn fresh_variailes(&self) -> CHC<C> {
        let mut fvs = self.body.fv();
        self.head.fv_with_vec(&mut fvs);

        let mut head = self.head.clone();
        let mut body = self.body.clone();
        let fvs = fvs.into_iter().map(|x| (x, Ident::fresh()));
        for (old, new) in fvs {
            head = head.rename(&old, &new);
            body = body.rename(&old, &new);
        }
        CHC { body, head }
    }
}

impl Fv for Atom {
    type Id = Ident;

    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>) {
        for a in self.args.iter() {
            a.fv_with_vec(fvs);
        }
    }
}

impl<C: Fv<Id = Ident>> Fv for CHCHead<C> {
    type Id = Ident;

    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>) {
        match &self {
            CHCHead::Constraint(c) => c.fv_with_vec(fvs),
            CHCHead::Predicate(a) => a.fv_with_vec(fvs),
        }
    }
}

impl<C: Fv<Id = Ident>> Fv for CHCBody<C> {
    type Id = Ident;

    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>) {
        for b in self.predicates.iter() {
            b.fv_with_vec(fvs);
        }
        self.constraint.fv_with_vec(fvs);
    }
}

impl<C: Fv<Id = Ident>> Fv for CHC<C> {
    type Id = Ident;

    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>) {
        self.body.fv_with_vec(fvs);
        self.head.fv_with_vec(fvs);
    }
}
fn to_pnf(a: &pcsp::Atom) -> pcsp::Atom {
    use pcsp::Atom;
    use pcsp::AtomKind;
    match a.kind() {
        AtomKind::True | AtomKind::Constraint(_) | AtomKind::Predicate(_, _) => a.clone(),
        AtomKind::Conj(a1, a2) => {
            let a1 = to_pnf(a1);
            let a2 = to_pnf(a2);
            Atom::mk_conj(a1, a2)
        }
        AtomKind::Disj(a1, a2) => {
            let a1 = to_pnf(a1);
            let a2 = to_pnf(a2);
            Atom::mk_disj(a1, a2)
        }
        AtomKind::Quantifier(_, _, a) => to_pnf(a),
    }
}

fn body_iter(body: pcsp::Atom) -> impl Iterator<Item = CHCBody<Constraint>> {
    fn translate(atom: pcsp::Atom, predicates: &mut Vec<Atom>, constraint: &mut Constraint) {
        match atom.kind() {
            pcsp::AtomKind::True => (),
            pcsp::AtomKind::Constraint(c) => {
                *constraint = Constraint::mk_conj(constraint.clone(), c.clone())
            }
            pcsp::AtomKind::Predicate(predicate, args) => predicates.push(Atom {
                predicate: *predicate,
                args: args.clone(),
            }),
            pcsp::AtomKind::Conj(_, _)
            | pcsp::AtomKind::Disj(_, _)
            | pcsp::AtomKind::Quantifier(_, _, _) => panic!("program error"),
        }
    }

    // 1. to_pnf
    let body = to_pnf(&body);
    // 2. dnf
    body.to_dnf().into_iter().map(|body| {
        let atoms = body.to_cnf();
        let mut constraint = Constraint::mk_true();
        let mut predicates = Vec::new();
        for atom in atoms {
            translate(atom, &mut predicates, &mut constraint);
        }
        CHCBody {
            predicates,
            constraint,
        }
    })
}

pub fn generate_chcs(
    pairs: impl Iterator<Item = (pcsp::Atom, CHCHead<Constraint>)>,
) -> Vec<CHC<Constraint>> {
    let mut chcs = Vec::new();
    for (body, head) in pairs {
        for body in body_iter(body) {
            chcs.push(CHC {
                body,
                head: head.clone(),
            })
        }
    }
    chcs
}

impl From<CHCBody<Constraint>> for pcsp::Atom {
    fn from(body: CHCBody<Constraint>) -> Self {
        let mut a = pcsp::Atom::mk_true();
        for b in body.predicates {
            let b = pcsp::Atom::mk_pred(b.predicate, b.args);
            a = pcsp::Atom::mk_conj(a, b);
        }
        pcsp::Atom::mk_conj(pcsp::Atom::mk_constraint(body.constraint), a)
    }
}
impl From<CHCBody<pcsp::Atom>> for pcsp::Atom {
    fn from(body: CHCBody<pcsp::Atom>) -> Self {
        let mut a = pcsp::Atom::mk_true();
        for b in body.predicates {
            let b = pcsp::Atom::mk_pred(b.predicate, b.args);
            a = pcsp::Atom::mk_conj(a, b);
        }
        pcsp::Atom::mk_conj(body.constraint, a)
    }
}

impl<C: fmt::Display + Top> fmt::Display for CHCBody<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        if !self.constraint.is_true() {
            first = false;
            write!(f, "{}", self.constraint)?;
        }
        for b in &self.predicates {
            if !first {
                write!(f, "/\\ ")?;
            } else {
                first = false;
            }
            write!(f, "{}", b)?;
        }
        Ok(())
    }
}
impl<C: fmt::Display + Top> fmt::Display for CHC<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} -> {}", self.body, self.head)
    }
}

impl From<CHCHead<Constraint>> for CHCHead<pcsp::Atom> {
    fn from(h: CHCHead<Constraint>) -> Self {
        match h {
            CHCHead::Constraint(c) => CHCHead::Constraint(c.into()),
            CHCHead::Predicate(p) => CHCHead::Predicate(p),
        }
    }
}

impl From<CHCBody<Constraint>> for CHCBody<pcsp::Atom> {
    fn from(h: CHCBody<Constraint>) -> Self {
        let constraint = h.constraint.into();
        CHCBody {
            constraint,
            predicates: h.predicates,
        }
    }
}

impl From<CHC<Constraint>> for CHC<pcsp::Atom> {
    fn from(c: CHC<Constraint>) -> Self {
        let body = c.body.into();
        let head = c.head.into();
        CHC { body, head }
    }
}

impl From<CHCHead<pcsp::Atom>> for CHCHead<Constraint> {
    fn from(h: CHCHead<pcsp::Atom>) -> Self {
        match h {
            CHCHead::Constraint(c) => CHCHead::Constraint(c.to_constraint().unwrap()),
            CHCHead::Predicate(p) => CHCHead::Predicate(p),
        }
    }
}

impl From<CHCBody<pcsp::Atom>> for CHCBody<Constraint> {
    fn from(h: CHCBody<pcsp::Atom>) -> Self {
        let constraint = h.constraint.to_constraint().unwrap();
        CHCBody {
            constraint,
            predicates: h.predicates,
        }
    }
}

impl From<CHC<pcsp::Atom>> for CHC<Constraint> {
    fn from(c: CHC<pcsp::Atom>) -> Self {
        let body = c.body.into();
        let head = c.head.into();
        CHC { body, head }
    }
}

impl<C: TConstraint> CHCBody<C> {
    fn collect_predicates(&self, predicates: &mut HashMap<Ident, usize>) {
        for a in self.predicates.iter() {
            match predicates.insert(a.predicate, a.args.len()) {
                Some(n) => debug_assert!(n == a.args.len()),
                None => (),
            }
        }
    }
}
impl<C: TConstraint> CHC<C> {
    pub fn collect_predicates(&self, predicates: &mut HashMap<Ident, usize>) {
        match &self.head {
            CHCHead::Constraint(_) => (),
            CHCHead::Predicate(a) => match predicates.insert(a.predicate, a.args.len()) {
                Some(n) => debug_assert!(n == a.args.len()),
                None => (),
            },
        }
        self.body.collect_predicates(predicates);
    }
}

fn cross_and<C: TConstraint>(
    left: Vec<Vec<CHCHead<C>>>,
    mut right: Vec<Vec<CHCHead<C>>>,
) -> Vec<Vec<CHCHead<C>>> {
    let mut ret = Vec::new();
    for x in left.iter() {
        for y in right.iter_mut() {
            let mut v = x.clone();
            v.append(y);
            ret.push(v);
        }
    }
    ret
}

pub fn to_dnf(atom: &pcsp::Atom) -> Vec<Vec<CHCHead<Constraint>>> {
    use pcsp::AtomKind;
    match atom.kind() {
        AtomKind::True => vec![vec![CHCHead::mk_true()]],
        AtomKind::Constraint(c) => vec![vec![CHCHead::mk_constraint(c.clone())]],
        AtomKind::Predicate(p, l) => vec![vec![CHCHead::mk_predicate(*p, l.clone())]],
        AtomKind::Conj(x, y) => {
            let left = to_dnf(x);
            let right = to_dnf(y);
            cross_and(left, right)
        }
        AtomKind::Disj(x, y) => {
            let mut left = to_dnf(x);
            let mut right = to_dnf(y);
            left.append(&mut right);
            left
        }
        AtomKind::Quantifier(_, _, _) => unimplemented!(),
    }
}
