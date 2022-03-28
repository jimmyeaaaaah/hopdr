use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;
use std::iter::FromIterator;
use std::vec;

use super::fofml;
use super::pcsp;
use super::{Constraint, Fv, Ident, Logic, Op, Rename, Top};

#[derive(Debug, Clone)]
pub struct Atom {
    predicate: Ident,
    args: Vec<Op>
}

#[derive(Debug, Clone)]
pub enum CHCHead {
    Constraint(Constraint),
    Predicate(Atom),
}
impl fmt::Display for CHCHead {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CHCHead::Constraint(c) => write!(f, "{}", c),
            CHCHead::Predicate(a) => {
                write!(f, "{}(", a.predicate)?;
                if !a.args.is_empty() {
                    write!(f, "{}", a.args[0])?;
                }
                for arg in a.args[1..].iter() {
                    write!(f, ",{}", arg)?;
                }
                write!(f, ")")
            }
        }
    }
}
impl CHCHead {
    fn have_same_predicate(&self, other: &CHCHead) -> bool {
        match (self, other) {
            (CHCHead::Predicate(p, _), CHCHead::Predicate(q, _)) if p == q => true,
            _ => false,
        }
    }
    fn predicate<'a>(&'a self) -> Option<(&'a Ident, &'a Vec<Op>)> {
        match self {
            CHCHead::Predicate(i, args) => Some((i, args)),
            _ => None,
        }
    }
    pub fn mk_true() -> CHCHead {
        CHCHead::Constraint(Constraint::mk_true())
    }
    pub fn mk_constraint(c: Constraint) -> CHCHead {
        CHCHead::Constraint(c)
    }
    pub fn mk_predicate(id: Ident, args: Vec<Op>) -> CHCHead {
        CHCHead::Predicate(id, args)
    }
}
impl Rename for CHCHead {
    fn rename(&self, x: &Ident, y: &Ident) -> Self {
        match self {
            CHCHead::Constraint(c) => CHCHead::Constraint(c.rename(x, y)),
            CHCHead::Predicate(_p, _args) => {
                unimplemented!()
                //let new_args = Ident::rename_idents(args, x, y);
                //CHCHead::Predicate(*p, new_args)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct CHC {
    pub body: Vec<CHCHead>,
    pub head: CHCHead,
}

impl Rename for CHC {
    fn rename(&self, x: &Ident, y: &Ident) -> Self {
        let body = self.body.iter().map(|h| h.rename(x, y)).collect();
        CHC::new(self.head.rename(x, y), body)
    }
}

impl Fv for CHCHead {
    type Id = Ident;

    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>) {
        match &self {
            CHCHead::Constraint(c) => c.fv_with_vec(fvs),
            CHCHead::Predicate(_, l) => {
                for i in l {
                    i.fv_with_vec(fvs);
                }
            }
        }
    }
}

impl Fv for CHC {
    type Id = Ident;

    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>) {
        for b in self.body.iter() {
            b.fv_with_vec(fvs);
        }
        self.head.fv_with_vec(fvs);
    }
}

impl CHCHead {
    pub fn new(body: pcsp::Atom) -> Vec<CHCHead> {
        // 1. to_pnf
        // 2. dnf
        // 3. cnf
    }
}

impl fmt::Display for CHC {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.body.len() > 0 {
            write!(f, "{}", self.body[0])?;
            for b in &self.body[1..] {
                write!(f, "/\\ {}", b)?;
            }
        }
        write!(f, " -> {}", self.head)
    }
}

impl CHC {
    fn vec_to_atom() -> 
    fn replace_inner(expr: &pcsp::Atom, target: &CHC) -> pcsp::Atom {
        let (target_p, target_args) = target.head.predicate().unwrap();
        match expr.kind() {
            pcsp::AtomKind::True | pcsp::AtomKind::Constraint(_) => expr.clone(),
            pcsp::AtomKind::Predicate(p, _) if p != target_p => expr.clone(),
            pcsp::AtomKind::Predicate(_, args) => {
                assert!(args.len() == target_args.len());
                for (_x, _y) in args.iter().zip(target_args.iter()) {
                    unimplemented!()
                    //if x != y {
                    //    panic!("replace failure")
                    //}
                }
                target.body.clone()
            }
            pcsp::AtomKind::Conj(x, y) => pcsp::Atom::mk_conj(
                Self::replace_inner(x, target),
                Self::replace_inner(y, target),
            ),
            pcsp::AtomKind::Disj(x, y) => pcsp::Atom::mk_disj(
                Self::replace_inner(x, target),
                Self::replace_inner(y, target),
            ),
            pcsp::AtomKind::Quantifier(q, x, c) => {
                pcsp::Atom::mk_quantifier(*q, *x, Self::replace_inner(c, target))
            }
        }
    }
    fn replace(self, target: &CHC) -> CHC {
        assert!(!self.head.have_same_predicate(&target.head));
        assert!(target.head.predicate().is_some());
        let body = Self::replace_inner(&self.body, target);
        CHC { body, ..self }
    }
    pub fn collect_predicates(&self, predicates: &mut HashMap<Ident, usize>) {
        match &self.head {
            CHCHead::Constraint(_) => (),
            CHCHead::Predicate(p, l) => match predicates.insert(*p, l.len()) {
                Some(n) => debug_assert!(n == l.len()),
                None => (),
            },
        }
        self.body.collect_predicates(predicates);
    }
}

fn cross_and(left: Vec<Vec<CHCHead>>, mut right: Vec<Vec<CHCHead>>) -> Vec<Vec<CHCHead>> {
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

pub fn to_dnf(atom: &pcsp::Atom) -> Vec<Vec<CHCHead>> {
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
