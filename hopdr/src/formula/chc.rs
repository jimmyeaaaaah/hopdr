use std::collections::HashMap;
use std::fmt;
use std::collections::HashSet;
use std::iter::FromIterator;
use std::vec;

use super::{Conjunctive, Constraint, Ident, Op, Subst, Top, Fv, PredKind};
use super::pcsp;
use crate::util::P;

#[derive(Debug)]
pub enum CHCHead {
    Constraint(Constraint),
    Predicate(Ident, Vec<Ident>),
}
impl fmt::Display for CHCHead {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CHCHead::Constraint(c) => write!(f, "{}", c),
            CHCHead::Predicate(i, args) => {
                write!(f, "{}(", i)?;
                if args.len() > 0 {
                    write!(f, "{}", args[0])?;
                }
                for arg in args[1..].iter() {
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
    fn predicate<'a>(&'a self) -> Option<(&'a Ident, &'a Vec<Ident>)> {
        match self {
            CHCHead::Predicate(i, args) => Some((i, args)),
            _ => None
        }
    }
}

#[derive(Debug)]
pub struct CHC<A> {
    pub body: A,
    pub head: CHCHead,
}


impl <A> CHC<A> {
    fn new(head: CHCHead, body: A) -> CHC<A> {
        CHC{head, body}
    }
}

impl <A: fmt::Display> fmt::Display for CHC<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} -> {}", self.body, self.head)
    }
}

impl CHC<pcsp::Atom> {
    fn replace_inner(expr: &pcsp::Atom, target: &CHC<pcsp::Atom>) -> pcsp::Atom {
        let (target_p, target_args) = target.head.predicate().unwrap();
        match expr.kind() {
            pcsp::AtomKind::True |
            pcsp::AtomKind::Constraint(_) => expr.clone(),
            pcsp::AtomKind::Predicate(p, _) if p != target_p => expr.clone(),
            pcsp::AtomKind::Predicate(p, args) => {
                assert!(args.len() == target_args.len());
                let mut substs = Vec::new();
                for (x, y) in args.iter().zip(target_args.iter()) {
                    substs.push((*y, Op::mk_var(*x)))
                }
                target.body.subst_multi(&substs)
            },
            pcsp::AtomKind::Conj(x, y) => {
                pcsp::Atom::mk_conj(Self::replace_inner(x, target), Self::replace_inner(y, target))
            }
            pcsp::AtomKind::Disj(x, y) => {
                pcsp::Atom::mk_disj(Self::replace_inner(x, target), Self::replace_inner(y, target))
            },
        }
    }
    fn replace(self, target: &CHC<pcsp::Atom>) -> CHC<pcsp::Atom> {
        assert!(!self.head.have_same_predicate(&target.head));
        assert!(target.head.predicate().is_some());
        let body = Self::replace_inner(&self.body, target);
        CHC{body, ..self}
    }

}


#[derive(Debug, Copy, Clone)]
pub enum ResolutionError {
    TargetVariableNotFound,
    CHCNotDeterministic,
    ContainsDisjunctions
}

fn simplify_atom(atom: pcsp::Atom) -> pcsp::Atom {
    fn simplify_atom_inner(atom: &pcsp::Atom) -> Result<Constraint, pcsp::Atom> {
        match atom.kind() {
            pcsp::AtomKind::True => Ok(Constraint::mk_true()),
            pcsp::AtomKind::Constraint(c) => Ok(c.clone()),
            pcsp::AtomKind::Predicate(_, _) => Err(atom.clone()),
            pcsp::AtomKind::Conj(x, y) => {
                let x2 = simplify_atom_inner(x);
                let y2 = simplify_atom_inner(y);
                match (x2, y2) {
                    (Ok(x1), Ok(x2)) => Ok(Constraint::mk_conj(x1, x2)),
                    (Err(x), Ok(c)) | (Ok(c), Err(x)) => 
                        Err(pcsp::Atom::mk_conj(x, pcsp::Atom::mk_constraint(c))),
                    (Err(x), Err(y)) => {
                        Err(pcsp::Atom::mk_conj(x, y))
                    }
                }
            },
            pcsp::AtomKind::Disj(x, y) => {
                let x2 = simplify_atom_inner(x);
                let y2 = simplify_atom_inner(y);
                match (x2, y2) {
                    (Ok(x1), Ok(x2)) => Ok(Constraint::mk_disj(x1, x2)),
                    (Err(x), Ok(c)) | (Ok(c), Err(x)) => 
                        Err(pcsp::Atom::mk_disj(x, pcsp::Atom::mk_constraint(c))),
                    (Err(x), Err(y)) => {
                        Err(pcsp::Atom::mk_disj(x, y))
                    }
                }
            },
        }
    }

    match simplify_atom_inner(&atom) {
        Ok(x) => pcsp::Atom::mk_constraint(x),
        Err(x) => x,
    }
}

fn conjoin2vec(atom: &pcsp::Atom) -> Vec<pcsp::Atom> {
    fn conjoin2vec_inner(atom: &pcsp::Atom, result: &mut Vec<pcsp::Atom>) {
        match atom.kind() {
            pcsp::AtomKind::True |
            pcsp::AtomKind::Constraint(_) |
            pcsp::AtomKind::Predicate(_, _)  |
            pcsp::AtomKind::Disj(_, _) => result.push(atom.clone()),
            pcsp::AtomKind::Conj(x, y) => {
                conjoin2vec_inner(x, result);
                conjoin2vec_inner(y, result);
            }
        }
    }
    let mut result = Vec::new();
    let atom = &simplify_atom(atom.clone());
    conjoin2vec_inner(atom, &mut result);
    result
}

// Assumption: atom has already been simplified by simplify_atom.
fn atom2chc_head(atom: pcsp::Atom) -> Option<CHCHead> {
    match atom.kind() {
        pcsp::AtomKind::True => Some(CHCHead::Constraint(Constraint::mk_true())),
        pcsp::AtomKind::Constraint(c) => Some(CHCHead::Constraint(c.clone())),
        pcsp::AtomKind::Conj(c1, c2) => None,
        pcsp::AtomKind::Predicate(p, args) 
            => Some(CHCHead::Predicate(*p, args.clone())),
        pcsp::AtomKind::Disj(c1, c2) => None,
    }

}

pub fn pcsps2chcs(clauses: &[pcsp::PCSP<pcsp::Atom>]) -> Option<Vec<CHC<pcsp::Atom>>> {
    let mut result = Vec::new();
    for clause in clauses {
        let body = clause.body.clone();
        let atom_heads = conjoin2vec(&clause.head);
        for atom in atom_heads {
            match atom2chc_head(atom) {
                Some(head) => {
                    result.push(CHC::new(head, body.clone()))
                },
                None => {
                    return None
                }
            }
        }
    }
    Some(result)
}

// solve by resolution
pub fn solve_by_resolution(target: Ident, clauses: Vec<CHC<pcsp::Atom>>) -> Result<Constraint, ResolutionError> {
    debug!("solve_by_resolution: target={}", target);
    
    let mut defs= HashMap::new();
    let mut goals = Vec::new();
    for clause in clauses {
        match &clause.head {
            CHCHead::Constraint(_) => goals.push(clause),
            CHCHead::Predicate(p, args) => {
                if defs.insert(*p, clause).is_some() {
                    return Err(ResolutionError::CHCNotDeterministic)
                }
            },
        }
    }
    let mut defs = Vec::from_iter(defs.into_iter().map(|(_, x)| x));
    while defs.len() > 0 {
        let target= defs.pop().unwrap();
        goals = goals.into_iter().map(|g| {
            g.replace(&target)
        }).collect();
        defs= defs.into_iter().map(|g| {
            g.replace(&target)
        }).collect();
    }
    for c in goals.iter() {
        debug!("- constraint: {}", c)
    }

    // subst をするべきで、
    unimplemented!()
}