use std::collections::HashMap;
use std::fmt;
use std::collections::HashSet;
use std::vec;

use super::{Conjunctive, Constraint, Ident, Op, Subst, Top, Fv, PredKind};
use super::pcsp;
use crate::util::P;

pub enum CHCHead {
    Constraint(Constraint),
    Predicate(Ident, Vec<Ident>),
}

#[derive(Debug)]
pub struct CHC<A> {
    pub body: A,
    pub head: CHCHead,
}

impl CHC<pcsp::Atom> {
    fn replace_inner(expr: &pcsp::Atom, target: &CHC<pcsp::Atom>) -> pcsp::Atom {
        let target_p = &target.head.0;
        match expr.kind() {
            pcsp::AtomKind::True |
            pcsp::AtomKind::Constraint(_) => expr.clone(),
            pcsp::AtomKind::Predicate(p, _) if p != target_p => expr.clone(),
            pcsp::AtomKind::Predicate(p, args) => {
                assert!(args.len() == target.head.1.len());
                let mut substs = Vec::new();
                for (x, y) in args.iter().zip(target.head.1.iter()) {
                    substs.push((*y, Op::mk_var(*x)))
                }
                target.body.subst_multi(&substs)
            },
            pcsp::AtomKind::Conj(x, y) => {
                pcsp::Atom::mk_conj(Self::replace_inner(x, target), Self::replace_inner(y, target))
            }
        }
    }
    fn replace(self, target: &CHC<pcsp::Atom>) -> CHC<pcsp::Atom> {
        assert!(self.head.0 != target.head.0);
        let body = Self::replace_inner(&self.body, target);
        CHC{body, ..self}
    }
}


#[derive(Debug, Copy, Clone)]
pub enum ResolutionError {
    TargetVariableNotFound,
    CHCNotDeterministic,
}

fn atom2chc_head(atom: pcsp::Atom) -> Option<CHCHead> {
    match atom.kind() {
        pcsp::AtomKind::True => Some(CHCHead::Constraint(Constraint::mk_true())),
        pcsp::AtomKind::Constraint(c) => Some(CHCHead::Constraint(c.clone())),
        pcsp::AtomKind::Conj(_, _) => None,
        pcsp::AtomKind::Predicate(p, args) 
            => Some(CHC{body: clause.body, head: CHCHead::Predicate(*p, args.clone())}),
    }

}

pub fn pcsp2chc(clause: pcsp::PCSP<pcsp::Atom>) -> Option<CHC<pcsp::Atom>> {
}

// solve by resolution
pub fn solve_by_resolution(target: Ident, clauses: Vec<CHC<pcsp::Atom>>) -> Result<Constraint, ResolutionError> {
    debug!("solve_by_resolution: target={}", target);
    let mut idents = HashSet::new();
    for clause in clauses.iter() {
        idents.insert(clause.head.0);
        clause.body.fv_with_vec(&mut idents);
    }
    if !idents.remove(&target) {
        debug!("target variable is not in cluases");
        return Err(ResolutionError::TargetVariableNotFound)
    }

    let mut map = HashMap::new();

    for clause in clauses {
        if map.insert(clause.head.0, clause).is_some() {
            return Err(ResolutionError::CHCNotDeterministic)
        }     
    }

    for ident in idents {
        let target = map.remove(&ident).unwrap();
        let mut new_map = HashMap::new();
        for (ident, clause) in map.into_iter() {
            if &ident == &target.head.0 {
                continue;
            }
            new_map.insert(ident, clause.replace(&target));
        }
        map = new_map;
    }
    unimplemented!()
}