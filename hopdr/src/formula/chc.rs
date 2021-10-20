use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;
use std::iter::FromIterator;
use std::vec;

use super::pcsp;
use super::{Bot, Conjunctive, Constraint, Fv, Ident, Op, PredKind, Rename, Subst, Top};
use crate::util::P;

#[derive(Debug, Clone)]
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
            _ => None,
        }
    }
    pub fn mk_true() -> CHCHead {
        CHCHead::Constraint(Constraint::mk_true())
    }
    pub fn mk_constraint(c: Constraint) -> CHCHead {
        CHCHead::Constraint(c)
    }
    pub fn mk_predicate(id: Ident, args: Vec<Ident>) -> CHCHead {
        CHCHead::Predicate(id, args)
    }
}
impl Rename for CHCHead {
    fn rename(&self, x: &Ident, y: &Ident) -> Self {
        match self {
            CHCHead::Constraint(c) => CHCHead::Constraint(c.rename(x, y)),
            CHCHead::Predicate(p, args) => {
                let new_args = Ident::rename_idents(args, x, y);
                CHCHead::Predicate(*p, new_args)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct CHC<A> {
    pub body: A,
    pub head: CHCHead,
}

impl<A: Rename> Rename for CHC<A> {
    fn rename(&self, x: &Ident, y: &Ident) -> Self {
        CHC::new(self.head.rename(x, y), self.body.rename(x, y))
    }
}

impl<A> CHC<A> {
    fn new(head: CHCHead, body: A) -> CHC<A> {
        CHC { head, body }
    }
}

impl<A: fmt::Display> fmt::Display for CHC<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} -> {}", self.body, self.head)
    }
}

impl CHC<pcsp::Atom> {
    fn replace_inner(expr: &pcsp::Atom, target: &CHC<pcsp::Atom>) -> pcsp::Atom {
        let (target_p, target_args) = target.head.predicate().unwrap();
        match expr.kind() {
            pcsp::AtomKind::True | pcsp::AtomKind::Constraint(_) => expr.clone(),
            pcsp::AtomKind::Predicate(p, _) if p != target_p => expr.clone(),
            pcsp::AtomKind::Predicate(_, args) => {
                assert!(args.len() == target_args.len());
                for (x, y) in args.iter().zip(target_args.iter()) {
                    if x != y {
                        panic!("replace failure")
                    }
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
        }
    }
    fn replace(self, target: &CHC<pcsp::Atom>) -> CHC<pcsp::Atom> {
        assert!(!self.head.have_same_predicate(&target.head));
        assert!(target.head.predicate().is_some());
        let body = Self::replace_inner(&self.body, target);
        CHC { body, ..self }
    }

    fn resolve_target(&self, target: &Ident) -> Result<Constraint, ResolutionError> {
        // 1. transform body of chc to disjunction normal form: bodies
        // 2. check when P(x, y, z) /\ P'(x', y', z') then x = x' and y = y' and z = z' and P = P' = target
        // 3. transform each body in bodies to P(x, y, z) /\ constraint => constraint'
        // 4. negate constraint, then P(x, y, z) => not(constraint) \/ constraint'
        // 5. returns /\_[for each body in bodies] not(constraint) \/ constraint'

        // 1. to dnf
        let bodies = to_dnf(&self.body);
        let head = match &self.head {
            CHCHead::Constraint(c) => c.clone(),
            CHCHead::Predicate(_, _) => return Err(ResolutionError::IllegalConstraint),
        };

        let mut result = Constraint::mk_true();
        for body in bodies.iter() {
            // 2. check
            debug!("bodies:");
            for body in body.iter() {
                debug!("body: {}", body);
            }
            let mut preds = body
                .iter()
                .filter_map(|x| match x {
                    CHCHead::Constraint(_) => None,
                    CHCHead::Predicate(p, l) => Some((p, l)),
                })
                .collect::<Vec<_>>();
            let (p, l) = if preds.len() == 0 {
                return Err(ResolutionError::IllegalConstraint);
            } else if preds.len() > 1 {
                let (p, l) = preds.pop().unwrap();
                if p != target {
                    return Err(ResolutionError::IllegalConstraint);
                }
                for (p2, l2) in preds {
                    if p2 != target || l2.len() != l.len() {
                        return Err(ResolutionError::IllegalConstraint);
                    }
                    for (x, y) in l.iter().zip(l2.iter()) {
                        if x != y {
                            return Err(ResolutionError::IllegalConstraint);
                        }
                    }
                }
                (p, l)
            } else {
                let (p, l) = preds.pop().unwrap();
                if p != target {
                    return Err(ResolutionError::IllegalConstraint);
                }
                (p, l)
            };
            // 3. simplify & negation
            let constrs = body
                .iter()
                .filter_map(|x| match x {
                    CHCHead::Constraint(c) => Some(c),
                    CHCHead::Predicate(_, _) => None,
                })
                .collect::<Vec<_>>();
            let mut h = head.clone();
            for c in constrs {
                match c.clone().negate() {
                    Some(c) => {
                        h = Constraint::mk_disj(c, h);
                    }
                    None => return Err(ResolutionError::IllegalConstraint),
                };
            }
            result = Constraint::mk_conj(h, result);
        }
        Ok(result)
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
    }
}

#[derive(Debug, Copy, Clone)]
pub enum ResolutionError {
    TargetVariableNotFound,
    CHCNotDeterministic,
    ContainsDisjunctions,
    IllegalConstraint,
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
                    (Err(x), Ok(c)) | (Ok(c), Err(x)) => {
                        Err(pcsp::Atom::mk_conj(x, pcsp::Atom::mk_constraint(c)))
                    }
                    (Err(x), Err(y)) => Err(pcsp::Atom::mk_conj(x, y)),
                }
            }
            pcsp::AtomKind::Disj(x, y) => {
                let x2 = simplify_atom_inner(x);
                let y2 = simplify_atom_inner(y);
                match (x2, y2) {
                    (Ok(x1), Ok(x2)) => Ok(Constraint::mk_disj(x1, x2)),
                    (Err(x), Ok(c)) | (Ok(c), Err(x)) => {
                        Err(pcsp::Atom::mk_disj(x, pcsp::Atom::mk_constraint(c)))
                    }
                    (Err(x), Err(y)) => Err(pcsp::Atom::mk_disj(x, y)),
                }
            }
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
            pcsp::AtomKind::True
            | pcsp::AtomKind::Constraint(_)
            | pcsp::AtomKind::Predicate(_, _)
            | pcsp::AtomKind::Disj(_, _) => result.push(atom.clone()),
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
        pcsp::AtomKind::Predicate(p, args) => Some(CHCHead::Predicate(*p, args.clone())),
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
                Some(head) => result.push(CHC::new(head, body.clone())),
                None => return None,
            }
        }
    }
    Some(result)
}

// solve by resolution
pub fn solve_by_resolution(
    target: Ident,
    clauses: Vec<CHC<pcsp::Atom>>,
) -> Result<Constraint, ResolutionError> {
    debug!("solve_by_resolution: target={}", target);

    let mut defs = HashMap::new();
    let mut goals = Vec::new();
    for clause in clauses {
        match &clause.head {
            CHCHead::Constraint(_) => goals.push(clause),
            CHCHead::Predicate(p, args) => {
                if defs.insert(*p, clause).is_some() {
                    return Err(ResolutionError::CHCNotDeterministic);
                }
            }
        }
    }
    let mut defs = Vec::from_iter(defs.into_iter().map(|(_, x)| x));
    while defs.len() > 0 {
        let target = defs.pop().unwrap();
        goals = goals.into_iter().map(|g| g.replace(&target)).collect();
        defs = defs.into_iter().map(|g| g.replace(&target)).collect();
    }
    for c in goals.iter() {
        debug!("- constraint: {}", c)
    }

    // subst をするべきで、
    unimplemented!()
}
pub fn simplify(
    c: &[CHC<pcsp::Atom>],
    c1: &[CHC<pcsp::Atom>],
    c2: &[CHC<pcsp::Atom>],
    l: &HashSet<Ident>,
) -> Result<Vec<CHC<pcsp::Atom>>, ResolutionError> {
    let mut defs = HashMap::new();
    let mut defs_l = HashMap::new();
    let mut goals = Vec::new();
    for clauses in [c, c1, c2].iter() {
        for clause in clauses.iter() {
            match &clause.head {
                CHCHead::Constraint(_) => goals.push(clause.clone()),
                CHCHead::Predicate(p, _) if l.contains(p) => {
                    if defs_l.insert(*p, clause.clone()).is_some() {
                        return Err(ResolutionError::CHCNotDeterministic);
                    }
                }
                CHCHead::Predicate(p, _) => {
                    if defs.insert(*p, clause.clone()).is_some() {
                        return Err(ResolutionError::CHCNotDeterministic);
                    }
                }
            }
        }
    }
    for c in goals.iter() {
        debug!("- constraint: {}", c);
    }
    for (_, c) in defs.iter() {
        debug!("- constraint: {}", c);
    }
    for (_, c) in defs_l.iter() {
        debug!("- constraint: {}", c);
    }
    debug!("-------");
    let mut defs = Vec::from_iter(defs.into_iter().map(|(_, x)| x));
    let mut defs_l = Vec::from_iter(defs_l.into_iter().map(|(_, x)| x));
    while defs.len() > 0 {
        let target = defs.pop().unwrap();
        goals = goals.into_iter().map(|g| g.replace(&target)).collect();
        defs = defs.into_iter().map(|g| g.replace(&target)).collect();
        defs_l = defs_l.into_iter().map(|g| g.replace(&target)).collect();
    }

    // merge goals and defs_l
    for def in defs_l {
        goals.push(def);
    }
    for c in goals.iter() {
        debug!("- constraint: {}", c)
    }
    Ok(goals)
}

pub fn resolve_target(
    chcs: Vec<CHC<pcsp::Atom>>,
    target: &Ident,
) -> Result<Constraint, ResolutionError> {
    let mut ret = Constraint::mk_true();
    for chc in chcs {
        let c = chc.resolve_target(target)?;
        ret = Constraint::mk_conj(c, ret);
    }
    Ok(ret)
}
