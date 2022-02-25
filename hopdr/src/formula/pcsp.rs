use std::collections::{HashMap, HashSet};
use std::fmt;

use super::{
    Bot, Constraint, Fv, Ident, Logic, Negation, Op, QuantifierKind, Rename, Subst, Top, Type,
    Variable,
};
use crate::util::P;

#[derive(Debug)]
pub enum AtomKind {
    True, // equivalent to Constraint(True). just for optimization purpose
    Constraint(Constraint),
    Predicate(Ident, Vec<Op>),
    Conj(Atom, Atom),
    Disj(Atom, Atom),
    Quantifier(QuantifierKind, Ident, Atom),
}
pub type Atom = P<AtomKind>;

// TODO: replace AtomKind::Predicate(Ident, Vec<Ident>) -> AtomKind::Predicate(Predicate)
pub struct Predicate {
    pub id: Ident,
    pub args: Vec<Ident>,
}

impl Predicate {
    pub fn fresh_pred(args: Vec<Ident>) -> Predicate {
        let id = Ident::fresh();
        Predicate { id, args }
    }
}

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
            AtomKind::Disj(x, y) => write!(f, "({} | {})", x, y),
            AtomKind::Quantifier(q, x, c) => write!(f, "{} {}. {}", q, x, c),
        }
    }
}

impl Negation for Atom {
    fn negate(&self) -> Option<Self> {
        match self.kind() {
            AtomKind::True => Some(Atom::mk_false()),
            AtomKind::Constraint(c) => c.clone().negate().map(|x| x.into()),
            AtomKind::Conj(l, r) => {
                let l = l.negate();
                let r = r.negate();
                match (l, r) {
                    (_, None) | (None, _) => None,
                    (Some(x), Some(y)) => Some(Atom::mk_disj(x, y)),
                }
            }
            AtomKind::Disj(l, r) => {
                let l = l.negate();
                let r = r.negate();
                match (l, r) {
                    (_, None) | (None, _) => None,
                    (Some(x), Some(y)) => Some(Atom::mk_conj(x, y)),
                }
            }
            AtomKind::Predicate(_, _) | AtomKind::Quantifier(_, _, _) => None,
        }
    }
}
impl Atom {
    pub fn mk_pred(ident: Ident, args: Vec<Op>) -> Atom {
        Atom::new(AtomKind::Predicate(ident, args))
    }
    pub fn contains_predicate(&self) -> bool {
        match self.kind() {
            AtomKind::True | AtomKind::Constraint(_) => false,
            AtomKind::Predicate(_, _) => true,
            AtomKind::Conj(c1, c2) | AtomKind::Disj(c1, c2) => {
                c1.contains_predicate() && c2.contains_predicate()
            }
            AtomKind::Quantifier(_, _, c) => c.contains_predicate(),
        }
    }
    pub fn extract_pred_and_constr(&self) -> Option<(Atom, Ident)> {
        match self.kind() {
            AtomKind::True | AtomKind::Constraint(_) => None,
            AtomKind::Predicate(i, _) => Some((Atom::mk_false(), *i)),
            AtomKind::Conj(x, y) | AtomKind::Conj(y, x) if x.contains_predicate() => y
                .negate()
                .map(|c2| {
                    x.extract_pred_and_constr()
                        .map(|(c, i)| (Atom::mk_disj(c, c2), i))
                })
                .flatten(),
            _ => None,
        }
    }

    pub fn mk_quantifier(q: QuantifierKind, x: Ident, c: Self) -> Atom {
        Atom::new(AtomKind::Quantifier(q, x, c))
    }

    pub fn to_constraint(&self) -> Option<Constraint> {
        match self.kind() {
            AtomKind::True => Some(Constraint::mk_true()),
            AtomKind::Constraint(c) => Some(c.clone()),
            AtomKind::Predicate(_, _) => None,
            AtomKind::Conj(x, y) => x
                .to_constraint()
                .map(|x| y.to_constraint().map(|y| Constraint::mk_conj(x, y)))
                .flatten(),
            AtomKind::Disj(x, y) => x
                .to_constraint()
                .map(|x| y.to_constraint().map(|y| Constraint::mk_disj(x, y)))
                .flatten(),
            AtomKind::Quantifier(q, x, c) => c
                .to_constraint()
                .map(|c| Constraint::mk_quantifier(*q, Variable::mk(*x, Type::mk_type_int()), c)),
        }
    }
}

impl Fv for Atom {
    type Id = Ident;
    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>) {
        match self.kind() {
            AtomKind::True => (),
            AtomKind::Constraint(c) => c.fv_with_vec(fvs),
            AtomKind::Predicate(_, l) => {
                for i in l {
                    i.fv_with_vec(fvs);
                }
            }
            AtomKind::Conj(x, y) | AtomKind::Disj(x, y) => {
                x.fv_with_vec(fvs);
                y.fv_with_vec(fvs);
            }
            AtomKind::Quantifier(_, x, c) => {
                c.fv_with_vec(fvs);
                fvs.remove(x);
            }
        }
    }
}

impl Atom {
    // auxiliary function for generating constraint
    pub fn mk_constraint(c: Constraint) -> Atom {
        Atom::new(AtomKind::Constraint(c))
    }
    pub fn assign(&self, model: &HashMap<Ident, (Vec<Ident>, Constraint)>) -> Constraint {
        match self.kind() {
            AtomKind::True => Constraint::mk_true(),
            AtomKind::Constraint(c) => c.clone(),
            AtomKind::Predicate(p, l) => match model.get(p) {
                Some((r, _c)) => {
                    debug!("assign: {:?}, {:?}", r, l);
                    unimplemented!()
                    //c.rename_idents_with_slices(r, l)
                }
                None => panic!("not found: {}", p),
            },
            AtomKind::Conj(x, y) => Constraint::mk_conj(x.assign(model), y.assign(model)),
            AtomKind::Disj(x, y) => Constraint::mk_disj(x.assign(model), y.assign(model)),
            AtomKind::Quantifier(q, x, c) => Constraint::mk_quantifier(
                *q,
                Variable::mk(*x, Type::mk_type_int()),
                c.assign(model),
            ),
        }
    }
    pub fn collect_predicates(&self, predicates: &mut HashMap<Ident, usize>) {
        match self.kind() {
            AtomKind::True | AtomKind::Constraint(_) => (),
            AtomKind::Predicate(p, l) => match predicates.insert(*p, l.len()) {
                Some(n) => debug_assert!(n == l.len()),
                None => (),
            },
            AtomKind::Conj(a1, a2) | AtomKind::Disj(a1, a2) => {
                a1.collect_predicates(predicates);
                a2.collect_predicates(predicates);
            }
            AtomKind::Quantifier(_, _, a) => a.collect_predicates(predicates),
        }
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

    fn is_true(&self) -> bool {
        match self.kind() {
            AtomKind::True => true,
            AtomKind::Constraint(x) => x.is_true(),
            AtomKind::Quantifier(QuantifierKind::Universal, _, a) => a.is_true(),
            AtomKind::Conj(a1, a2) => a1.is_true() && a2.is_true(),
            AtomKind::Disj(a1, a2) => a1.is_true() || a2.is_true(),
            _ => false,
        }
    }
}

impl Bot for Atom {
    fn mk_false() -> Self {
        Atom::new(AtomKind::Constraint(Constraint::mk_false()))
    }

    fn is_false(&self) -> bool {
        match self.kind() {
            AtomKind::Constraint(x) => x.is_false(),
            AtomKind::Quantifier(QuantifierKind::Universal, _, a) => a.is_false(),
            AtomKind::Conj(a1, a2) => a1.is_false() || a2.is_false(),
            AtomKind::Disj(a1, a2) => a1.is_false() && a2.is_false(),
            _ => false,
        }
    }
}

impl Logic for Atom {
    fn is_conj<'a>(&'a self) -> Option<(&'a Atom, &'a Atom)> {
        match self.kind() {
            AtomKind::Conj(x, y) => Some((x, y)),
            _ => None,
        }
    }
    fn mk_conj(x: Self, y: Self) -> Atom {
        use AtomKind::*;
        if x.is_false() || y.is_false() {
            Atom::mk_false()
        } else if x.is_true() {
            y
        } else if y.is_true() {
            x
        } else {
            Atom::new(Conj(x, y))
        }
    }
    fn is_disj<'a>(&'a self) -> Option<(&'a Atom, &'a Atom)> {
        match self.kind() {
            AtomKind::Disj(x, y) => Some((x, y)),
            _ => None,
        }
    }
    fn mk_disj(x: Self, y: Self) -> Atom {
        if x.is_true() || y.is_true() {
            Atom::mk_true()
        } else if x.is_false() {
            y
        } else if y.is_false() {
            x
        } else {
            Atom::new(AtomKind::Disj(x, y))
        }
    }
}

impl Subst for Atom {
    type Item = super::Op;
    type Id = Ident;
    fn subst(&self, x: &Ident, v: &super::Op) -> Self {
        match self.kind() {
            AtomKind::True => self.clone(),
            AtomKind::Constraint(c) => Atom::mk_constraint(c.subst(x, v)),
            AtomKind::Predicate(k, args) => {
                let _target = match v.kind() {
                    super::OpExpr::Var(v) => *v,
                    _ => unimplemented!("not implemented"),
                };
                let new_ops = args.iter().map(|op| op.subst(x, v)).collect();
                Atom::mk_pred(*k, new_ops)
            }
            AtomKind::Conj(r, l) => Atom::mk_conj(r.subst(x, v), l.subst(x, v)),
            AtomKind::Disj(r, l) => Atom::mk_disj(r.subst(x, v), l.subst(x, v)),
            // assumption: vars are different each other ?
            AtomKind::Quantifier(q, var, cstr) => Atom::mk_quantifier(*q, *var, cstr.subst(x, v)),
        }
    }
}

impl Rename for Atom {
    fn rename(&self, x: &Ident, y: &Ident) -> Self {
        match self.kind() {
            AtomKind::True => self.clone(),
            AtomKind::Constraint(c) => Atom::mk_constraint(c.rename(x, y)),
            AtomKind::Predicate(_p, _args) => {
                unimplemented!()
                //let new_args = Ident::rename_idents(args, x, y);
                //Atom::mk_pred(*p, new_args)
            }
            AtomKind::Conj(a, b) => Atom::mk_conj(a.rename(x, y), b.rename(x, y)),
            AtomKind::Disj(a, b) => Atom::mk_disj(a.rename(x, y), b.rename(x, y)),
            AtomKind::Quantifier(q, z, c) => Atom::mk_quantifier(*q, *z, c.rename(x, y)),
        }
    }
}

#[derive(Debug)]
pub struct PCSP<A> {
    pub body: A,
    pub head: A,
}

impl<A> PCSP<A> {
    pub fn new(body: A, head: A) -> PCSP<A> {
        PCSP { body, head }
    }
}

impl PCSP<Constraint> {
    pub fn to_constraint(&self) -> Option<Constraint> {
        Constraint::mk_arrow(self.body.clone(), self.head.clone())
    }
}

impl<A: fmt::Display> fmt::Display for PCSP<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} -> {}", self.body, self.head)
    }
}
