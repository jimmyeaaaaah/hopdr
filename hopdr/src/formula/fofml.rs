use std::collections::{HashMap, HashSet};
use std::fmt;

use super::chc;
use super::pcsp;
use super::{
    hes, Arithmetic, Bot, Constraint, ConstraintBase, FirstOrderLogic, Fv, Ident, Logic, Negation,
    Op, OpKind, PredKind, QuantifierKind, Rename, Subst, Top, Type, Variable,
};
use crate::solver;
use crate::solver::smt;
use crate::util::P;

#[derive(Debug, PartialEq)]
pub enum AtomKind<Op> {
    True, // equivalent to Constraint(True). just for optimization purpose
    Constraint(ConstraintBase<Op>),
    Predicate(Ident, Vec<Op>),
    Conj(AtomBase<Op>, AtomBase<Op>),
    Disj(AtomBase<Op>, AtomBase<Op>),
    Not(AtomBase<Op>),
    Quantifier(QuantifierKind, Ident, AtomBase<Op>),
}
pub type AtomBase<Op> = P<AtomKind<Op>>;
pub type Atom = AtomBase<Op>;

impl<Op: Arithmetic> fmt::Display for AtomBase<Op> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            AtomKind::True => write!(f, "true"),
            AtomKind::Constraint(c) => write!(f, "({})", c),
            AtomKind::Predicate(id, ops) => {
                write!(f, "{}(", id)?;
                for op in ops.iter() {
                    write!(f, "{},", op)?;
                }
                write!(f, ")")
            }
            AtomKind::Conj(x, y) => write!(f, "({} & {})", x, y),
            AtomKind::Disj(x, y) => write!(f, "({} | {})", x, y),
            AtomKind::Not(x) => write!(f, "not({})", x),
            AtomKind::Quantifier(q, x, c) => write!(f, "{} {}. {}", q, x, c),
        }
    }
}

impl<Op: Arithmetic> Fv for AtomBase<Op> {
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

impl<O: Arithmetic> Rename for AtomBase<O> {
    fn rename(&self, x: &Ident, y: &Ident) -> Self {
        match self.kind() {
            AtomKind::True => self.clone(),
            AtomKind::Constraint(c) => AtomBase::mk_constraint(c.rename(x, y)),
            AtomKind::Predicate(p, l) => {
                let l2: Vec<O> = l.iter().map(|id| id.rename(x, y)).collect();
                AtomBase::mk_pred(*p, l2)
            }
            AtomKind::Conj(a1, a2) => AtomBase::mk_conj(a1.rename(x, y), a2.rename(x, y)),
            AtomKind::Disj(a1, a2) => AtomBase::mk_disj(a1.rename(x, y), a2.rename(x, y)),
            AtomKind::Not(a) => AtomBase::mk_not(a.rename(x, y)),
            AtomKind::Quantifier(q, x, a) => AtomBase::mk_quantifier(*q, *x, a.rename(x, y)),
        }
    }
}

impl<O: Arithmetic> From<ConstraintBase<O>> for AtomBase<O> {
    fn from(from: ConstraintBase<O>) -> AtomBase<O> {
        AtomBase::mk_constraint(from)
    }
}
impl<O: Arithmetic> From<AtomBase<O>> for ConstraintBase<O> {
    fn from(from: AtomBase<O>) -> ConstraintBase<O> {
        match from.kind() {
            AtomKind::True => ConstraintBase::mk_true(),
            AtomKind::Constraint(c) => c.clone(),
            AtomKind::Conj(a1, a2) => {
                let c1 = a1.clone().into();
                let c2 = a2.clone().into();
                ConstraintBase::mk_conj(c1, c2)
            }
            AtomKind::Disj(a1, a2) => {
                let c1 = a1.clone().into();
                let c2 = a2.clone().into();
                ConstraintBase::mk_disj(c1, c2)
            }
            AtomKind::Not(a) => {
                let c: ConstraintBase<O> = a.clone().into();
                c.negate().unwrap()
            }
            AtomKind::Quantifier(q, x, a) => {
                let c: ConstraintBase<O> = a.clone().into();
                ConstraintBase::mk_quantifier_int(*q, *x, c)
            }
            AtomKind::Predicate(_, _) => panic!("program error"),
        }
    }
}

impl From<pcsp::Atom> for AtomBase<Op> {
    fn from(from: pcsp::Atom) -> AtomBase<Op> {
        match from.kind() {
            pcsp::AtomKind::True => AtomBase::mk_true(),
            pcsp::AtomKind::Constraint(c) => AtomBase::mk_constraint(c.clone().into()),
            pcsp::AtomKind::Predicate(p, l) => AtomBase::mk_pred(*p, l.clone()),
            pcsp::AtomKind::Conj(x, y) => AtomBase::mk_conj(x.clone().into(), y.clone().into()),
            pcsp::AtomKind::Disj(x, y) => AtomBase::mk_disj(x.clone().into(), y.clone().into()),
            pcsp::AtomKind::Quantifier(q, x, c) if *q == QuantifierKind::Universal => {
                AtomBase::mk_univq(*x, c.clone().into())
            }
            pcsp::AtomKind::Quantifier(q, x, c) if *q == QuantifierKind::Existential => {
                AtomBase::mk_existq(*x, c.clone().into())
            }
            pcsp::AtomKind::Quantifier(_q, _x, _c) => panic!("fail"),
        }
    }
}
impl From<AtomBase<Op>> for pcsp::Atom {
    fn from(from: AtomBase<Op>) -> pcsp::Atom {
        match from.kind() {
            AtomKind::True => pcsp::Atom::mk_true(),
            AtomKind::Constraint(c) => pcsp::Atom::mk_constraint(c.clone()),
            AtomKind::Conj(a1, a2) => {
                let c1 = a1.clone().into();
                let c2 = a2.clone().into();
                pcsp::Atom::mk_conj(c1, c2)
            }
            AtomKind::Disj(a1, a2) => {
                let c1 = a1.clone().into();
                let c2 = a2.clone().into();
                pcsp::Atom::mk_disj(c1, c2)
            }
            AtomKind::Not(a) => {
                let c: pcsp::Atom = a.clone().into();
                c.negate().unwrap()
            }
            AtomKind::Quantifier(q, x, a) => {
                let c: pcsp::Atom = a.clone().into();
                pcsp::Atom::mk_quantifier(*q, *x, c)
            }
            AtomKind::Predicate(p, l) => pcsp::Atom::mk_pred(p.clone(), l.clone()),
        }
    }
}

impl From<pcsp::PCSP<pcsp::Atom>> for Atom {
    fn from(from: pcsp::PCSP<pcsp::Atom>) -> Atom {
        AtomBase::mk_disj(AtomBase::mk_not(from.body.into()), from.head.into())
    }
}

impl<O: Arithmetic> From<pcsp::PCSP<AtomBase<O>>> for AtomBase<O> {
    fn from(from: pcsp::PCSP<AtomBase<O>>) -> AtomBase<O> {
        AtomBase::mk_disj(AtomBase::mk_not(from.body), from.head)
    }
}

impl<O: Arithmetic> Top for AtomBase<O> {
    fn mk_true() -> Self {
        AtomBase::new(AtomKind::True)
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

impl<O: Arithmetic> Bot for AtomBase<O> {
    fn mk_false() -> Self {
        AtomBase::new(AtomKind::Constraint(ConstraintBase::mk_false()))
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

impl<O: Arithmetic> Logic for AtomBase<O> {
    fn is_conj<'a>(&'a self) -> Option<(&'a Self, &'a Self)> {
        match self.kind() {
            AtomKind::Conj(x, y) => Some((x, y)),
            _ => None,
        }
    }
    fn mk_conj(x: Self, y: Self) -> Self {
        use AtomKind::*;
        if x.is_false() || y.is_false() {
            AtomBase::mk_false()
        } else if x.is_true() {
            y
        } else if y.is_true() {
            x
        } else {
            AtomBase::new(Conj(x, y))
        }
    }
    fn is_disj<'a>(&'a self) -> Option<(&'a Self, &'a Self)> {
        match self.kind() {
            AtomKind::Disj(x, y) => Some((x, y)),
            _ => None,
        }
    }
    fn mk_disj(x: Self, y: Self) -> Self {
        if x.is_true() || y.is_true() {
            AtomBase::mk_true()
        } else if x.is_false() {
            y
        } else if y.is_false() {
            x
        } else {
            AtomBase::new(AtomKind::Disj(x, y))
        }
    }
}

// For AtomBase, negation always succeeds
impl<O: Arithmetic> Negation for AtomBase<O> {
    fn negate(&self) -> Option<Self> {
        match self.kind() {
            AtomKind::True => Some(AtomBase::mk_false()),
            AtomKind::Constraint(c) => c.negate().map(|c| AtomBase::mk_constraint(c)),
            AtomKind::Predicate(_, _) => Some(AtomBase::mk_not(self.clone())),
            AtomKind::Conj(c1, c2) => c1
                .negate()
                .map(|c1| c2.negate().map(|c2| AtomBase::mk_disj(c1, c2)))
                .flatten(),
            AtomKind::Disj(c1, c2) => c1
                .negate()
                .map(|c1| c2.negate().map(|c2| AtomBase::mk_conj(c1, c2)))
                .flatten(),
            AtomKind::Not(a) => Some(a.clone()),
            AtomKind::Quantifier(q, x, a) => {
                let q = q.negate();
                a.negate().map(|a| AtomBase::mk_quantifier(q, *x, a))
            }
        }
    }
}

impl<O: Arithmetic> Subst for AtomBase<O> {
    type Item = O;
    type Id = Ident;
    fn subst(&self, x: &Ident, v: &O) -> Self {
        match self.kind() {
            AtomKind::True => self.clone(),
            AtomKind::Constraint(c) => AtomBase::mk_constraint(c.subst(x, v)),
            AtomKind::Predicate(p, l) => {
                let l2: Vec<O> = l.iter().map(|id| id.subst(x, v)).collect();
                AtomBase::mk_pred(*p, l2)
            }
            AtomKind::Conj(a1, a2) => {
                let a1 = a1.subst(x, v);
                let a2 = a2.subst(x, v);
                AtomBase::mk_conj(a1, a2)
            }
            AtomKind::Disj(a1, a2) => {
                let a1 = a1.subst(x, v);
                let a2 = a2.subst(x, v);
                AtomBase::mk_disj(a1, a2)
            }
            AtomKind::Not(a) => {
                let a = a.subst(x, v);
                AtomBase::mk_not(a)
            }
            AtomKind::Quantifier(q, y, a) => {
                if x == y {
                    AtomBase::mk_quantifier(*q, *y, a.clone())
                } else {
                    AtomBase::mk_quantifier(*q, *y, a.subst(x, v))
                }
            }
        }
    }
}
impl<O: Arithmetic> FirstOrderLogic for AtomBase<O> {
    fn mk_quantifier_int(q: QuantifierKind, x: Ident, c: Self) -> Self {
        AtomBase::mk_quantifier(q, x, c)
    }
}

impl From<Constraint> for hes::Goal<AtomBase<Op>> {
    fn from(c: Constraint) -> Self {
        let a: AtomBase<Op> = c.into();
        a.into()
    }
}

impl AtomBase<Op> {
    fn replace_by_template(&self, map: &HashMap<Ident, Template>) -> Constraint {
        match self.kind() {
            AtomKind::True => ConstraintBase::mk_true(),
            AtomKind::Constraint(c) => c.clone(),
            AtomKind::Conj(x, y) => {
                ConstraintBase::mk_conj(x.replace_by_template(map), y.replace_by_template(map))
            }
            AtomKind::Disj(x, y) => {
                ConstraintBase::mk_disj(x.replace_by_template(map), y.replace_by_template(map))
            }
            AtomKind::Not(c) => c.replace_by_template(map).negate().unwrap(),
            AtomKind::Quantifier(q, v, x) => {
                ConstraintBase::mk_quantifier_int(*q, *v, x.replace_by_template(map))
            }
            AtomKind::Predicate(p, l) => map.get(p).unwrap().apply(l),
        }
    }
    /// check the satisfiability of the given fofml formula
    pub fn check_satisfiability(&self) -> Option<HashMap<Ident, (Vec<Ident>, Constraint)>> {
        fn collect_templates<O>(
            a: &AtomBase<O>,
            map: &mut HashMap<Ident, Template>,
            fvs: &mut HashSet<Ident>,
        ) {
            match a.kind() {
                AtomKind::True | AtomKind::Constraint(_) => (),
                AtomKind::Predicate(p, l) => match map.get(p) {
                    Some(_) => (),
                    None => {
                        let t = Template::new(l.len());
                        for i in t.coef_iter() {
                            fvs.insert(*i);
                        }
                        map.insert(*p, t);
                    }
                },
                AtomKind::Conj(a1, a2) | AtomKind::Disj(a1, a2) => {
                    collect_templates(a1, map, fvs);
                    collect_templates(a2, map, fvs);
                }
                AtomKind::Not(a) | AtomKind::Quantifier(_, _, a) => collect_templates(a, map, fvs),
            }
        }
        let mut templates = HashMap::new();
        let mut fvs = HashSet::new();
        collect_templates(self, &mut templates, &mut fvs);
        let c = self.replace_by_template(&templates);
        // check satisfiability of c and get model
        let mut solver = smt::default_solver();
        let model = match solver.solve_with_model(&c, &HashSet::new(), &fvs) {
            Ok(model) => model,
            Err(solver::SolverResult::Unsat) => {
                // when c is unsat, returns None
                return None;
            }
            _ => panic!("program error"),
        };
        // generate map predicate -> constraints
        let h = templates
            .into_iter()
            .map(|(p, t)| (p, t.to_constraint(&model)))
            .collect();
        Some(h)
    }

    pub fn to_chcs_or_pcsps(
        &self,
    ) -> either::Either<Vec<chc::CHC<chc::Atom, Constraint>>, Vec<pcsp::PCSP<pcsp::Atom>>> {
        let constraint = self.reduce_not();
        let (quantifiers, pnf) = constraint.prenex_normal_form_raw(&mut HashSet::new());
        let mut ienv = HashSet::new();
        for (q, x) in quantifiers {
            match q {
                QuantifierKind::Universal => {
                    ienv.insert(x);
                }
                QuantifierKind::Existential => panic!("program error"),
            }
        }
        let cnf = pnf.to_cnf();
        let mut is_chc = true;
        let mut clauses = Vec::new();
        crate::title!("PNF");
        debug!("{}", pnf);
        crate::title!("CNF");
        for c in cnf.iter() {
            debug!("{}", c);
        }

        for c in cnf {
            let dnf = c.to_dnf();
            let mut body = pcsp::Atom::mk_true();
            let mut head = pcsp::Atom::mk_false();
            for atom in dnf {
                match atom.kind() {
                    AtomKind::True | AtomKind::Constraint(_) => {
                        body = pcsp::Atom::mk_conj(atom.negate().into(), body);
                    }
                    AtomKind::Predicate(_, _) => {
                        if !head.is_false() {
                            is_chc = false;
                        }
                        head = pcsp::Atom::mk_disj(atom.clone().into(), head);
                    }
                    AtomKind::Not(a) => {
                        match a.kind() {
                            AtomKind::Predicate(_, _) => {
                                body = pcsp::Atom::mk_conj(a.clone().into(), body)
                            }
                            _ => debug_assert!(false),
                        };
                    }
                    AtomKind::Quantifier(_, _, _) | AtomKind::Conj(_, _) | AtomKind::Disj(_, _) => {
                        panic!("program error")
                    }
                }
            }
            clauses.push(pcsp::PCSP::new(body, head));
        }
        if is_chc {
            let clauses = clauses.into_iter().map(|c| {
                let head = match c.head.kind() {
                    pcsp::AtomKind::Predicate(p, l) => {
                        chc::CHCHead::Predicate(chc::Atom::new(*p, l.clone()))
                    }
                    _ if c.head.is_false() => chc::CHCHead::Constraint(Constraint::mk_false()),
                    _ => panic!("program error"),
                };
                (c.body, head)
            });
            let clauses = chc::generate_chcs(clauses);
            //debug!("{}", "[generated CHC]".bold());
            crate::title!("generated CHC");
            for c in clauses.iter() {
                debug!("{}", c);
            }
            either::Left(clauses)
        } else {
            either::Right(clauses)
        }
    }
}
impl<O: Arithmetic> AtomBase<O> {
    pub fn mk_false() -> AtomBase<O> {
        AtomBase::mk_constraint(ConstraintBase::mk_false())
    }
    pub fn mk_not(x: Self) -> AtomBase<O> {
        AtomBase::new(AtomKind::Not(x))
    }
    //pub fn mk_var(x: Ident) -> AtomBase {
    //    AtomBase::new(AtomBaseKind::)
    //}
    // auxiliary function for generating constraint
    pub fn mk_constraint(c: ConstraintBase<O>) -> AtomBase<O> {
        AtomBase::new(AtomKind::Constraint(c))
    }
    pub fn mk_pred(p: Ident, l: impl Into<Vec<O>>) -> AtomBase<O> {
        AtomBase::new(AtomKind::Predicate(p, l.into()))
    }
    pub fn mk_fresh_pred(l: Vec<O>) -> AtomBase<O> {
        let p = Ident::fresh();
        AtomBase::mk_pred(p, l)
    }
    pub fn mk_quantifier(q: QuantifierKind, x: Ident, c: AtomBase<O>) -> AtomBase<O> {
        AtomBase::new(AtomKind::Quantifier(q, x, c))
    }
    pub fn mk_univq(x: Ident, c: AtomBase<O>) -> AtomBase<O> {
        AtomBase::mk_quantifier(QuantifierKind::Universal, x, c)
    }
    pub fn mk_existq(x: Ident, c: Self) -> Self {
        AtomBase::mk_quantifier(QuantifierKind::Existential, x, c)
    }
    pub fn negate(self) -> Self {
        AtomBase::mk_not(self)
    }
    pub fn integer_fv(&self) -> HashSet<Ident> {
        fn inner<O: Arithmetic>(atom: &AtomBase<O>, fvs: &mut HashSet<Ident>) {
            match atom.kind() {
                AtomKind::True => (),
                AtomKind::Constraint(c) => {
                    c.fv_with_vec(fvs);
                }
                AtomKind::Predicate(_, args) => {
                    for a in args {
                        a.fv_with_vec(fvs);
                    }
                }
                AtomKind::Conj(x, y) | AtomKind::Disj(x, y) => {
                    inner(x, fvs);
                    inner(y, fvs);
                }
                AtomKind::Quantifier(_, x, c) => {
                    inner(c, fvs);
                    fvs.remove(x);
                }
                AtomKind::Not(x) => inner(x, fvs),
            }
        }
        let mut fvs = HashSet::new();
        inner(self, &mut fvs);
        fvs
    }
    pub fn to_constraint(&self) -> Option<ConstraintBase<O>> {
        match self.kind() {
            AtomKind::True => Some(ConstraintBase::mk_true()),
            AtomKind::Constraint(c) => Some(c.clone()),
            AtomKind::Predicate(_, _) => None,
            AtomKind::Conj(x, y) => x
                .to_constraint()
                .map(|x| y.to_constraint().map(|y| ConstraintBase::mk_conj(x, y)))
                .flatten(),
            AtomKind::Disj(x, y) => x
                .to_constraint()
                .map(|x| y.to_constraint().map(|y| ConstraintBase::mk_disj(x, y)))
                .flatten(),
            AtomKind::Quantifier(q, x, c) => c.to_constraint().map(|c| {
                ConstraintBase::mk_quantifier(*q, Variable::mk(*x, Type::mk_type_int()), c)
            }),
            AtomKind::Not(x) => x.to_constraint().map(|x| x.negate()).flatten(),
        }
    }
    pub fn assign(
        &self,
        model: &HashMap<Ident, (Vec<Ident>, ConstraintBase<O>)>,
    ) -> ConstraintBase<O> {
        match self.kind() {
            AtomKind::True => ConstraintBase::mk_true(),
            AtomKind::Constraint(c) => c.clone(),
            AtomKind::Predicate(p, l) => match model.get(p) {
                Some((r, c)) => {
                    c.subst_multi(r.iter().zip(l.iter()).map(|(x, y)| (x.clone(), y.clone())))
                }
                None => {
                    // TODO: is it true?
                    // there is no entry in p
                    ConstraintBase::mk_false()
                }
            },
            AtomKind::Conj(x, y) => ConstraintBase::mk_conj(x.assign(model), y.assign(model)),
            AtomKind::Disj(x, y) => ConstraintBase::mk_disj(x.assign(model), y.assign(model)),
            AtomKind::Quantifier(q, x, c) => ConstraintBase::mk_quantifier(
                *q,
                Variable::mk(*x, Type::mk_type_int()),
                c.assign(model),
            ),
            AtomKind::Not(x) => x.assign(&model).negate().unwrap(),
        }
    }
    // reduces AtomBase a to a' where all the occurences of not
    // are of the form `Not(Predicate(...))`.
    pub fn reduce_not(&self) -> AtomBase<O> {
        fn negate<O: Arithmetic>(x: &AtomBase<O>) -> AtomBase<O> {
            match x.kind() {
                AtomKind::True => AtomBase::mk_false(),
                AtomKind::Constraint(c) => AtomBase::mk_constraint(c.negate().unwrap()),
                AtomKind::Predicate(_, _) => AtomBase::mk_not(x.clone()),
                AtomKind::Conj(a1, a2) => {
                    let a1 = negate(a1);
                    let a2 = negate(a2);
                    AtomBase::mk_disj(a1, a2)
                }
                AtomKind::Disj(a1, a2) => {
                    let a1 = negate(a1);
                    let a2 = negate(a2);
                    AtomBase::mk_conj(a1, a2)
                }
                AtomKind::Quantifier(q, x, c) => AtomBase::mk_quantifier(q.negate(), *x, negate(c)),
                AtomKind::Not(x) => x.clone(),
            }
        }
        match self.kind() {
            AtomKind::True | AtomKind::Constraint(_) | AtomKind::Predicate(_, _) => self.clone(),
            AtomKind::Conj(a1, a2) => {
                let a1 = a1.reduce_not();
                let a2 = a2.reduce_not();
                AtomBase::mk_conj(a1, a2)
            }
            AtomKind::Disj(a1, a2) => {
                let a1 = a1.reduce_not();
                let a2 = a2.reduce_not();
                AtomBase::mk_disj(a1, a2)
            }
            AtomKind::Quantifier(q, x, c) => AtomBase::mk_quantifier(*q, *x, c.reduce_not()),
            AtomKind::Not(x) => negate(x),
        }
    }
    // Assumption: Not is already reduced by `reduce_not`
    pub fn prenex_normal_form_raw(
        self: &AtomBase<O>,
        env: &mut HashSet<Ident>,
    ) -> (Vec<(QuantifierKind, Ident)>, AtomBase<O>) {
        match self.kind() {
            AtomKind::True | AtomKind::Constraint(_) | AtomKind::Predicate(_, _) => {
                (Vec::new(), self.clone())
            }
            AtomKind::Conj(a1, a2) => {
                let (mut v1, a1) = a1.prenex_normal_form_raw(env);
                let (mut v2, a2) = a2.prenex_normal_form_raw(env);
                v1.append(&mut v2);
                (v1, AtomBase::mk_conj(a1, a2))
            }
            AtomKind::Disj(a1, a2) => {
                let (mut v1, a1) = a1.prenex_normal_form_raw(env);
                let (mut v2, a2) = a2.prenex_normal_form_raw(env);
                v1.append(&mut v2);
                (v1, AtomBase::mk_disj(a1, a2))
            }
            AtomKind::Quantifier(q, x, a) => {
                let (x, a) = if env.contains(x) {
                    // if env already contains the ident to be bound,
                    // we rename it to a fresh one.
                    let x2 = Ident::fresh();
                    let a = a.rename(x, &x2);
                    (x2, a)
                } else {
                    (*x, a.clone())
                };
                env.insert(x);
                let (mut v, a) = a.prenex_normal_form_raw(env);
                debug_assert!(v.iter().find(|(_, y)| { x == *y }).is_none());
                v.push((*q, x));
                env.remove(&x);
                (v, a)
            }
            AtomKind::Not(x) => {
                // Not is already reduced, so x must be Predicate
                // this match is just to make sure this.
                match x.kind() {
                    AtomKind::Predicate(_, _) => (Vec::new(), self.clone()),
                    _ => panic!("program error"),
                }
            }
        }
    }
    // Assumption: Not is already reduced by `reduce_not`
    pub fn prenex_normal_form(&self) -> AtomBase<O> {
        let (v, mut a) = self.prenex_normal_form_raw(&mut HashSet::new());
        for (q, x) in v.into_iter().rev() {
            a = AtomBase::mk_quantifier(q, x, a);
        }
        a
    }
}

trait TemplateKind {
    fn apply(&self, args: &[Op]) -> Constraint;
    fn instantiate(&self, args: &[Op], model: &smt::Model) -> Constraint;
    fn coefs<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Ident> + 'a>;
}

struct Linear {
    coefs: Vec<Ident>,
    constant: Ident,
    predicate: PredKind,
}

impl Linear {
    fn to_constraint(
        &self,
        coefs: impl Iterator<Item = Op>,
        args: &[Ident],
        constant: Op,
    ) -> Constraint {
        let o = gen_linear_sum(coefs, args);
        let o = Op::mk_bin_op(OpKind::Add, o, constant);
        Constraint::mk_pred(self.predicate, vec![o, Op::mk_const(0)])
    }
}

impl Linear {
    fn new(nargs: usize, predicate: PredKind) -> Linear {
        let mut coefs = Vec::new();
        for _ in 0..nargs {
            coefs.push(Ident::fresh());
        }
        let constant = Ident::fresh();
        Linear {
            coefs,
            constant,
            predicate,
        }
    }
}

#[allow(dead_code)]
fn new_eq_template(nargs: usize) -> Linear {
    Linear::new(nargs, PredKind::Eq)
}

fn new_gt_template(nargs: usize) -> Linear {
    Linear::new(nargs, PredKind::Gt)
}

impl TemplateKind for Linear {
    fn apply(&self, arg_ops: &[Op]) -> Constraint {
        let coefs = self.coefs.iter().map(|x| Op::mk_var(*x));
        let args: Vec<Ident> = arg_ops.iter().map(|_| Ident::fresh()).collect();
        let constant = Op::mk_var(self.constant);
        let c = self.to_constraint(coefs, &args, constant);
        c.subst_multi(
            args.iter()
                .zip(arg_ops.iter())
                .map(|(x, y)| (x.clone(), y.clone())),
        )
    }

    fn instantiate(&self, arg_ops: &[Op], model: &smt::Model) -> Constraint {
        let coefs = self.coefs.iter().map(|x| {
            let v = model.get(x).unwrap();
            Op::mk_const(v)
        });
        let args: Vec<Ident> = arg_ops.iter().map(|_| Ident::fresh()).collect();
        let constant = Op::mk_const(model.get(&self.constant).unwrap());
        let c = self.to_constraint(coefs, &args, constant);
        c.subst_multi(
            args.iter()
                .zip(arg_ops.iter())
                .map(|(x, y)| (x.clone(), y.clone())),
        )
    }

    fn coefs<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Ident> + 'a> {
        Box::new(self.coefs.iter().chain(vec![&self.constant]))
    }
}

///
/// P(x1, x2) -> a1 x1 + a2 x2 + b >= 0
pub struct Template<'a> {
    // information of the original predicate
    nargs: usize,
    template_kinds: Vec<Box<dyn TemplateKind + 'a>>,
}

fn gen_linear_sum(coefs: impl IntoIterator<Item = Op>, args: &[Ident]) -> Op {
    if !args.is_empty() {
        let mut coefs = coefs.into_iter();
        let c = coefs.next().unwrap();
        let mut cur = Op::mk_bin_op(OpKind::Mul, c, args[0].clone().into());
        for (id, coef) in args[1..].iter().zip(coefs) {
            let id = id.clone();
            let term = Op::mk_bin_op(OpKind::Mul, coef, id.into());
            cur = Op::mk_bin_op(OpKind::Add, cur, term)
        }
        cur
    } else {
        Op::mk_const(0)
    }
}

impl<'a> Template<'a> {
    fn new(nargs: usize) -> Template<'a> {
        let mut template_kinds: Vec<Box<dyn TemplateKind>> = Vec::new();
        // Here, the list of templates
        //// 1. ax + by + c = d
        //template_kinds.push(Box::new(new_eq_template(nargs)));
        // 1. ax + by + c > d
        template_kinds.push(Box::new(new_gt_template(nargs)));
        Template {
            nargs,
            template_kinds,
        }
    }

    fn apply(&self, args: &[Op]) -> Constraint {
        let mut c = Constraint::mk_true();
        for t in self.template_kinds.iter() {
            c = Constraint::mk_conj(t.apply(args), c);
        }
        c
    }

    fn coef_iter(&'a self) -> impl Iterator<Item = &'a Ident> {
        self.template_kinds.iter().map(|x| x.coefs()).flatten()
    }

    fn to_constraint(self, model: &smt::Model) -> (Vec<Ident>, Constraint) {
        let args = (0..self.nargs)
            .into_iter()
            .map(|_| Ident::fresh())
            .collect::<Vec<_>>();
        let op_args: Vec<Op> = args.iter().map(|x| x.clone().into()).collect();
        let mut c = Constraint::mk_true();
        for t in self.template_kinds.iter() {
            c = Constraint::mk_conj(t.instantiate(&op_args, model), c);
        }
        (args, c)
    }
}
