use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;
use std::vec;

use crate::formula;
use crate::formula::Type;
use crate::pdr::rtype::Refinement;
use crate::util::Pretty;

use super::pcsp;
use super::Bot;
use super::Negation;
use super::PredKind;
use super::Subst;
use super::{Constraint, Fv, Ident, Logic, Op, Rename, Top, Variable};

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
pub enum CHCHead<A, C> {
    Constraint(C),
    Predicate(A),
}

#[derive(Debug, Clone)]
pub struct CHCBody<A, C> {
    pub predicates: Vec<A>,
    pub constraint: C,
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.pretty_display())
    }
}

impl<A: fmt::Display, C: fmt::Display> fmt::Display for CHCHead<A, C> {
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

impl<A, C: TConstraint> CHCHead<A, C> {
    pub fn mk_true() -> CHCHead<A, C> {
        CHCHead::Constraint(C::mk_true())
    }
    pub fn mk_constraint(c: C) -> CHCHead<A, C> {
        CHCHead::Constraint(c)
    }
}
impl<C> CHCHead<Atom, C> {
    pub fn mk_predicate(predicate: Ident, args: Vec<Op>) -> CHCHead<Atom, C> {
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
impl<A: Rename, C: Rename> Rename for CHCHead<A, C> {
    fn rename(&self, x: &Ident, y: &Ident) -> Self {
        match self {
            CHCHead::Constraint(c) => CHCHead::Constraint(c.rename(x, y)),
            CHCHead::Predicate(a) => CHCHead::Predicate(a.rename(x, y)),
        }
    }
}
impl<A: Rename, C: Rename> Rename for CHCBody<A, C> {
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
pub struct CHC<A, C> {
    pub body: CHCBody<A, C>,
    pub head: CHCHead<A, C>,
}

impl<A: Refinement, C: Refinement> Rename for CHC<A, C> {
    fn rename(&self, x: &Ident, y: &Ident) -> Self {
        let body = self.body.rename(x, y);
        let head = self.head.rename(x, y);
        CHC { head, body }
    }
}

impl<A: Rename + Fv, C: Rename + Fv> CHCBody<A, C> {}

impl<A: Rename + Fv<Id = Ident> + Clone, C: Rename + Fv<Id = Ident> + Clone> CHC<A, C> {
    pub fn fresh_variables(&self) -> CHC<A, C> {
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

impl<A: Fv<Id = Ident>, C: Fv<Id = Ident>> Fv for CHCHead<A, C> {
    type Id = Ident;

    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>) {
        match &self {
            CHCHead::Constraint(c) => c.fv_with_vec(fvs),
            CHCHead::Predicate(a) => a.fv_with_vec(fvs),
        }
    }
}

impl<A: Fv<Id = Ident>, C: Fv<Id = Ident>> Fv for CHCBody<A, C> {
    type Id = Ident;

    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>) {
        for b in self.predicates.iter() {
            b.fv_with_vec(fvs);
        }
        self.constraint.fv_with_vec(fvs);
    }
}

impl<A: Fv<Id = Ident>, C: Fv<Id = Ident>> Fv for CHC<A, C> {
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

pub(crate) fn body_iter(body: pcsp::Atom) -> impl Iterator<Item = CHCBody<Atom, Constraint>> {
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
    pairs: impl Iterator<Item = (pcsp::Atom, CHCHead<Atom, Constraint>)>,
) -> Vec<CHC<Atom, Constraint>> {
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

impl From<CHCBody<Atom, Constraint>> for pcsp::Atom {
    fn from(body: CHCBody<Atom, Constraint>) -> Self {
        let mut a = pcsp::Atom::mk_true();
        for b in body.predicates {
            let b = pcsp::Atom::mk_pred(b.predicate, b.args);
            a = pcsp::Atom::mk_conj(a, b);
        }
        pcsp::Atom::mk_conj(pcsp::Atom::mk_constraint(body.constraint), a)
    }
}
impl From<CHCBody<Atom, pcsp::Atom>> for pcsp::Atom {
    fn from(body: CHCBody<Atom, pcsp::Atom>) -> Self {
        let mut a = pcsp::Atom::mk_true();
        for b in body.predicates {
            let b = pcsp::Atom::mk_pred(b.predicate, b.args);
            a = pcsp::Atom::mk_conj(a, b);
        }
        pcsp::Atom::mk_conj(body.constraint, a)
    }
}

impl<A: fmt::Display, C: fmt::Display + Top> fmt::Display for CHCBody<A, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        if !self.constraint.is_true() {
            first = false;
            write!(f, "{}", self.constraint)?;
        }
        for b in &self.predicates {
            if !first {
                write!(f, " ∧ ")?;
            } else {
                first = false;
            }
            write!(f, "{}", b)?;
        }
        Ok(())
    }
}
impl<A: fmt::Display, C: fmt::Display + Top> fmt::Display for CHC<A, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} -> {}", self.body, self.head)
    }
}

impl<A> From<CHCHead<A, Constraint>> for CHCHead<A, pcsp::Atom> {
    fn from(h: CHCHead<A, Constraint>) -> Self {
        match h {
            CHCHead::Constraint(c) => CHCHead::Constraint(c.into()),
            CHCHead::Predicate(p) => CHCHead::Predicate(p),
        }
    }
}

impl<A> From<CHCBody<A, Constraint>> for CHCBody<A, pcsp::Atom> {
    fn from(h: CHCBody<A, Constraint>) -> Self {
        let constraint = h.constraint.into();
        CHCBody {
            constraint,
            predicates: h.predicates,
        }
    }
}

impl<A> From<CHC<A, Constraint>> for CHC<A, pcsp::Atom> {
    fn from(c: CHC<A, Constraint>) -> Self {
        let body = c.body.into();
        let head = c.head.into();
        CHC { body, head }
    }
}

impl<A> From<CHCHead<A, pcsp::Atom>> for CHCHead<A, Constraint> {
    fn from(h: CHCHead<A, pcsp::Atom>) -> Self {
        match h {
            CHCHead::Constraint(c) => CHCHead::Constraint(c.to_constraint().unwrap()),
            CHCHead::Predicate(p) => CHCHead::Predicate(p),
        }
    }
}

impl<A> From<CHCBody<A, pcsp::Atom>> for CHCBody<A, Constraint> {
    fn from(h: CHCBody<A, pcsp::Atom>) -> Self {
        let constraint = h.constraint.to_constraint().unwrap();
        CHCBody {
            constraint,
            predicates: h.predicates,
        }
    }
}

impl<A> From<CHC<A, pcsp::Atom>> for CHC<A, Constraint> {
    fn from(c: CHC<A, pcsp::Atom>) -> Self {
        let body = c.body.into();
        let head = c.head.into();
        CHC { body, head }
    }
}

impl<C: TConstraint> CHCBody<Atom, C> {
    fn collect_predicates(&self, predicates: &mut HashMap<Ident, usize>) {
        for a in self.predicates.iter() {
            if let Some(n) = predicates.insert(a.predicate, a.args.len()) {
                debug_assert!(n == a.args.len())
            }
        }
    }
}
impl<C: TConstraint> CHC<Atom, C> {
    pub fn collect_predicates(&self, predicates: &mut HashMap<Ident, usize>) {
        match &self.head {
            CHCHead::Constraint(_) => (),
            CHCHead::Predicate(a) => {
                if let Some(n) = predicates.insert(a.predicate, a.args.len()) {
                    debug_assert!(n == a.args.len())
                }
            }
        }
        self.body.collect_predicates(predicates);
    }
}

impl Atom {
    fn replace_with_model(&self, model: &Model) -> Constraint {
        let m = model.model.get(&self.predicate).unwrap();
        assert_eq!(m.0.len(), self.args.len());
        let v: Vec<_> =
            m.0.iter()
                .zip(self.args.iter())
                .map(|(x, y)| (*x, y.clone()))
                .collect();
        m.1.subst_multi(&v)
    }
}

impl CHCHead<Atom, Constraint> {
    fn replace_with_model(&self, model: &Model) -> Constraint {
        match self {
            CHCHead::Constraint(c) => c.clone(),
            CHCHead::Predicate(a) => a.replace_with_model(model),
        }
    }
}

impl CHCBody<Atom, Constraint> {
    fn replace_with_model(&self, model: &Model) -> Constraint {
        let mut c = self.constraint.clone();
        for a in self.predicates.iter() {
            c = Constraint::mk_conj(c, a.replace_with_model(model));
        }
        c
    }
}

impl CHC<Atom, Constraint> {
    pub fn replace_with_model(&self, model: &Model) -> Constraint {
        let head = self.head.replace_with_model(model);
        let body = self.body.replace_with_model(model);
        Constraint::mk_implies(body, head)
    }
}

pub fn nonliniality<'a, A, C, I>(itr: I) -> usize
where
    A: 'a,
    C: 'a,
    I: 'a + Iterator<Item = &'a CHC<A, C>>,
{
    let mut n = 0;
    for chc in itr {
        n = usize::max(chc.body.predicates.len(), n);
    }
    n
}

pub fn is_linear<'a, A, C, I>(itr: I) -> bool
where
    A: 'a,
    C: 'a,
    I: 'a + Iterator<Item = &'a CHC<A, C>>,
{
    nonliniality(itr) == 1
}

#[cfg(test)]
/// ### clause
/// P(x + 1, y) /\ Q(y) /\ x < 0 => P(x, y)
/// ### model
/// - P(x, y) = x < y
/// - Q(y)    = 5 < y
/// ### variables
/// [x, y, p, q]
pub fn gen_clause_pqp() -> (CHC<Atom, Constraint>, Model, Vec<Ident>) {
    let p = Ident::fresh();
    let q = Ident::fresh();
    let x = Ident::fresh();
    let y = Ident::fresh();
    let x_p_1 = Op::mk_add(Op::mk_var(x), Op::mk_const(1));
    let head = CHCHead::Predicate(Atom {
        predicate: p,
        args: vec![Op::mk_var(x), Op::mk_var(y)],
    });
    let c1 = Atom {
        predicate: p,
        args: vec![x_p_1, Op::mk_var(y)],
    };
    let c2 = Atom {
        predicate: q,
        args: vec![Op::mk_var(y)],
    };
    let constr = Constraint::mk_lt(Op::mk_var(x), Op::mk_const(0));
    let body = CHCBody {
        constraint: constr,
        predicates: vec![c1, c2],
    };

    let p_c = Constraint::mk_lt(Op::mk_var(x), Op::mk_var(y));
    let q_c = Constraint::mk_lt(Op::mk_const(5), Op::mk_var(y));
    let mut model = Model::new();
    model.model.insert(p, (vec![x, y], p_c));
    model.model.insert(q, (vec![x], q_c));
    (CHC { head, body }, model, vec![x, y, p, q])
}

#[test]
fn test_replace_with_model() {
    let (chc, model, vars) = gen_clause_pqp();
    let result = chc.replace_with_model(&model);
    println!("result: {}", result);
    let x = vars[0];
    let y = vars[1];

    // x + 1 < y /\ 5 < y /\ x < 0 => x < y
    let c1 = Constraint::mk_lt(Op::mk_add(Op::mk_var(x), Op::mk_const(1)), Op::mk_var(y));
    let c2 = Constraint::mk_lt(Op::mk_const(5), Op::mk_var(y));
    let c3 = Constraint::mk_lt(Op::mk_var(x), Op::mk_const(0));
    let head = Constraint::mk_lt(Op::mk_var(x), Op::mk_var(y));
    let body = Constraint::mk_conj(c1, Constraint::mk_conj(c2, c3));
    let answer = Constraint::mk_implies(body, head);
    println!("answer: {}", answer);

    // check if result <=> answer using SMT solver
    use crate::solver::smt;
    let mut solver = smt::default_solver();
    match solver.check_equivalent(&result, &answer) {
        crate::solver::SolverResult::Sat => (),
        _ => panic!("error"),
    }
}

fn cross_and<A: Clone, C: TConstraint>(
    left: Vec<Vec<CHCHead<A, C>>>,
    mut right: Vec<Vec<CHCHead<A, C>>>,
) -> Vec<Vec<CHCHead<A, C>>> {
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

pub fn to_dnf(atom: &pcsp::Atom) -> Vec<Vec<CHCHead<Atom, Constraint>>> {
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

pub struct Model {
    pub model: HashMap<Ident, (Vec<Ident>, Constraint)>,
}

impl fmt::Display for Model {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.pretty_display())
    }
}

impl Default for Model {
    fn default() -> Self {
        Self::new()
    }
}

impl Model {
    pub fn new() -> Model {
        Model {
            model: HashMap::new(),
        }
    }
    pub fn merge(&mut self, model: Model) {
        for (k, v) in model.model.into_iter() {
            self.model.insert(k, v);
        }
    }
    /// check if model is tracktable
    ///
    /// model is tracktable: all constraints in model do not contain any existential quantifier.
    pub fn is_solution_tractable(&self) -> bool {
        for (_, (_, c)) in self.model.iter() {
            let (qs, _) = c.to_pnf_raw();
            for (q, _) in qs {
                if q.is_existential() {
                    return false;
                }
            }
        }
        true
    }
}

#[test]
fn test_solution_tractability() {
    use super::{Constraint, FirstOrderLogic, Ident, QuantifierKind};
    let v = Ident::fresh();
    let w = Ident::fresh();

    let c = Constraint::mk_quantifier_int(
        QuantifierKind::Universal,
        w,
        Constraint::mk_quantifier_int(
            QuantifierKind::Existential,
            v,
            Constraint::mk_eq(Op::mk_var(v), Op::mk_var(w)),
        ),
    );
    let mut m = Model::new();
    m.model.insert(Ident::fresh(), (Vec::new(), c));
    assert!(!m.is_solution_tractable());

    let c = Constraint::mk_quantifier_int(
        QuantifierKind::Universal,
        w,
        Constraint::mk_quantifier_int(
            QuantifierKind::Universal,
            v,
            Constraint::mk_eq(Op::mk_var(v), Op::mk_var(w)),
        ),
    );
    let mut m = Model::new();
    m.model.insert(Ident::fresh(), (Vec::new(), c));
    assert!(m.is_solution_tractable());
}

/// this is a debug function for checking the given model is actually "a model" of the given CHC by
/// using SMT solver.
pub fn check_the_model_validity(model: &Model, chc: &Vec<CHC<Atom, Constraint>>) -> bool {
    use crate::solver::smt;
    let mut solver = smt::default_solver();
    let c = chc.iter().fold(Constraint::mk_true(), |c, chc| {
        Constraint::mk_conj(c, chc.replace_with_model(model))
    });
    let vars = c.fv();
    match solver.solve(&c, &vars) {
        crate::solver::SolverResult::Sat => true,
        crate::solver::SolverResult::Unsat => false,
        _ => panic!("error"),
    }
}

#[test]
fn test_check_the_model_validity() {
    let (chc, model, _) = gen_clause_pqp();
    assert!(check_the_model_validity(&model, &vec![chc]))
}

////// Implementation for translating CHCs to HES.
////// Here are some auxiliary functions for that.
fn translate_predciate(atom: Atom) -> crate::formula::hes::Goal<Constraint> {
    use crate::formula::hes::*;
    let pred = Goal::mk_var(atom.predicate);
    atom.args
        .into_iter()
        .fold(pred, |a, x| Goal::mk_app(a, Goal::mk_op(x.clone())))
}

fn translate_predicates(
    predicates: Vec<Atom>,
    mut constraint: crate::formula::hes::Goal<Constraint>,
) -> crate::formula::hes::Goal<Constraint> {
    use crate::formula::hes::*;
    for atom in predicates {
        let app = translate_predciate(atom);
        constraint = Goal::mk_disj_opt(constraint, app);
    }
    constraint
}
fn quantify(
    mut c: crate::formula::hes::Goal<Constraint>,
    free_variables: &Vec<Variable>,
) -> crate::formula::hes::Goal<Constraint> {
    use crate::formula::hes::*;

    for v in free_variables.iter() {
        c = Goal::mk_univ(v.clone(), c);
    }
    c
}

/// Extended version of CHC struct
/// that contains type information on free variables to track
/// which variables are boolean
#[derive(Clone, Debug)]
pub struct ExtendedCHC<A, C> {
    pub chc: CHC<A, C>,
    pub free_variables: Vec<Variable>,
}

/// normalize the heads of CHCs so that they are either false or a predicate
/// and returns the map from predicate name to their arguments which newly generated
fn normalize_constraint_and_generate_new_args(
    chcs: &mut Vec<ExtendedCHC<Atom, Constraint>>,
) -> HashMap<Ident, Vec<Ident>> {
    let mut arguments: HashMap<Ident, Vec<Ident>> = HashMap::new();
    chcs.iter_mut().for_each(|echc| {
        let chc = &mut echc.chc;
        match &chc.head {
            CHCHead::Constraint(c) => {
                chc.body.constraint =
                    Constraint::mk_conj(chc.body.constraint.clone(), c.negate().unwrap());
                chc.head = CHCHead::Constraint(Constraint::mk_false());
            }
            CHCHead::Predicate(p) => {
                arguments
                    .entry(p.predicate)
                    .or_insert((0..p.args.len()).map(|_| Ident::fresh()).collect());
            }
        }
    });
    arguments
}

/// returns consr that is not eq constraint
fn group_eq_constrs(constraint: &Constraint, eqs: &mut Vec<(Op, Op)>) -> Constraint {
    let cnf = constraint.to_cnf();
    let mut res = Constraint::mk_true();
    for c in cnf {
        match c.kind() {
            crate::formula::ConstraintExpr::Pred(p, l) if l.len() == 2 && *p == PredKind::Eq => {
                let x = &l[0];
                let y = &l[1];
                eqs.push((x.clone(), y.clone()));
            }
            _ => res = Constraint::mk_conj(res, c),
        }
    }
    res
}

fn replace_by_eq(
    constraint: &mut Constraint,
    predicates: &mut Vec<Atom>,
    eqs: &mut Vec<(Op, Op)>,
    fv: &Ident,
) {
    let r: Option<(usize, formula::P<formula::OpExpr>)> =
        eqs.iter().enumerate().find_map(|(i, (o1, o2))| {
            let mut fvs = o1.fv();
            o2.fv_with_vec(&mut fvs);
            if fvs.contains(fv) {
                Op::solve_for(fv, o1, o2).map(|x| (i, x))
            } else {
                None
            }
        });
    match r {
        Some((idx, replace)) => {
            let mut new_eqs = Vec::new();
            for (i, (o1, o2)) in eqs.into_iter().enumerate() {
                if i == idx {
                    continue;
                }
                let o1 = o1.subst(fv, &replace);
                let o2 = o2.subst(fv, &replace);
                new_eqs.push((o1, o2));
            }
            // replace predicates
            *constraint = constraint.subst(fv, &replace);
            *predicates = predicates
                .into_iter()
                .map(|p| Atom {
                    args: p.args.iter().map(|a| a.subst(fv, &replace)).collect(),
                    predicate: p.predicate,
                })
                .collect();
            *eqs = new_eqs;
        }
        None => (),
    }
}

fn finalize_replacement(
    eqs: Vec<(Op, Op)>,
    mut constraint: Constraint,
    predicates: Vec<Atom>,
) -> (Constraint, Vec<Atom>) {
    for (o1, o2) in eqs {
        constraint = Constraint::mk_conj(constraint, Constraint::mk_eq(o1, o2));
    }

    let predicates = predicates
        .iter()
        .map(|atom| Atom {
            args: atom.args.clone(),
            ..atom.clone()
        })
        .collect();
    (constraint, predicates)
}

fn filter_and_append_fvs(
    free_variables: &mut Vec<Variable>,
    old_fvs: &Vec<Variable>,
    clause_fvs: &HashSet<Ident>,
) {
    for v in old_fvs.iter() {
        if clause_fvs.contains(&v.id) {
            free_variables.push(v.clone());
        }
    }
}
/// Merge CHCs that have the same head predicate.
/// Divide goal formulas and clauses
///
/// For example, if we have the following CHCs:
/// - x_1 >= 101 -> P0(x_1,x_1 - 10)
/// - x_2 <= 100 ∧ P0(x_4,x_3) ∧ P0(x_2 + 11,x_4) -> P0(x_2,x_3)
/// this function returns the following CHC:
///  (x_1 >= 101 /\ w = x_1 - 10 /\ x_2 = w) \/ (x_1 <= 100 /\  P0(x_4,x_2) ∧ P0(x_1 + 11,x_4)) -> P0(x_1, x_2)
fn merge_chcs_with_same_head(
    mut chcs: Vec<ExtendedCHC<Atom, Constraint>>,
) -> (
    // pair of free variables and the body of clauses whose head is false
    (Vec<Variable>, Vec<CHCBody<Atom, Constraint>>),
    // map from predicate name to its free variables and clauses
    HashMap<Ident, (Vec<Variable>, Vec<(Atom, CHCBody<Atom, Constraint>)>)>,
) {
    // 2. group chcs that have the same head
    let mut map = HashMap::new();
    let mut constraints = Vec::new();
    let mut top_free_variables = Vec::new();
    let arguments = normalize_constraint_and_generate_new_args(&mut chcs);

    // 2. normalize the head (e.g. ... => P(x, y + 1)  ---> ... /\ y + 1 = w => P(x, w))
    // 3. rename vairables so that all the chcs have the same (non-free) variables
    for chc in chcs {
        let mut eqs = match &chc.chc.head {
            CHCHead::Constraint(_) => Vec::new(),
            CHCHead::Predicate(atom) => {
                let varnames = arguments.get(&atom.predicate).unwrap();
                atom.args
                    .iter()
                    .zip(varnames.iter())
                    .map(|(a, x)| (Op::mk_var(*x), a.clone()))
                    .collect()
            }
        };

        let mut constraint = group_eq_constrs(&chc.chc.body.constraint, &mut eqs);
        let mut predicates = chc.chc.body.predicates.clone();

        // remove fvs as much as possible
        for fv in chc.free_variables.iter() {
            replace_by_eq(&mut constraint, &mut predicates, &mut eqs, &fv.id);
        }
        let (constraint, predicates) = finalize_replacement(eqs, constraint, predicates);
        let body = CHCBody {
            constraint,
            predicates,
        };
        // insert the normalized predicate to `map`
        match chc.chc.head {
            CHCHead::Constraint(_) => {
                filter_and_append_fvs(&mut top_free_variables, &chc.free_variables, &body.fv());
                constraints.push(body);
            }
            CHCHead::Predicate(a) => {
                let atom = Atom {
                    predicate: a.predicate,
                    args: arguments
                        .get(&a.predicate)
                        .unwrap()
                        .iter()
                        .map(|x| Op::mk_var(*x))
                        .collect(),
                };
                let (free_variables, clauses) =
                    map.entry(atom.predicate).or_insert((vec![], vec![]));
                filter_and_append_fvs(free_variables, &chc.free_variables, &body.fv());
                clauses.push((atom, body));
            }
        };
    }
    ((top_free_variables, constraints), map)
}

fn get_hfl_atom_info_from_atom(a: &Atom) -> (crate::formula::Type, Vec<Ident>) {
    let args: Vec<Ident> = a
        .args
        .iter()
        .map(|x| match x.kind() {
            crate::formula::OpExpr::Var(v) => *v,
            _ => panic!("error"),
        })
        .collect();
    let mut ty = Type::mk_type_prop();
    for _ in args.iter() {
        ty = Type::mk_type_arrow(Type::mk_type_int(), ty);
    }
    (ty, args)
}

fn gen_clause(
    pred_name: Ident,
    ty: Type,
    mut form: crate::formula::hes::Goal<Constraint>,
    args: Vec<Ident>,
) -> crate::formula::hes::Clause<Constraint> {
    use crate::formula::hes::*;
    use crate::formula::*;
    for x in args.into_iter().rev() {
        form = Goal::mk_abs(Variable::mk(x, Type::mk_type_int()), form);
    }
    Clause {
        head: Variable::mk(pred_name, ty),
        body: form,
    }
}

pub fn translate_to_hes(
    chcs: Vec<ExtendedCHC<Atom, Constraint>>,
) -> crate::formula::hes::Problem<Constraint> {
    use crate::formula::hes::*;
    fn handle_body(
        body: CHCBody<Atom, Constraint>,
        free_variables: &Vec<Variable>,
    ) -> Goal<Constraint> {
        let c = Goal::mk_constr(body.constraint.negate().unwrap());
        let c = translate_predicates(body.predicates, c);
        let c = quantify(c, free_variables);
        c
    }
    let ((top_free_variables, toplevel), map) = merge_chcs_with_same_head(chcs);

    let mut top = Goal::mk_true();
    for body in toplevel {
        top = Goal::mk_conj_opt(top, handle_body(body, &top_free_variables));
    }

    let mut clauses = Vec::new();
    for (k, (free_variables, chcs)) in map {
        let (ty, args) = get_hfl_atom_info_from_atom(&chcs[0].0);
        let form = chcs.into_iter().fold(Goal::mk_true(), |form, (_, body)| {
            Goal::mk_conj_opt(form, handle_body(body, &free_variables))
        });
        clauses.push(gen_clause(k, ty, form, args));
    }
    Problem { clauses, top }
}

/// I didn't come up with the way to merge the following linear-case and non-linear case
/// So I wrote two different functions, but essentially they do the same thing.

/// Assumption: chcs are linear
/// Therefore, each clause is a triple of (a1, c, a2)  where a1 and a2 are atoms and
/// c is a constraint such that a1 /\ c => a2. (a1 and a2 can be T).
///
/// We see each clause as a1 => a2 \/ c. And merge_chcs_with_same_head_linear merges each clause
/// with the same predicate name p.
/// For example, given
///   x != 0 => P(x),
///   x < 10000 /\ P(x) => P(x + 1)
///   x >= 10000 /\ P(x) => x > 10000
fn merge_chcs_with_same_head_linear(
    mut chcs: Vec<ExtendedCHC<Atom, Constraint>>,
) -> (
    Vec<ExtendedCHC<Atom, Constraint>>,
    HashMap<Ident, Vec<ExtendedCHC<Atom, Constraint>>>,
) {
    // 2. group chcs that have the same head
    let mut map = HashMap::new();
    let mut constraints = Vec::new();

    let arguments: HashMap<Ident, Vec<Ident>> =
        normalize_constraint_and_generate_new_args(&mut chcs);

    // 2. normalize the head (e.g. ... => P(x, y + 1)  ---> ... /\ y + 1 = w => P(x, w))
    // 3. rename vairables so that all the chcs have the same (non-free) variables
    for echc in chcs {
        let chc = &echc.chc;
        let fvs = chc.fv();
        let (mut eqs, body_predicates) = if chc.body.predicates.len() == 1 {
            let atom = &chc.body.predicates[0];
            let varnames = arguments.get(&atom.predicate).unwrap();
            let eqs = atom
                .args
                .iter()
                .zip(varnames.iter())
                .map(|(a, x)| (Op::mk_var(*x), a.clone()))
                .collect();
            (
                eqs,
                vec![Atom {
                    predicate: atom.predicate,
                    args: varnames.iter().map(|x| Op::mk_var(*x)).collect(),
                }],
            )
        } else {
            (Vec::new(), Vec::new())
        };

        let mut constraint = group_eq_constrs(&chc.body.constraint, &mut eqs);
        // use head's predicate will be substituted
        let mut predicates = match &chc.head {
            CHCHead::Constraint(_) => Vec::new(),
            CHCHead::Predicate(a) => vec![a.clone()],
        };

        // remove fvs as much as possible
        for fv in fvs.iter() {
            replace_by_eq(&mut constraint, &mut predicates, &mut eqs, fv)
        }
        let (constraint, predicates) = finalize_replacement(eqs, constraint, predicates);
        let body = CHCBody {
            constraint,
            predicates: body_predicates,
        };
        let head = if predicates.len() == 1 {
            CHCHead::Predicate(predicates[0].clone())
        } else {
            assert_eq!(predicates.len(), 0);
            CHCHead::Constraint(Constraint::mk_false())
        };
        let chc = CHC { head, body };
        let mut free_variables = Vec::new();
        filter_and_append_fvs(&mut free_variables, &echc.free_variables, &chc.fv());
        let echc = ExtendedCHC {
            free_variables,
            chc,
        };

        if echc.chc.body.predicates.len() == 0 {
            constraints.push(echc);
        } else {
            map.entry(echc.chc.body.predicates[0].predicate)
                .or_insert(vec![])
                .push(echc);
        }
    }
    (constraints, map)
}

fn translate_predicate_linear(
    atom: Atom,
    constraint: crate::formula::hes::Goal<Constraint>,
) -> crate::formula::hes::Goal<Constraint> {
    let app = translate_predciate(atom);
    crate::formula::hes::Goal::mk_disj_opt(constraint, app)
}

/// Interprets the CHC in a style of greatest fixpoint.
pub fn translate_to_hes_linear(
    chcs: Vec<ExtendedCHC<Atom, Constraint>>,
) -> crate::formula::hes::Problem<Constraint> {
    use crate::formula::hes::*;
    fn handle_chc(echc: ExtendedCHC<Atom, Constraint>) -> Goal<Constraint> {
        let constraint = echc.chc.body.constraint.clone().negate().unwrap();
        let g = match echc.chc.head {
            CHCHead::Constraint(c) => Goal::mk_constr(Constraint::mk_disj(constraint, c)),
            CHCHead::Predicate(p) => translate_predicate_linear(p, Goal::mk_constr(constraint)),
        };
        quantify(g, &echc.free_variables)
    }
    let (toplevel, map) = merge_chcs_with_same_head_linear(chcs);

    let mut top = Goal::mk_true();
    for echc in toplevel {
        assert_eq!(echc.chc.body.predicates.len(), 0);
        top = Goal::mk_conj_opt(top, handle_chc(echc));
    }

    let mut clauses = Vec::new();
    for (k, echcs) in map {
        let p = &echcs[0].chc.body.predicates[0];
        let (ty, args) = get_hfl_atom_info_from_atom(p);
        let form = echcs.into_iter().fold(Goal::mk_true(), |form, echc| {
            assert_eq!(echc.chc.body.predicates.len(), 1);
            assert_eq!(echc.chc.body.predicates[0].predicate, k);
            Goal::mk_conj_opt(form, handle_chc(echc))
        });
        clauses.push(gen_clause(k, ty, form, args));
    }
    Problem { clauses, top }
}

#[test]
fn test_translation() {
    let chcs = crate::parse::get_mc91();
    println!("Target CHC");
    chcs.iter().for_each(|c| println!("{}", c.chc));

    println!("Translated HES");
    let hes = translate_to_hes(chcs);
    println!("{}", hes);
}

#[test]
fn test_translation_linear() {
    let chcs = crate::parse::get_linear();

    println!("Target CHC");
    chcs.iter().for_each(|c| println!("{}", c.chc));

    println!("Translated HES");
    let hes = translate_to_hes_linear(chcs);
    println!("{}", hes);
}
