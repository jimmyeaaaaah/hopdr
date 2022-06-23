use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Display},
};

use crate::formula::{fofml, Variable};
use crate::formula::{
    Constraint, DerefPtr, FirstOrderLogic, Fv, Ident, Logic, Negation, Op, Polarity, Rename, Subst,
    Top, Type as SType, TypeKind as STypeKind,
};
use crate::util::P;
use crate::{formula, formula::hes::Goal, solver, solver::smt};

use rpds::Stack;

#[derive(Debug)]
pub enum TauKind<C> {
    Proposition(C),
    IArrow(Ident, Tau<C>),
    Arrow(Vec<Tau<C>>, Tau<C>),
}

pub type Tau<C> = P<TauKind<C>>;
pub type TyKind<C> = TauKind<C>;
pub type Ty = Tau<Constraint>;

pub trait Refinement:
    Clone
    + Negation
    + FirstOrderLogic
    + Subst<Id = Ident, Item = Op>
    + Fv<Id = Ident>
    + PartialEq
    + Rename
    + From<Goal<Self>>
    + DerefPtr
    + fmt::Display
{
    fn mk_implies_opt(x: Self, y: Self) -> Option<Self> {
        x.negate().map(|x| Self::mk_disj(x, y))
    }
}
impl<T> Refinement for T where
    T: Clone
        + Negation
        + FirstOrderLogic
        + Subst<Id = Ident, Item = Op>
        + Fv<Id = Ident>
        + PartialEq
        + Rename
        + From<Goal<Self>>
        + DerefPtr
        + fmt::Display
{
}

pub struct Positive {}

#[derive(Debug)]
pub enum Error {
    TypeError,
    SMTTimeout,
    SMTUnknown,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Error::TypeError => "type error",
            Error::SMTTimeout => "SMT Timeout",
            Error::SMTUnknown => "SMT Unknown",
        };
        write!(f, "{}", s)
    }
}
impl<C: fmt::Display> fmt::Display for Tau<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TauKind::Proposition(c) => write!(f, "bool[{}]", c),
            TauKind::IArrow(i, t) => write!(f, "({}: int -> {})", i, t),
            TauKind::Arrow(t1, t2) => {
                write!(f, "(")?;
                if t1.len() == 0 {
                    write!(f, "T")?;
                } else {
                    if t1.len() > 1 {
                        write!(f, "(")?;
                    }
                    write!(f, "{}", &t1[0])?;
                    for t in t1[1..].iter() {
                        write!(f, " /\\ {}", t)?;
                    }
                    if t1.len() > 1 {
                        write!(f, ")")?;
                    }
                }
                write!(f, "-> {})", t2)
            }
        }
    }
}

pub trait TTop {
    fn mk_top(st: &SType) -> Self;
}

pub trait TBot {
    fn mk_bot(st: &SType) -> Self;
}

impl<C: Refinement> TTop for Tau<C> {
    fn mk_top(st: &SType) -> Self {
        Tau::new(TyKind::new_top(st))
    }
}

impl<C: Refinement> TBot for Tau<C> {
    fn mk_bot(st: &SType) -> Self {
        Tau::new(TyKind::new_bot(st))
    }
}
impl<C: Refinement> TyKind<C> {
    fn new_top(st: &SType) -> TyKind<C> {
        use STypeKind::*;
        match st.kind() {
            Proposition => TauKind::Proposition(C::mk_true()),
            Arrow(x, y) if **x == Integer => {
                TauKind::IArrow(Ident::fresh(), Tau::new(TauKind::new_top(y)))
            }
            Arrow(x, y) => TauKind::Arrow(
                vec![Tau::new(TauKind::new_bot(x))],
                Tau::new(TauKind::new_top(y)),
            ),
            Integer => panic!("integer occurs at the result position"),
        }
    }
    fn new_bot(st: &SType) -> TyKind<C> {
        use STypeKind::*;
        match st.kind() {
            Proposition => TauKind::Proposition(C::mk_false()),
            Arrow(x, y) if **x == Integer => {
                TauKind::IArrow(Ident::fresh(), Tau::new(TauKind::new_bot(y)))
            }
            Arrow(x, y) => TauKind::Arrow(
                vec![Tau::new(TauKind::new_top(x))],
                Tau::new(TauKind::new_bot(y)),
            ),
            Integer => panic!("integer occurs at the result position"),
        }
    }
}

impl<C: Refinement> Rename for Tau<C> {
    fn rename(&self, x: &Ident, y: &Ident) -> Self {
        match self.kind() {
            TauKind::Proposition(c) => Self::mk_prop_ty(c.rename(x, y)),
            TauKind::IArrow(z, _) if x == z => self.clone(),
            TauKind::IArrow(z, t) if y == z => {
                let z2 = Ident::fresh();
                let t = t.rename(z, &z2);
                Self::mk_iarrow(z2, t.rename(x, y))
            }
            TauKind::IArrow(z, t) => Self::mk_iarrow(*z, t.rename(x, y)),
            TauKind::Arrow(ts, t) => {
                let ts = ts.iter().map(|t| t.rename(x, y)).collect();
                Self::mk_arrow(ts, t.rename(x, y))
            }
        }
    }
}

impl<C: Refinement> Subst for Tau<C> {
    type Id = Ident;
    type Item = Op;

    fn subst(&self, x: &Self::Id, v: &Self::Item) -> Self {
        match self.kind() {
            TauKind::Proposition(c) => Self::mk_prop_ty(c.subst(x, v)),
            TauKind::IArrow(y, _) if y == x => self.clone(),
            TauKind::IArrow(y, t) => Self::mk_iarrow(*y, t.subst(x, v)),
            TauKind::Arrow(ts, t) => {
                let ts = ts.iter().map(|t| t.subst(x, v)).collect();
                let t = t.subst(x, v);
                Self::mk_arrow(ts, t)
            }
        }
    }
}

impl<C: Refinement> DerefPtr for Tau<C> {
    fn deref_ptr(&self, id: &Ident) -> Self {
        match self.kind() {
            TauKind::Proposition(c) => Tau::mk_prop_ty(c.deref_ptr(id)),
            TauKind::IArrow(x, t) => Tau::mk_iarrow(*x, t.deref_ptr(id)),
            TauKind::Arrow(ts, s) => {
                let ts = ts.iter().map(|t| t.deref_ptr(id)).collect();
                Tau::mk_arrow(ts, s.deref_ptr(id))
            }
        }
    }
}

#[test]
fn test_tau_deref_ptr() {
    use crate::formula::fofml::Atom;
    use crate::formula::Logic;
    let x = Ident::fresh();
    let p = Ident::fresh();
    let o = Op::mk_add(Op::mk_const(1), Op::mk_var(x));
    let o2 = Op::mk_const(4);
    let c = Constraint::mk_lt(o, o2.clone());
    let a = Atom::mk_conj(
        Atom::mk_pred(p, vec![Op::mk_var(x)]),
        Atom::mk_constraint(c),
    );
    let t = Tau::mk_prop_ty(a.clone());
    let t = Tau::mk_iarrow(Ident::fresh(), t);
    let t2 = t.subst(&x, &o2);
    let t3 = t2.deref_ptr(&x);
    match t3.kind() {
        TauKind::IArrow(_, t4) => match t4.kind() {
            TauKind::Proposition(a2) => {
                assert_eq!(&a, a2)
            }
            _ => panic!("fatal"),
        },
        _ => panic!("fatal"),
    }
}

// inner purpose
enum Method {
    Conj,
    Disj,
}

impl<C: Refinement> Tau<C> {
    pub fn rty(&self) -> C {
        match self.kind() {
            TauKind::Proposition(c) => c.clone(),
            TauKind::IArrow(x, t) => C::mk_exists_int(*x, t.rty()),
            TauKind::Arrow(_, t) => t.rty(),
        }
    }
    pub fn rty_no_exists(&self) -> C {
        match self.kind() {
            TauKind::Proposition(c) => c.clone(),
            TauKind::IArrow(_, t) => t.rty_no_exists(),
            TauKind::Arrow(_, t) => t.rty_no_exists(),
        }
    }
    // coarse the rty(self) to be `constraint`
    pub fn add_context(&self, constraint: &C) -> Tau<C> {
        fn go<C: Refinement>(t: &Tau<C>, constraint: &C, polarity: Polarity) -> Tau<C> {
            match t.kind() {
                // *[c] <: *[?] under constraint <=> constraint /\ ? => c. so ? = constraint => c
                TauKind::Proposition(c) if polarity == Polarity::Positive => {
                    Tau::mk_prop_ty(C::mk_implies_opt(constraint.clone(), c.clone()).unwrap())
                }
                // *[?] <: *[c] under constraint <=> constraint /\ c => ?. so ? = constraint /\ c
                TauKind::Proposition(c) => {
                    Tau::mk_prop_ty(C::mk_conj(constraint.clone(), c.clone()))
                }
                TauKind::IArrow(x, t) => {
                    let t = go(t, constraint, polarity);
                    Tau::mk_iarrow(*x, t)
                }
                TauKind::Arrow(ts, t) => {
                    let t = go(t, constraint, polarity);
                    let constraint = C::mk_conj(constraint.clone(), t.rty());
                    let ts = ts
                        .iter()
                        .map(|s| go(s, &constraint, polarity.rev()))
                        .collect();
                    Tau::mk_arrow(ts, t)
                }
            }
        }
        go(self, constraint, Polarity::Positive)
    }
    // returns the constraint that is equivalent to hold constraint |- t <= s
    pub fn check_subtype(constraint: &C, t: &Tau<C>, s: &Tau<C>) -> C {
        match (t.kind(), s.kind()) {
            (TauKind::Proposition(c1), TauKind::Proposition(c2)) => {
                C::mk_implies_opt(C::mk_conj(constraint.clone(), c2.clone()), c1.clone()).unwrap()
            }
            (TauKind::IArrow(x1, t1), TauKind::IArrow(x2, t2)) => {
                let t2 = t2.rename(x2, x1);
                Tau::check_subtype(constraint, t1, &t2)
            }
            (TauKind::Arrow(ts1, t1), TauKind::Arrow(ts2, t2)) => {
                let mut result_constraint = Tau::check_subtype(constraint, t1, t2);
                // ⋀ᵢ tᵢ ≺ ⋀ⱼt'ⱼ ⇔∀ tᵢ. ∃ t'ⱼ. tᵢ ≺ t'ⱼ
                let arg_constraint = C::mk_conj(constraint.clone(), t2.rty());
                for tx in ts1 {
                    let mut tmpc = C::mk_false();
                    for ty in ts2 {
                        tmpc = C::mk_disj(tmpc, Tau::check_subtype(&arg_constraint, tx, ty));
                    }
                    result_constraint = C::mk_conj(result_constraint, tmpc);
                }
                result_constraint
            }
            (_, _) => panic!("fatal"),
        }
    }
    /// this subtyping is different in that for the argument of τ₁ ∧ τ₂ → τ₃ < τ₁' ∧ τ₂' → τ₃'
    /// we do τ₁ < τ₁' and τ₂ < τ₂'
    pub fn check_subtype_structural(constraint: &C, t: &Tau<C>, s: &Tau<C>) -> C {
        match (t.kind(), s.kind()) {
            (TauKind::Proposition(c1), TauKind::Proposition(c2)) => {
                C::mk_implies_opt(C::mk_conj(constraint.clone(), c2.clone()), c1.clone()).unwrap()
            }
            (TauKind::IArrow(x1, t1), TauKind::IArrow(x2, t2)) => {
                let t2 = t2.rename(x2, x1);
                Tau::check_subtype_structural(constraint, t1, &t2)
            }
            (TauKind::Arrow(ts1, t1), TauKind::Arrow(ts2, t2)) => {
                assert!(ts1.len() == ts2.len());
                let mut result_constraint = Tau::check_subtype_structural(constraint, t1, t2);
                let arg_constraint = C::mk_conj(constraint.clone(), t2.rty());
                for (tx, ty) in ts1.iter().zip(ts2.iter()) {
                    let tmpc = Tau::check_subtype_structural(&arg_constraint, tx, ty);
                    result_constraint = C::mk_conj(result_constraint, tmpc);
                }
                result_constraint
            }
            (_, _) => panic!("fatal"),
        }
    }
    pub fn clone_with_template(&self, fvs: &mut HashSet<Ident>) -> Tau<fofml::Atom> {
        match self.kind() {
            TauKind::Proposition(_) => {
                let args: Vec<Op> = fvs.iter().map(|x| Op::mk_var(*x)).collect();
                let pred = fofml::Atom::mk_fresh_pred(args);
                Tau::mk_prop_ty(pred)
            }
            TauKind::IArrow(x, t) => {
                fvs.insert(*x);
                let t_temp = t.clone_with_template(fvs);
                fvs.remove(x);
                Tau::mk_iarrow(*x, t_temp)
            }
            TauKind::Arrow(ts, t) => {
                let ts = ts.iter().map(|s| s.clone_with_template(fvs)).collect();
                let t = t.clone_with_template(fvs);
                Tau::mk_arrow(ts, t)
            }
        }
    }
    fn merge_inner(self, c: Self, method: Method) -> Self {
        match (self.kind(), c.kind()) {
            (TauKind::Proposition(c1), TauKind::Proposition(c2)) => match method {
                Method::Conj => Self::mk_prop_ty(C::mk_conj(c1.clone(), c2.clone())),
                Method::Disj => Self::mk_prop_ty(C::mk_disj(c1.clone(), c2.clone())),
            },
            (_, _) => panic!("fatal"),
        }
    }
    // only for bool type
    fn conjoin(self, t: Self) -> Self {
        self.merge_inner(t, Method::Conj)
    }
    fn disjoin(self, t: Self) -> Self {
        self.merge_inner(t, Method::Disj)
    }
}
impl From<Tau<Constraint>> for Tau<fofml::Atom> {
    fn from(t: Tau<Constraint>) -> Self {
        match t.kind() {
            TauKind::Proposition(c) => Tau::mk_prop_ty(c.clone().into()),
            TauKind::IArrow(x, t) => Tau::mk_iarrow(*x, t.clone().into()),
            TauKind::Arrow(ts, t2) => {
                let ts = ts.iter().map(|t| t.clone().into()).collect();
                Tau::mk_arrow(ts, t2.clone().into())
            }
        }
    }
}

impl Tau<fofml::Atom> {
    pub fn assign(&self, model: &HashMap<Ident, (Vec<Ident>, Constraint)>) -> Tau<Constraint> {
        match self.kind() {
            TauKind::Proposition(p) => Tau::mk_prop_ty(p.assign(model)),
            TauKind::IArrow(v, x) => Tau::mk_iarrow(*v, x.assign(model)),
            TauKind::Arrow(x, y) => {
                let ts = x.iter().map(|t| t.assign(model)).collect();
                Tau::mk_arrow(ts, y.assign(model))
            }
        }
    }
    pub fn clone_with_rty_template(&self, fvs: &mut HashSet<Ident>) -> Tau<fofml::Atom> {
        match self.kind() {
            TauKind::Proposition(_) => {
                let args: Vec<Op> = fvs.iter().map(|x| Op::mk_var(*x)).collect();
                let pred = fofml::Atom::mk_fresh_pred(args);
                Tau::mk_prop_ty(pred)
            }
            TauKind::IArrow(x, t) => {
                fvs.insert(*x);
                let t_temp = t.clone_with_rty_template(fvs);
                fvs.remove(x);
                Tau::mk_iarrow(*x, t_temp)
            }
            TauKind::Arrow(ts, t) => {
                let t = t.clone_with_rty_template(fvs);
                Tau::mk_arrow(ts.clone(), t)
            }
        }
    }
}

impl<C> Tau<C> {
    pub fn to_sty(&self) -> SType {
        match self.kind() {
            TauKind::Proposition(_) => SType::mk_type_prop(),
            TauKind::IArrow(_, t) => SType::mk_type_arrow(SType::mk_type_int(), t.to_sty()),
            TauKind::Arrow(t1, t2) => SType::mk_type_arrow(t1[0].to_sty(), t2.to_sty()),
        }
    }
    pub fn mk_prop_ty(c: C) -> Tau<C> {
        Tau::new(TauKind::Proposition(c))
    }

    pub fn mk_iarrow(id: Ident, t: Tau<C>) -> Tau<C> {
        Tau::new(TauKind::IArrow(id, t))
    }

    pub fn mk_arrow(t: Vec<Tau<C>>, s: Tau<C>) -> Tau<C> {
        Tau::new(TauKind::Arrow(t, s))
    }

    pub fn mk_arrow_single(t: Tau<C>, s: Tau<C>) -> Tau<C> {
        Tau::new(TauKind::Arrow(vec![t], s))
    }
    pub fn is_proposition(&self) -> bool {
        match self.kind() {
            TauKind::Proposition(_) => true,
            _ => false,
        }
    }
}
impl Tau<Constraint> {
    pub fn constraint_rty(&self) -> Constraint {
        self.rty()
    }
}

// Type environment
#[derive(Clone, Debug)]
pub struct TypeEnvironment<Type> {
    pub map: HashMap<Ident, Vec<Type>>,
}
pub type TyEnv = TypeEnvironment<Ty>;

impl<T: Display> Display for TypeEnvironment<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (idx, ts) in self.map.iter() {
            write!(f, "{} : ", idx)?;
            let mut fst = true;
            for t in ts {
                if fst {
                    fst = false;
                } else {
                    write!(f, ", ")?;
                }
                write!(f, "{}", t)?;
            }
            writeln!(f)?;
        }
        writeln!(f)
    }
}

impl From<&TypeEnvironment<Tau<Constraint>>> for TypeEnvironment<Tau<fofml::Atom>> {
    fn from(env: &TypeEnvironment<Tau<Constraint>>) -> TypeEnvironment<Tau<fofml::Atom>> {
        let mut map = HashMap::new();
        for (k, ts) in env.map.iter() {
            map.insert(*k, ts.iter().map(|x| x.clone().into()).collect());
        }
        TypeEnvironment { map }
    }
}

impl<T> TypeEnvironment<T> {
    pub fn new() -> TypeEnvironment<T> {
        TypeEnvironment {
            map: HashMap::new(),
        }
    }

    fn add_(&mut self, v: Ident, t: T) {
        match self.map.get_mut(&v) {
            Some(s) => {
                s.push(t);
            }
            None => {
                self.map.insert(v, vec![t]);
            }
        }
    }
    pub fn add(&mut self, v: Ident, t: T) {
        self.add_(v, t);
    }
    pub fn remove(&mut self, key: &Ident) {
        self.map.remove(&key);
    }
    pub fn exists(&self, v: &Ident) -> bool {
        self.map.get(v).is_some()
    }
    pub fn get<'a>(&'a self, v: &Ident) -> Option<&'a Vec<T>> {
        let r = self.map.get(v);
        match r {
            Some(v) => {
                for _x in v.iter() {
                    //debug!("tget cont: {}", x);
                }
            }
            None => {
                debug!("not found");
            }
        }
        r
    }
}

impl<T: Clone> TypeEnvironment<T> {
    pub fn append(&mut self, x: &TypeEnvironment<T>) {
        for (k, v) in x.map.iter() {
            match self.map.get_mut(k) {
                Some(w) => {
                    for t in v {
                        w.push(t.clone());
                    }
                }
                None => {
                    self.map.insert(*k, v.iter().cloned().collect());
                }
            }
        }
    }
    pub fn merge(env1: &TypeEnvironment<T>, env2: &TypeEnvironment<T>) -> TypeEnvironment<T> {
        let mut map: HashMap<Ident, Vec<T>> = HashMap::new();
        for (k, v) in env1.map.iter() {
            map.insert(*k, v.iter().cloned().collect());
        }
        for (k, ts) in env2.map.iter() {
            match map.get_mut(k) {
                Some(vs) => {
                    for t in ts {
                        vs.push(t.clone())
                    }
                }
                None => {
                    map.insert(*k, ts.iter().cloned().collect());
                }
            }
        }
        TypeEnvironment { map }
    }
}

impl<C: Refinement> TypeEnvironment<Tau<C>> {
    pub fn add_top(&mut self, v: Ident, st: &SType) {
        self.add(v, Tau::mk_top(st));
    }

    pub fn add_bot(&mut self, v: Ident, st: &SType) {
        self.add(v, Tau::mk_bot(st));
    }
}

// ⌊τ⌋_c
pub fn to_fml<C: Refinement>(c: Goal<C>, t: Tau<C>) -> Goal<C> {
    match t.kind() {
        TauKind::Proposition(c2) => Goal::mk_conj(c, c2.clone().into()),
        TauKind::IArrow(x, y) => {
            Goal::mk_abs(Variable::mk(*x, SType::mk_type_int()), to_fml(c, y.clone()))
        }
        TauKind::Arrow(ts, y) => {
            let ident = Ident::fresh();
            let g = Goal::mk_var(ident);
            let mut cs = c;
            for t in ts.iter() {
                cs = Goal::mk_conj(types(g.clone(), t.clone()), cs);
            }
            let fml = to_fml(cs, y.clone());
            Goal::mk_abs(Variable::mk(ident, ts[0].to_sty()), fml)
        }
    }
}

// ⌊τ⌋_tt
pub fn least_fml<C: Refinement>(t: Tau<C>) -> Goal<C> {
    let f = to_fml(Goal::mk_true(), t.clone());
    // debug
    // println!("least_fml: {} ---> {}", t, f);
    f
}

// ψ↑τ
fn types<C: Refinement>(fml: Goal<C>, t: Tau<C>) -> Goal<C> {
    match t.kind() {
        TauKind::Proposition(c) => {
            let c = c.clone().negate().unwrap().into();
            Goal::mk_disj(c, fml)
        }
        TauKind::IArrow(x, t) => {
            let v = Variable::mk(*x, SType::mk_type_int());
            let p = Goal::mk_app(fml, Goal::mk_var(*x));
            let fml = types(p, t.clone());
            Goal::mk_univ(v, fml)
        }
        TauKind::Arrow(x, y) => {
            let arg = Goal::mk_ho_disj(x.iter().map(|t| least_fml(t.clone())), x[0].to_sty());
            let fml = Goal::mk_app(fml, arg);
            types(fml, y.clone())
        }
    }
}

// g ↑ t
pub fn type_check<C: Refinement>(g: &Goal<C>, t: &Tau<C>) -> C {
    types_check(g, vec![t.clone()])
}

// g ↑ ti where t = t1 ∧ ⋯ ∧ t2
pub fn types_check<C: Refinement>(g: &Goal<C>, ts: impl IntoIterator<Item = Tau<C>>) -> C {
    let f = g;
    let cnstr = ts
        .into_iter()
        .map(|t| {
            debug!("type_check: {} : {}", g, t);
            let cnstr = types(f.clone(), t.clone()).reduce();
            //println!("constr: {}", cnstr);
            cnstr
        })
        .fold(C::mk_true(), |x, y| C::mk_conj(x, y));
    cnstr
}

// TODO: Reconsider whether it is restricted to fofml::Atom
pub fn ty_check(g: &Goal<Constraint>, t: &Tau<Constraint>) -> bool {
    tys_check(g, vec![t.clone()])
}

// allow inter section types
pub fn tys_check(
    //env: &Env<Constraint>,
    g: &Goal<Constraint>,
    ts: impl IntoIterator<Item = Ty>,
) -> bool {
    //let f = env.eval(g.clone());
    let cnstr = types_check(g, ts);
    match smt::default_solver().solve(&cnstr, &HashSet::new()) {
        solver::SolverResult::Sat => true,
        solver::SolverResult::Unsat => false,
        solver::SolverResult::Timeout | solver::SolverResult::Unknown => panic!("smt check fail.."),
    }
}

#[derive(Debug)]
struct PossibleType {
    types: Stack<Ty>,
}
impl<'a, T: IntoIterator<Item = Ty>> From<T> for PossibleType {
    fn from(ts: T) -> Self {
        let mut types = Stack::new();
        for t in ts.into_iter() {
            types.push_mut(t);
        }
        PossibleType::new(types)
    }
}
impl fmt::Display for PossibleType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for t in self.types.iter() {
            if first {
                write!(f, "{}", t)?;
                first = false;
            } else {
                write!(f, " /\\ {}", t)?;
            }
        }
        Ok(())
    }
}
impl PossibleType {
    fn empty() -> PossibleType {
        PossibleType {
            types: Stack::new(),
        }
    }
    fn new(types: Stack<Ty>) -> PossibleType {
        PossibleType { types }
    }
}
type G = Goal<Constraint>;

// tenv |- goal: ty
pub fn type_check_goal(tenv: &TyEnv, goal: &G, t: &Ty) -> bool {
    // tenv+ienv; constraint |- App(arg, ret): t
    fn handle_app(
        constraint: &Constraint,
        tenv: &mut TyEnv,
        ienv: &mut HashSet<Ident>,
        app_expr: &G,
    ) -> PossibleType {
        fn handle_inner(
            constraint: &Constraint,
            tenv: &mut TyEnv,
            ienv: &mut HashSet<Ident>,
            pred: &G,
        ) -> PossibleType {
            match pred.kind() {
                formula::hes::GoalKind::Var(x) => match tenv.get(x) {
                    // TODO! we have to instantiate x
                    Some(ts) => ts.iter().map(|t| t.add_context(constraint)).into(),
                    None => PossibleType::empty(),
                },
                formula::hes::GoalKind::App(predg, argg) => {
                    let pred_pt = handle_inner(constraint, tenv, ienv, predg);
                    // Case: the argument is integer
                    match argg.check_int_expr(ienv) {
                        // Case: the type of argument is int
                        Some(op) => {
                            let types = pred_pt
                                .types
                                .into_iter()
                                .map(|t| match t.kind() {
                                    TauKind::IArrow(x, t2) => t2.subst(x, &op),
                                    _ => panic!("fatal"),
                                })
                                .collect();
                            return PossibleType::new(types); // eary return
                        }
                        // Otherwise, we continue.
                        None => (),
                    };

                    // Case: the argument is not integer
                    let mut result_cts = Stack::new();
                    // we calculate the argument's type. we have to enumerate all the possible type of pt1.
                    'pt_iter: for ty in pred_pt.types.iter() {
                        let (arg_t, result_t) = match ty.kind() {
                            TauKind::Arrow(arg, result) => (arg, result),
                            TauKind::Proposition(_) | TauKind::IArrow(_, _) => panic!("fatal"),
                        };
                        // check if there exists a derivation for all types in the intersection type.
                        for t in arg_t {
                            let arg_constraint =
                                Constraint::mk_conj(t.rty_no_exists(), constraint.clone());
                            debug!("t: {}", t);
                            // check if arg_constraint |- argg: arg_t
                            if !go(&arg_constraint, t, tenv, ienv, argg) {
                                continue 'pt_iter;
                            }
                        }
                        // Now that all the argument for `pred_pt` can be derived, we have candidatetype `result_t`
                        // with the derivations of `ct`s
                        result_cts.push_mut(result_t.clone());
                    }
                    PossibleType::new(result_cts)
                }
                formula::hes::GoalKind::Constr(_)
                | formula::hes::GoalKind::Op(_)
                | formula::hes::GoalKind::Abs(_, _)
                | formula::hes::GoalKind::Conj(_, _)
                | formula::hes::GoalKind::Disj(_, _)
                | formula::hes::GoalKind::Univ(_, _) => panic!("fatal"),
            }
        }
        let mut pt = handle_inner(constraint, tenv, ienv, app_expr);
        debug!("handle_app: {} |- {} : {} ", constraint, app_expr, pt);
        pt
    }
    // we assume conjunction normal form and has the form (θ => a₁ a₂ ⋯) ∧ ⋯
    // constraint: Θ
    // Γ; Θ ⊢ c : t
    // function go constructs possible derivation trees by induction on the structure of c(ψ)
    //
    fn go(
        constraint: &Constraint,
        t: &Ty,
        tenv: &mut TyEnv,
        ienv: &mut HashSet<Ident>,
        c: &G,
    ) -> bool {
        match c.kind() {
            formula::hes::GoalKind::Constr(c) => {
                let constraint = constraint.clone().into();
                let type_constr = match t.kind() {
                    TauKind::Proposition(type_constr) => type_constr.clone().into(),
                    TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => panic!("fatal"),
                };
                solver::smt::default_solver()
                    .solve_with_universal_quantifiers(&Constraint::mk_implies(
                        Constraint::mk_conj(constraint, type_constr),
                        c.clone(),
                    ))
                    .is_sat()
            }
            formula::hes::GoalKind::Var(x) => match tenv.get(x) {
                Some(ts) => {
                    for s in ts {
                        // check if constraint |- s <: t
                        let c = Ty::check_subtype(constraint, s, t);
                        let c = c.into();
                        if solver::smt::default_solver()
                            .solve_with_universal_quantifiers(&c)
                            .is_sat()
                        {
                            return true;
                        }
                    }
                    false
                }
                None => {
                    panic!("{} is not found in env", x)
                }
            },
            formula::hes::GoalKind::Conj(g1, g2) => {
                let t1 = go(constraint, t, tenv, ienv, g1);
                let t2 = go(constraint, t, tenv, ienv, g2);
                t1 && t2
            }
            formula::hes::GoalKind::Disj(g1, g2) => {
                let c1: Option<Constraint> = g1.clone().into();
                let (c, g, g_) = match c1 {
                    Some(c) => (c, g2, g1),
                    None => (g2.clone().into(), g1, g2),
                };
                let c_neg = c.negate().unwrap();
                let t1 = go(
                    &Constraint::mk_conj(c_neg.into(), constraint.clone()),
                    t,
                    tenv,
                    ienv,
                    g,
                );
                // type check of constraints (to track the type derivation, checking g2 is necessary)
                let t2 = go(
                    &Constraint::mk_conj(c.into(), constraint.clone()),
                    t,
                    tenv,
                    ienv,
                    g_,
                );
                t1 && t2
            }
            formula::hes::GoalKind::Univ(x, g) => {
                // to avoid the collision, we rename the variable.
                assert!(ienv.insert(x.id));
                let pt = go(constraint, t, tenv, ienv, &g);
                ienv.remove(&x.id);
                pt
            }
            formula::hes::GoalKind::App(_, _) => {
                handle_app(constraint, tenv, ienv, c).types.pop().is_some()
            }
            formula::hes::GoalKind::Abs(v, g) => {
                // 1. check t and calculate the argument's type.
                // 2.
                match t.kind() {
                    TauKind::IArrow(id, t) if v.ty.is_int() => {
                        let t = t.rename(id, &v.id);
                        assert!(ienv.insert(v.id));
                        let ct = go(constraint, &t, tenv, ienv, g);
                        ienv.remove(&v.id);
                        ct
                    }
                    TauKind::Arrow(ts, t) if !v.ty.is_int() => {
                        for t in ts {
                            tenv.add(v.id, t.clone());
                        }
                        go(constraint, t, tenv, ienv, g)
                    }
                    _ => panic!("fatal"),
                }
            }
            // op is always handled by App(x, op)
            formula::hes::GoalKind::Op(_) => panic!("fatal error"),
        }
    }
    crate::title!("type_check_top");
    debug!("tenv: {}", tenv);
    let mut tenv = tenv.clone();
    let mut ienv = HashSet::new();
    go(&Constraint::mk_true(), &t, &mut tenv, &mut ienv, &goal)
}

pub fn type_check_top(tenv: &TyEnv, goal: &G) -> bool {
    let ty = Tau::mk_prop_ty(Constraint::mk_true());
    type_check_goal(tenv, goal, &ty)
}
