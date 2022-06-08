use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Display},
};

use crate::formula::{fofml, Variable};
use crate::formula::{
    Constraint, FirstOrderLogic, Fv, Ident, Negation, Op, Polarity, Rename, Subst, Top,
    Type as SType, TypeKind as STypeKind,
};
use crate::{formula::hes::Goal, solver, solver::smt};

use crate::util::P;

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

impl<C: Refinement> Tau<C> {
    pub fn rty(&self) -> C {
        match self.kind() {
            TauKind::Proposition(c) => c.clone(),
            TauKind::IArrow(x, t) => C::mk_exists_int(*x, t.rty()),
            TauKind::Arrow(_, t) => t.rty(),
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
    pub fn clone_with_template(&self, fvs: &mut HashSet<Ident>) -> Tau<fofml::Atom> {
        match self.kind() {
            TauKind::Proposition(_) => {
                let args = fvs.iter().map(|x| Op::mk_var(*x)).collect();
                let pred = fofml::Atom::mk_fresh_pred(args);
                Tau::mk_prop_ty(pred)
            }
            TauKind::IArrow(x, t) => {
                let (x, t) = if fvs.contains(x) {
                    let y = Ident::fresh();
                    (y, t.rename(x, &y))
                } else {
                    (*x, t.clone())
                };
                fvs.insert(x);
                let t_temp = t.clone_with_template(fvs);
                fvs.remove(&x);
                Tau::mk_iarrow(x, t_temp)
            }
            TauKind::Arrow(ts, t) => {
                let ts = ts.iter().map(|s| s.clone_with_template(fvs)).collect();
                let t = t.clone_with_template(fvs);
                Tau::mk_arrow(ts, t)
            }
        }
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
}
impl Tau<Constraint> {
    pub fn constraint_rty(&self) -> Constraint {
        self.rty()
    }
}

// Type environment
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
