use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Display},
};

use crate::formula::{fofml, PredKind, TeXFormat, TeXPrinter, Variable};
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
pub type PTy = PolymorphicType<Ty>;

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

impl<C: TeXFormat> TeXFormat for Tau<C> {
    fn tex_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self.kind() {
            TauKind::Proposition(c) => write!(f, r"\tb{{ {} }}", TeXPrinter(c)),
            TauKind::IArrow(i, t) => {
                write!(f, r"(\ti{{ {} }} \to {})", TeXPrinter(i), TeXPrinter(t))
            }
            TauKind::Arrow(t1, t2) => {
                write!(f, "(")?;
                if t1.len() == 0 {
                    write!(f, r"\top")?;
                } else {
                    if t1.len() > 1 {
                        write!(f, "(")?;
                    }
                    write!(f, "{}", TeXPrinter(&t1[0]))?;
                    for t in t1[1..].iter() {
                        write!(f, r" \wedge {}", TeXPrinter(t))?;
                    }
                    if t1.len() > 1 {
                        write!(f, ")")?;
                    }
                }
                write!(f, r"\to {})", TeXPrinter(t2))
            }
        }
    }
}

impl<C: PartialEq + Display> PartialEq for Tau<C> {
    fn eq(&self, other: &Self) -> bool {
        let r = match (self.kind(), other.kind()) {
            (TauKind::Proposition(c), TauKind::Proposition(c2)) => c == c2,
            (TauKind::IArrow(x1, t1), TauKind::IArrow(x2, t2)) => x1 == x2 && t1 == t2,
            (TauKind::Arrow(ts1, t1), TauKind::Arrow(ts2, t2)) => t1 == t2 && ts1 == ts2,
            (_, _) => false,
        };
        r
    }
}

pub trait TTop {
    fn mk_top(st: &SType) -> Self;
    fn is_top(&self) -> bool;
}

pub trait TBot {
    fn mk_bot(st: &SType) -> Self;
    fn is_bot(&self) -> bool;
}

impl<C: Refinement> TTop for Tau<C> {
    fn mk_top(st: &SType) -> Self {
        Tau::new(TyKind::new_top(st))
    }
    fn is_top(&self) -> bool {
        match self.kind() {
            TauKind::Proposition(c) => c.is_true(),
            TauKind::IArrow(_, t) => t.is_top(),
            TauKind::Arrow(s, t) if s.len() == 1 => s[0].is_bot() && t.is_top(),
            TauKind::Arrow(_, _) => false,
        }
    }
}

impl<C: Refinement> TBot for Tau<C> {
    fn mk_bot(st: &SType) -> Self {
        Tau::new(TyKind::new_bot(st))
    }
    fn is_bot(&self) -> bool {
        match self.kind() {
            TauKind::Proposition(c) => c.is_false(),
            TauKind::IArrow(_, t) => t.is_bot(),
            TauKind::Arrow(s, t) if s.len() == 1 => s[0].is_top() && t.is_bot(),
            TauKind::Arrow(_, _) => false,
        }
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

impl<C: Refinement> Fv for Tau<C> {
    type Id = Ident;

    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>) {
        match self.kind() {
            TauKind::Proposition(c) => {
                c.fv_with_vec(fvs);
            }
            TauKind::IArrow(i, t) => {
                t.fv_with_vec(fvs);
                fvs.remove(i);
            }
            TauKind::Arrow(ts, t) => {
                for s in ts {
                    s.fv_with_vec(fvs);
                }
                t.fv_with_vec(fvs);
            }
        }
    }
}

// inner purpose
#[allow(dead_code)]
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
        crate::title!("add_context");
        debug!("constraint = {}", constraint);
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
                    //let constraint = C::mk_conj(constraint.clone(), t.rty());
                    let ts = ts
                        .iter()
                        .map(|s| go(s, constraint, polarity.rev()))
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
                for tx in ts2 {
                    let mut tmpc = C::mk_false();
                    for ty in ts1 {
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
                    let tmpc = Tau::check_subtype_structural(&arg_constraint, ty, tx);
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
    fn _merge_inner(self, c: Self, method: Method) -> Self {
        match (self.kind(), c.kind()) {
            (TauKind::Proposition(c1), TauKind::Proposition(c2)) => match method {
                Method::Conj => Self::mk_prop_ty(C::mk_conj(c1.clone(), c2.clone())),
                Method::Disj => Self::mk_prop_ty(C::mk_disj(c1.clone(), c2.clone())),
            },
            (_, _) => panic!("fatal"),
        }
    }
    // only for bool type
    fn _conjoin(self, t: Self) -> Self {
        self._merge_inner(t, Method::Conj)
    }
    fn _disjoin(self, t: Self) -> Self {
        self._merge_inner(t, Method::Disj)
    }
    pub fn avoid_collision(&self) -> Self {
        match self.kind() {
            TauKind::Proposition(_) => self.clone(),
            TauKind::IArrow(x, t) => {
                let new_x = Ident::fresh();
                let t = t.rename(x, &new_x);
                let t = t.avoid_collision();
                Tau::mk_iarrow(new_x, t)
            }
            TauKind::Arrow(ts, t) => {
                let ts = ts.iter().map(|t| t.avoid_collision()).collect();
                let t = t.avoid_collision();
                Tau::mk_arrow(ts, t)
            }
        }
    }
    pub fn mk_arrow(t: Vec<Tau<C>>, s: Tau<C>) -> Tau<C> {
        let t_fst = t[0].clone();
        let t: Vec<_> = t.into_iter().filter(|t| !t.is_bot()).collect();
        if t.len() == 0 {
            // t_fst must be bot ty
            Tau::new(TauKind::Arrow(vec![t_fst], s))
        } else {
            Tau::new(TauKind::Arrow(t, s))
        }
    }
}

#[test]
fn test_check_subtype() {
    use formula::PredKind;
    let n = Ident::fresh();
    let r = Ident::fresh();
    type T = Tau<Constraint>;
    // n: int → (r: int → •〈r ≥ n〉 → •〈⊤〉≺
    //   n: int → (r: int → •〈r ≥ 0〉 → •〈n ≥ 0〉
    fn leqty(left: Op, right: Op) -> T {
        Tau::mk_prop_ty(Constraint::mk_bin_pred(PredKind::Leq, left, right))
    }
    fn o(x: Ident) -> Op {
        Op::mk_var(x)
    }
    fn check(t1: &T, t2: &T) -> bool {
        let c = Tau::check_subtype(&Constraint::mk_true(), t1, t2);

        let mut sol = solver::smt::smt_solver(solver::SMTSolverType::Auto);
        let m = sol.solve_with_model(&c, &c.fv(), &HashSet::new());
        m.is_ok()
    }

    let t1 = {
        let s = Tau::mk_iarrow(r, leqty(o(r), o(n)));
        let t = Tau::mk_prop_ty(Constraint::mk_true());
        let t = Tau::mk_arrow_single(s, t);
        let t = Tau::mk_iarrow(n, t);
        t
    };
    let t2 = {
        let s = Tau::mk_iarrow(r, leqty(o(r), Op::zero()));
        let t = leqty(o(n), Op::zero());
        let t = Tau::mk_arrow_single(s, t);
        let t = Tau::mk_iarrow(n, t);
        t
    };

    assert!(check(&t1, &t2));
    assert!(!check(&t2, &t1));
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
    pub fn clone_with_rty_template(
        &self,
        constraint: fofml::Atom,
        fvs: &mut HashSet<Ident>,
    ) -> Tau<fofml::Atom> {
        match self.kind() {
            TauKind::Proposition(_) => {
                let args: Vec<Op> = fvs.iter().map(|x| Op::mk_var(*x)).collect();
                let pred = fofml::Atom::mk_fresh_pred(args);
                let constr = fofml::Atom::mk_conj(pred, constraint);
                Tau::mk_prop_ty(constr)
            }
            TauKind::IArrow(x, t) => {
                fvs.insert(*x);
                let t_temp = t.clone_with_rty_template(constraint, fvs);
                fvs.remove(x);
                Tau::mk_iarrow(*x, t_temp)
            }
            TauKind::Arrow(ts, t) => {
                let t = t.clone_with_rty_template(constraint, fvs);
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

    /// traverse all the prop types, and reduce the constraint by `Constraint::reduction_trivial`
    fn optimize_constraint_reduction(&self) -> Self {
        match self.kind() {
            TauKind::Proposition(c) => Ty::mk_prop_ty(c.simplify()),
            TauKind::IArrow(x, t) => Ty::mk_iarrow(*x, t.optimize_constraint_reduction()),
            TauKind::Arrow(ts, t) => {
                let ts = ts
                    .iter()
                    .map(|s| s.optimize_constraint_reduction())
                    .collect();
                let t = t.optimize_constraint_reduction();
                Ty::mk_arrow(ts, t)
            }
        }
    }
    /// traverse all the intersection types at the argument positions,
    /// check if there are redundant intersections t1 /\ t2 in the sense that
    /// t1 == t2 (syntactically equivalent)
    fn optimize_intersection_trivial(&self) -> Self {
        debug!("optimize_intersection_trivial: {self}");
        match self.kind() {
            TauKind::Proposition(_) => self.clone(),
            TauKind::IArrow(x, y) => {
                let y = y.optimize_intersection_trivial();
                Ty::mk_iarrow(*x, y)
            }
            TauKind::Arrow(ts, t) => {
                let t = t.optimize_intersection_trivial();
                let mut ts_new = Vec::new();
                for s in ts.iter() {
                    let mut required = true;
                    for s2 in ts_new.iter() {
                        if s == s2 {
                            required = false;
                            break;
                        }
                    }
                    if required {
                        ts_new.push(s.clone());
                    }
                }
                let ts_new = ts_new
                    .iter()
                    .map(|t| t.optimize_intersection_trivial())
                    .collect();
                Ty::mk_arrow(ts_new, t)
            }
        }
    }

    pub fn optimize(&self) -> Self {
        // Pass
        //  - optimize_constraint_reduction
        //  - optimize_intersection_trivial
        //  # - optimize_intersection_subsumption
        let t = self.clone();
        let t = t.optimize_constraint_reduction();
        let t = t.optimize_intersection_trivial();
        t
    }
}

#[test]
fn test_optimize_intersection_trivial() {
    // t: (•〈⊤〉→•〈⊤〉∧ •〈⊤〉→•〈⊤〉)→•〈⊤〉
    // s: (•〈⊤〉→•〈⊤〉)→•〈⊤〉
    let t = Tau::mk_prop_ty(Constraint::mk_true());
    let t2t = Tau::mk_arrow_single(t.clone(), t.clone());
    let arg_t = vec![t2t.clone(), t2t.clone()];
    let s = Tau::mk_arrow_single(t2t, t.clone());
    let t = Tau::mk_arrow(arg_t, t);

    let t = t.optimize_intersection_trivial();
    assert_eq!(t, s);
}

#[test]
fn test_optimize_constraint_reduction() {
    // t1: (•〈⊤〉→•〈⊤〉)→•〈⊤〉
    // t1: (•〈1=1〉→•〈1=1〉)→•〈1=1〉
    let t1 = {
        let t = Tau::mk_prop_ty(Constraint::mk_true());
        let t2t = Tau::mk_arrow_single(t.clone(), t.clone());
        let arg_t = vec![t2t.clone(), t2t.clone()];
        Tau::mk_arrow(arg_t, t)
    };
    let t2 = {
        let t = Tau::mk_prop_ty(Constraint::mk_eq(Op::mk_const(1), Op::mk_const(1)));
        let t2t = Tau::mk_arrow_single(t.clone(), t.clone());
        let arg_t = vec![t2t.clone(), t2t.clone()];
        Tau::mk_arrow(arg_t, t)
    };

    let t2 = t2.optimize_constraint_reduction();
    assert_eq!(t1, t2);
}

/// `generate_t_and_its_subtype_for_test` return the following two refinement types
///   - t: ∀ x₁, x₂. (y:int → •〈y =x₁+x₂〉)→z:int→ • 〈z=x₁+x₂〉
///   - s: ∀ x₃.(y:int→•〈y=x₃〉)→z:int→•〈z=x₃〉
/// Note that t ≤ s holds.
#[cfg(test)]
fn generate_t_and_its_subtype_for_test() -> (PTy, PTy) {
    // x + 1 <= 4
    // ∀ x₁, x₂. (y:int → •〈y =x₁+x₂〉)→z:int→ • 〈z=x₁+x₂〉
    //           ≤ ∀ x₃.(y:int→•〈y=x₃〉)→z:int→•〈z=x₃〉
    let x1 = Ident::fresh();
    let x2 = Ident::fresh();
    let x3 = Ident::fresh();

    let y = Ident::fresh();
    let z = Ident::fresh();

    let x_1_plus_x2 = Op::mk_add(Op::mk_var(x1), Op::mk_var(x2));
    let t = Tau::mk_prop_ty(Constraint::mk_eq(Op::mk_var(y), x_1_plus_x2.clone()));
    let t = Tau::mk_iarrow(y, t);
    let s = Tau::mk_prop_ty(Constraint::mk_eq(Op::mk_var(z), x_1_plus_x2.clone()));
    let s = Tau::mk_iarrow(z, s);
    let t1 = Tau::mk_arrow_single(t, s);

    let t = Tau::mk_prop_ty(Constraint::mk_eq(Op::mk_var(y), Op::mk_var(x3)));
    let t = Tau::mk_iarrow(y, t);
    let s = Tau::mk_prop_ty(Constraint::mk_eq(Op::mk_var(z), Op::mk_var(x3)));
    let s = Tau::mk_iarrow(z, s);
    let t2 = Tau::mk_arrow_single(t, s);
    (PTy::poly(t1), PTy::poly(t2))
}

#[cfg(test)]
fn generate_t_and_its_subtype_for_test2() -> (PTy, PTy) {
    // x + 1 <= 4
    // ∀ x₁, x₂. (y:int → •〈y =2x₁+x₂〉)→z:int→ • 〈z=x₁+x₂〉
    //           ≤ ∀ x₃.(y:int→•〈y=x₃〉)→z:int→•〈z=x₃〉
    let x1 = Ident::fresh();
    let x2 = Ident::fresh();
    let x3 = Ident::fresh();

    let y = Ident::fresh();
    let z = Ident::fresh();

    let x_1_plus_x2 = Op::mk_add(Op::mk_var(x1), Op::mk_var(x2));
    let two_x_1_plus_x2 = Op::mk_add(Op::mk_mul(Op::mk_const(2), Op::mk_var(x1)), Op::mk_var(x2));
    let t = Tau::mk_prop_ty(Constraint::mk_eq(Op::mk_var(y), two_x_1_plus_x2.clone()));
    let t = Tau::mk_iarrow(y, t);
    let s = Tau::mk_prop_ty(Constraint::mk_eq(Op::mk_var(z), x_1_plus_x2.clone()));
    let s = Tau::mk_iarrow(z, s);
    let t1 = Tau::mk_arrow_single(t, s);

    let t = Tau::mk_prop_ty(Constraint::mk_eq(Op::mk_var(y), Op::mk_var(x3)));
    let t = Tau::mk_iarrow(y, t);
    let s = Tau::mk_prop_ty(Constraint::mk_eq(Op::mk_var(z), Op::mk_var(x3)));
    let s = Tau::mk_iarrow(z, s);
    let t2 = Tau::mk_arrow_single(t, s);
    (PTy::poly(t1), PTy::poly(t2))
}

// template for polymorphic types
pub fn generate_arithmetic_template(
    ints: &HashSet<Ident>,
    coefficients: &mut Stack<Ident>,
    all_coefficients: &mut HashSet<Ident>,
) -> Op {
    // linear template
    let c_id = Ident::fresh();
    let mut o = Op::mk_var(c_id);
    coefficients.push_mut(c_id);
    all_coefficients.insert(c_id);
    // linear expr
    for int in ints {
        let tmp = Ident::fresh();
        // o += c_i * x_i
        let t = Op::mk_bin_op(formula::OpKind::Mul, Op::mk_var(tmp), Op::mk_var(*int));
        o = Op::mk_add(o, t);
        coefficients.push_mut(tmp);
        all_coefficients.insert(tmp);
    }
    o
}
#[test]
fn test_generate_arithmetic_template() {
    // fvs: x, y
    let x = Ident::fresh();
    let y = Ident::fresh();
    let mut ints = HashSet::new();
    ints.insert(x);
    ints.insert(y);
    let mut coefs = Stack::new();
    let o = generate_arithmetic_template(&ints, &mut coefs, &mut HashSet::new());
    // expected: o = (ax + by) + c
    println!("{o}");
    use crate::formula::{OpExpr, OpKind};
    fn disasm_addition(o: &Op, ops: &mut Vec<Op>) {
        match o.kind() {
            OpExpr::Op(OpKind::Add, x, y) => {
                disasm_addition(x, ops);
                disasm_addition(y, ops);
            }
            _ => ops.push(o.clone()),
        }
    }
    let mut ops = Vec::new();
    disasm_addition(&o, &mut ops);
    assert_eq!(coefs.iter().len(), 3);
    assert_eq!(ops.len(), 3);
    for o in ops {
        match o.kind() {
            OpExpr::Op(OpKind::Mul, o1, o2) => match (o1.kind(), o2.kind()) {
                (OpExpr::Var(a), OpExpr::Var(b)) if *a == x || *a == y || *b == x || *b == y => (),
                (_, _) => panic!("fail"),
            },
            OpExpr::Var(z) if *z != x && *z != y => (),
            _ => panic!("fail"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct PolymorphicType<Type> {
    pub vars: HashSet<Ident>,
    pub ty: Type,
}

impl<T: Display> Display for PolymorphicType<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for var in self.vars.iter() {
            write!(f, "∀{}. ", var)?;
        }
        write!(f, "{}", self.ty)
    }
}

impl<T: PartialEq + Display> PartialEq for PolymorphicType<T> {
    fn eq(&self, other: &Self) -> bool {
        &self.vars == &other.vars && &self.ty == &other.ty
    }
}

impl<T: TeXFormat> TeXFormat for PolymorphicType<T> {
    fn tex_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        for var in self.vars.iter() {
            write!(f, r"\forall {}. ", var)?;
        }
        write!(f, "{}", TeXPrinter(&self.ty))
    }
}

impl<C: Refinement> TTop for PolymorphicType<Tau<C>> {
    fn mk_top(st: &SType) -> Self {
        Self::mono(Tau::new(TyKind::new_top(st)))
    }
    fn is_top(&self) -> bool {
        self.ty.is_top()
    }
}

impl<C: Refinement> TBot for PolymorphicType<Tau<C>> {
    fn mk_bot(st: &SType) -> Self {
        Self::mono(Tau::new(TyKind::new_bot(st)))
    }
    fn is_bot(&self) -> bool {
        match self.ty.kind() {
            TauKind::Proposition(c) => c.is_false(),
            TauKind::IArrow(_, t) => t.is_bot(),
            TauKind::Arrow(s, t) if s.len() == 1 => s[0].is_top() && t.is_bot(),
            TauKind::Arrow(_, _) => false,
        }
    }
}

impl From<PolymorphicType<Tau<Constraint>>> for PolymorphicType<Tau<fofml::Atom>> {
    fn from(t: PolymorphicType<Tau<Constraint>>) -> Self {
        Self {
            vars: t.vars,
            ty: t.ty.into(),
        }
    }
}

impl<T> PolymorphicType<T> {
    pub fn mono(ty: T) -> PolymorphicType<T> {
        PolymorphicType {
            vars: HashSet::new(),
            ty,
        }
    }
}

impl<T: Fv<Id = Ident>> PolymorphicType<T> {
    /// each variable freely appears in `ty` is generalized
    pub fn poly(ty: T) -> PolymorphicType<T> {
        let vars = ty.fv();
        PolymorphicType { vars, ty }
    }
}

impl PTy {
    pub fn check_subtype_polymorphic(t: &Self, s: &Self) -> bool {
        // Assumption: polymorphic type appears only at the top level of types.
        // Subtyping rule for polymorphic type
        // V; θ ▹ [e/x]τ₁ ≤ τ₂     x ∉ Fv(θ)   {y: int | y ∈ V } ⊢ e : int
        // ------------------------------------------------------------ [AllL]
        //                          ∀x.τ₁ ≤ τ₂
        //
        // V ∪ {x}; θ ▹ τ₁ ≤ τ₂    x ∉ Fv(θ) ∪ FIV(τ₁)
        // ----------------------------------------- [AllR]
        //             V; θ ▹ τ₁ ≤  ∀x. τ₂
        //
        // 1. Rename s's free variables with fresh ones (let them V'): s'.
        // 2. Instantiate t by substituting free variables with linear templates: t'.
        // 3. Generate constraint by `check_subtype(constraint, t', s')`
        // 4. Bind all the varaibles in V' by universal quantifiers
        // 5. Bind all the variables used for the linear templates by existential quantifiers
        // 6. Solve the generated constraint by some SMT solver.

        crate::title!("check_subtype_polymorphic");

        debug!("t: {t}");
        debug!("s: {s}");

        // 1. rename
        // not requried?
        // 2. instantiate t
        // for ∀x. t  ≤  ∀y. s
        // by using y's variables, first, t is instantiated.
        let mut coefficients = Stack::new();
        let mut all_coefficients = HashSet::new();
        let tprime = t.instantiate(&s.vars, &mut coefficients, &mut all_coefficients);
        debug!("tprime: {tprime}");

        // 3. constraint
        debug!("check |- {tprime} <= {}", s.ty);
        let constraint = Tau::check_subtype(&Constraint::mk_true(), &tprime, &s.ty);
        debug!("constraint: {constraint}");
        // 4. univ 5.existential quantifier 6. smt solver
        let mut sol = solver::smt::smt_solver(solver::SMTSolverType::Auto);
        let mut vprime = s.vars.clone();
        let coefficients: HashSet<Ident> = coefficients.iter().cloned().collect();
        for fv in constraint.fv() {
            if !coefficients.contains(&fv) {
                vprime.insert(fv);
            }
        }
        debug!("vprime: {vprime:?}");
        let m = sol.solve_with_model(&constraint, &vprime, &coefficients);
        m.is_ok()
    }

    fn optimize_trivial_ty(&self) -> Self {
        // ∀x_18. (x_150: int -> ((x_19: int -> bool[(0 <= x_19) ∧ (x_18 <= 0)])-> bool[x_150 = x_18]))
        // ---> x_150: int -> ((x_19: int -> bool[(0 <= x_19) ∧ (x_150 <= 0)])-> bool[T])

        // Tr(*[θ], args, (xᵢ=oᵢ)ᵢ)
        //     = for each xᵢ=oᵢ,  *[[θᵢ/xᵢ]θ] if fv(oᵢ) ⊂ args, *[θ] otherwise
        // Tr(x:int → τ, args, (xᵢ=oᵢ)ᵢ)
        //     = x:int → Tr(τ, x::args,  (xᵢ=oᵢ)ᵢ)
        // Tr(∧τᵢ → τ, args, (xᵢ=oᵢ)ᵢ)
        //     = τᵢ'  → Tr(τ, args, (xᵢ=oᵢ)ᵢ)
        //        where τᵢ'  = Tr(τᵢ, args, eq(rty(τᵢ)) ⊕ (xᵢ=oᵢ)ᵢ)

        fn tr(
            t: &Ty,
            args: &mut HashSet<Ident>,
            eqs: Stack<(Ident, Op)>,
            vars: &HashSet<Ident>,
        ) -> Ty {
            match t.kind() {
                TauKind::Proposition(c) => {
                    let mut c = c.clone();
                    for (x, o) in eqs.iter() {
                        if args.is_subset(&o.fv()) {
                            c = c.subst(x, o);
                        }
                    }
                    Ty::mk_prop_ty(c)
                }
                TauKind::IArrow(x, t) => {
                    let should_remove = args.insert(*x);
                    let t = tr(t, args, eqs, vars);
                    if should_remove {
                        args.remove(x);
                    }
                    Ty::mk_iarrow(*x, t)
                }
                TauKind::Arrow(ts, t) => {
                    let t = tr(t, args, eqs.clone(), vars);
                    let ts = ts
                        .into_iter()
                        .map(|t| tr(t, args, eq(&t.rty_no_exists(), eqs.clone(), vars), vars))
                        .collect();
                    Ty::mk_arrow(ts, t)
                }
            }
        }

        // search for x == y where x in vars and y's free variables are a set set of args
        fn search(c: &Constraint, pairs: &mut Stack<(Ident, Op)>, vars: &HashSet<Ident>) {
            match c.kind() {
                formula::ConstraintExpr::Pred(PredKind::Eq, l) if l.len() == 2 => {
                    match (l[0].kind(), l[1].kind()) {
                        (formula::OpExpr::Var(x), o) | (o, formula::OpExpr::Var(x)) => {
                            let o = Op::new(*o);
                            // if o.fv() does not contain any polymorphic variables,
                            // o only contains args.
                            if vars.contains(x) && o.fv().is_disjoint(vars) {
                                pairs.push_mut((*x, o))
                            }
                        }
                        (_, _) => (),
                    }
                }
                formula::ConstraintExpr::True
                | formula::ConstraintExpr::False
                | formula::ConstraintExpr::Pred(_, _) => (),
                formula::ConstraintExpr::Conj(c1, c2) => {
                    search(c1, pairs, vars);
                    search(c2, pairs, vars);
                }
                formula::ConstraintExpr::Disj(_, _) => (),
                formula::ConstraintExpr::Quantifier(_, _, _) => (),
            }
        }

        fn eq(
            c: &Constraint,
            mut s: Stack<(Ident, Op)>,
            vars: &HashSet<Ident>,
        ) -> Stack<(Ident, Op)> {
            search(c, &mut s, vars);
            s
        }

        fn go(t: &Ty, arg_idents: &mut HashSet<Ident>) -> Constraint {
            match t.kind() {
                TauKind::Proposition(c) => c.clone(),
                TauKind::IArrow(i, t) => {
                    assert!(arg_idents.insert(*i));
                    go(t, arg_idents)
                }
                TauKind::Arrow(_, t) => go(t, arg_idents),
            }
        }
        let mut arg_idents = HashSet::new();
        let c = go(&self.ty, &mut arg_idents);

        unimplemented!()
    }
    pub fn optimize(&self) -> Self {
        let ty = self.ty.optimize();
        Self {
            ty,
            vars: self.vars.clone(),
        }
    }
}

#[test]
fn test_subtype_polymorphic() {
    let (t1, t2) = generate_t_and_its_subtype_for_test();
    println!("{t1} <= {t2}");
    assert!(PTy::check_subtype_polymorphic(&t1, &t2));
    assert!(PTy::check_subtype_polymorphic(&t2, &t1));
}

#[test]
fn test_subtype_polymorphic2() {
    let (t1, t2) = generate_t_and_its_subtype_for_test2();
    println!("{t1} <= {t2}");
    assert!(PTy::check_subtype_polymorphic(&t1, &t2));
    println!("ok");
    assert!(!PTy::check_subtype_polymorphic(&t2, &t1));
}

impl<C: Refinement> PolymorphicType<Tau<C>> {
    pub fn instantiate(
        &self,
        ints: &HashSet<Ident>,
        coefficients: &mut Stack<Ident>,
        all_coefficients: &mut HashSet<Ident>,
    ) -> Tau<C> {
        crate::title!("instatiate_type");
        debug!("type={}", self);
        debug!("ints: {:?}", ints);
        let mut ts = self.ty.avoid_collision();
        for fv in self.vars.iter() {
            let o = generate_arithmetic_template(ints, coefficients, all_coefficients);
            debug!("template: {}", o);
            ts = ts.subst(&fv, &o);
        }
        debug!("instantiated: {}", ts);
        ts
    }
}

#[derive(Clone, Debug)]
pub struct TypeEnvironment<Type> {
    pub map: HashMap<Ident, Vec<Type>>,
}
pub type TyEnv = TypeEnvironment<PolymorphicType<Ty>>;

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

impl<T: TeXFormat> TeXFormat for TypeEnvironment<T> {
    fn tex_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        writeln!(f, r"\begin{{align*}}")?;
        for (idx, ts) in self.map.iter() {
            write!(f, "{} &: ", TeXPrinter(idx))?;
            let mut fst = true;
            for t in ts {
                if fst {
                    fst = false;
                } else {
                    write!(f, ", ")?;
                }
                write!(f, "{}", TeXPrinter(t))?;
            }
            writeln!(f, r"\\")?;
        }
        writeln!(f, r"\end{{align*}}")
    }
}

impl From<&TypeEnvironment<PolymorphicType<Tau<Constraint>>>>
    for TypeEnvironment<PolymorphicType<Tau<fofml::Atom>>>
{
    fn from(env: &TypeEnvironment<PolymorphicType<Tau<Constraint>>>) -> Self {
        let mut map = HashMap::new();
        for (k, ts) in env.map.iter() {
            map.insert(*k, ts.iter().map(|x| x.clone().into()).collect());
        }
        TypeEnvironment { map }
    }
}

fn add_if_not_exist<T: PartialEq + Display>(ts: &mut Vec<T>, t: T) {
    if ts
        .iter()
        .find_map(|x| if x == &t { Some(()) } else { None })
        .is_none()
    {
        ts.push(t);
    }
}

impl<T: PartialEq + Display> TypeEnvironment<T> {
    pub fn new() -> TypeEnvironment<T> {
        TypeEnvironment {
            map: HashMap::new(),
        }
    }

    fn add_(&mut self, v: Ident, t: T) {
        match self.map.get_mut(&v) {
            Some(ts) => {
                add_if_not_exist(ts, t);
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
    /// `size_pred` returns the number of refinement types saved in the type environment
    /// if the given pred name exists in the map.
    /// otherwise, it returns 0.
    pub fn size_pred(&self, pred: &Ident) -> usize {
        self.map.get(pred).map_or(0, |ts| ts.len())
    }
    pub fn size(&self) -> usize {
        let mut s = 0usize;
        for ts in self.map.values() {
            s += ts.len()
        }
        s
    }
}

impl<C: Refinement> TypeEnvironment<PolymorphicType<Tau<C>>> {
    pub fn append(&mut self, x: &TypeEnvironment<PolymorphicType<Tau<C>>>) {
        for (k, v) in x.map.iter() {
            match self.map.get_mut(k) {
                Some(w) => {
                    if w.len() == 1 && w[0].is_bot() {
                        *w = vec![];
                    }
                    if w.len() != 1 || !w[0].is_top() {
                        for t in v {
                            add_if_not_exist(w, t.clone());
                        }
                    }
                }
                None => {
                    self.map.insert(*k, v.iter().cloned().collect());
                }
            }
        }
    }
    pub fn merge(
        env1: &TypeEnvironment<Tau<C>>,
        env2: &TypeEnvironment<Tau<C>>,
    ) -> TypeEnvironment<Tau<C>> {
        let mut map: HashMap<Ident, Vec<Tau<C>>> = HashMap::new();
        for (k, v) in env1.map.iter() {
            map.insert(*k, v.iter().cloned().collect());
        }
        for (k, ts) in env2.map.iter() {
            match map.get_mut(k) {
                Some(vs) => {
                    for t in ts {
                        add_if_not_exist(vs, t.clone());
                    }
                }
                None => {
                    map.insert(*k, ts.iter().cloned().collect());
                }
            }
        }
        TypeEnvironment { map }
    }
    pub fn add_top(&mut self, v: Ident, st: &SType) {
        self.add(v, PolymorphicType::mk_top(st));
    }

    pub fn add_bot(&mut self, v: Ident, st: &SType) {
        self.add(v, PolymorphicType::mk_bot(st));
    }
}

impl TyEnv {
    pub fn shrink(&mut self) {
        let mut new_map = HashMap::new();
        for (k, ts) in self.map.iter() {
            let mut new_ts = Vec::new();
            for (i, t) in ts.iter().enumerate() {
                let mut required = true;
                for s in new_ts.iter().chain(ts[i + 1..].iter()) {
                    if PTy::check_subtype_polymorphic(s, t) {
                        // s can become t by using the subsumption rule, so t is no longer required in the environment.
                        required = false;
                        break;
                    }
                }
                if required {
                    new_ts.push(t.clone())
                }
            }
            new_map.insert(*k, new_ts);
        }
        self.map = new_map;
    }
    pub fn optimize(&mut self) {
        let mut new_map = HashMap::new();
        for (k, ts) in self.map.iter() {
            let ts = ts.iter().map(|t| t.optimize()).collect();
            new_map.insert(*k, ts);
        }
        self.map = new_map;
    }
}

#[test]
fn test_tyenv_shrink() {
    let (t1, t2) = generate_t_and_its_subtype_for_test();
    let mut e = TypeEnvironment::new();
    let x = Ident::fresh();
    e.add(x, t1);
    e.add(x, t2);
    assert_eq!(e.size_pred(&x), 2);
    e.shrink();
    assert_eq!(e.size_pred(&x), 1);
    e.shrink();
    assert_eq!(e.size_pred(&x), 1);

    let t = PTy::mk_bot(&SType::mk_type_prop());
    let t2 = PTy::mk_top(&SType::mk_type_prop());
    let mut e = TypeEnvironment::new();
    let x = Ident::fresh();
    e.add(x, t);
    e.add(x, t2);
    assert_eq!(e.size_pred(&x), 2);
    e.shrink();
    assert_eq!(e.size_pred(&x), 1);
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
            let v: Vec<_> = x.iter().map(|t| least_fml(t.clone())).collect();
            let arg = Goal::mk_ho_disj(&v, x[0].to_sty());
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
    match smt::default_solver().solve(&cnstr, &cnstr.fv()) {
        solver::SolverResult::Sat => true,
        solver::SolverResult::Unsat => false,
        solver::SolverResult::Timeout | solver::SolverResult::Unknown => panic!("smt check fail.."),
    }
}
