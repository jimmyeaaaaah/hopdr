use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Display},
    hash::Hash,
};

use crate::{formula, formula::hes::Goal, solver, solver::smt};
use crate::{formula::Precedence, util::P};
use crate::{
    formula::{fofml, PredKind, TeXFormat, TeXPrinter, Variable},
    title,
};
use crate::{
    formula::{
        Bot, Constraint, ConstraintExpr, DerefPtr, FirstOrderLogic, Fv, Ident, Logic, Negation, Op,
        OpExpr, OpKind, Polarity, Rename, Subst, Top, Type as SType, TypeKind as STypeKind,
    },
    util::Pretty,
};

use rpds::Stack;

#[derive(Debug, Hash)]
pub enum TauKind<C> {
    Proposition(C),
    IArrow(Ident, Tau<C>),
    Arrow(Vec<Tau<C>>, Tau<C>),
    PTy(Ident, Tau<C>),
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
    + Hash
    + fmt::Display
    + Pretty
    + Precedence
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
        + Hash
        + fmt::Display
        + Pretty
        + Precedence
{
}

pub struct Positive {}

#[derive(Debug)]
pub enum Error {
    TypeError,
    SMTTimeout,
    SMTUnknown,
}

impl Error {
    fn to_str(&self) -> &'static str {
        match self {
            Error::TypeError => "type error",
            Error::SMTTimeout => "SMT Timeout",
            Error::SMTUnknown => "SMT Unknown",
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_str())
    }
}

impl<C: Pretty> fmt::Display for Tau<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.pretty_display())
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
                if t1.is_empty() {
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

            TauKind::PTy(arg, ty) => {
                write!(f, r"\forall")?;
                write!(f, r" {}", TeXPrinter(arg))?;
                write!(f, ". {}", TeXPrinter(ty))
            }
        }
    }
}

impl<C: Refinement> PartialEq for Tau<C> {
    fn eq(&self, other: &Self) -> bool {
        let r = match (self.kind(), other.kind()) {
            (TauKind::Proposition(c), TauKind::Proposition(c2)) => c == c2,
            (TauKind::PTy(x1, t1), TauKind::PTy(x2, t2))
            | (TauKind::IArrow(x1, t1), TauKind::IArrow(x2, t2)) => {
                let y = Ident::fresh();
                let t1 = t1.rename(x1, &y);
                let t2 = t2.rename(x2, &y);
                t1 == t2
            }
            (TauKind::Arrow(ts1, t1), TauKind::Arrow(ts2, t2)) => t1 == t2 && ts1 == ts2,
            (_, _) => false,
        };
        r
    }
}

impl<C: Refinement> Eq for Tau<C> {}

#[test]
fn test_eq_for_rtype() {
    let x = Ident::fresh();
    let c = Constraint::mk_eq(Op::mk_var(x), Op::mk_const(0));
    let y = Ident::fresh();
    let c2 = Constraint::mk_eq(Op::mk_var(y), Op::mk_const(0));
    let t = Ty::mk_prop_ty(c);
    let t2 = Ty::mk_prop_ty(c2);
    let t = Ty::mk_iarrow(x, t);
    let t2 = Ty::mk_iarrow(y, t2);
    assert_eq!(t, t2)
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
            TauKind::PTy(_, t) => t.is_top(),
        }
    }
}

impl<C: Refinement> TBot for Tau<C> {
    fn mk_bot(st: &SType) -> Self {
        Tau::new(TyKind::new_bot(st))
    }
    fn is_bot(&self) -> bool {
        if self.rty().is_false() {
            return true;
        }
        match self.kind() {
            TauKind::Proposition(c) => c.is_false(),
            TauKind::IArrow(_, t) => t.is_bot(),
            TauKind::Arrow(s, t) if s.len() == 1 => s[0].is_top() && t.is_bot(),
            TauKind::Arrow(_, _) => false,
            TauKind::PTy(_, t) => t.is_bot(),
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
            TauKind::IArrow(z, _) | TauKind::PTy(z, _) if x == z => self.clone(),
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
            TauKind::PTy(z, t) if y == z => {
                let z2 = Ident::fresh();
                let t = t.rename(z, &z2);
                Self::mk_poly_ty(z2, t.rename(x, y))
            }
            TauKind::PTy(z, t) => Self::mk_poly_ty(*z, t.rename(x, y)),
        }
    }
}

impl<C: Refinement> Subst for Tau<C> {
    type Id = Ident;
    type Item = Op;

    fn subst(&self, x: &Self::Id, v: &Self::Item) -> Self {
        match self.kind() {
            TauKind::Proposition(c) => Self::mk_prop_ty(c.subst(x, v)),
            TauKind::IArrow(y, _) | TauKind::PTy(y, _) if y == x => self.clone(),
            TauKind::IArrow(y, t) => Self::mk_iarrow(*y, t.subst(x, v)),
            TauKind::Arrow(ts, t) => {
                let ts = ts.iter().map(|t| t.subst(x, v)).collect();
                let t = t.subst(x, v);
                Self::mk_arrow(ts, t)
            }
            TauKind::PTy(y, t) => Self::mk_poly_ty(*y, t.subst(x, v)),
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
            TauKind::PTy(x, t) => Tau::mk_poly_ty(*x, t.deref_ptr(id)),
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
        fn inner<C: Refinement>(t: &Tau<C>, fvs: &mut HashSet<Ident>) {
            match t.kind() {
                TauKind::Proposition(c) => {
                    c.fv_with_vec(fvs);
                }
                TauKind::IArrow(i, t) | TauKind::PTy(i, t) => {
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
        let t = self.alpha_renaming();
        inner(&t, fvs)
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
            TauKind::PTy(x, t) => C::mk_exists_int(*x, t.rty()),
        }
    }
    pub fn rty_no_exists(&self) -> C {
        match self.kind() {
            TauKind::Proposition(c) => c.clone(),
            TauKind::IArrow(_, t) => t.rty_no_exists(),
            TauKind::PTy(_, t) => t.rty_no_exists(),
            TauKind::Arrow(_, t) => t.rty_no_exists(),
        }
    }

    /// conjoin c as the context
    pub fn conjoin_constraint_to_arg(&self, c: &C) -> Self {
        match self.kind() {
            TauKind::Proposition(c_old) => {
                //let c_new = C::mk_disj(c.clone().negate().unwrap(), c_old.clone());
                let c_new = C::mk_conj(c.clone(), c_old.clone());
                Self::mk_prop_ty(c_new)
            }
            TauKind::IArrow(i, t) => {
                let t = t.conjoin_constraint_to_arg(c);
                Self::mk_iarrow(*i, t)
            }
            TauKind::PTy(i, t) => {
                let t = t.conjoin_constraint_to_arg(c);
                Self::mk_poly_ty(*i, t)
            }
            TauKind::Arrow(ts, t) => {
                let t = t.conjoin_constraint_to_arg(c);
                let ts = ts.iter().map(|t| t.conjoin_constraint_to_arg(c)).collect();
                Self::mk_arrow(ts, t)
            }
        }
    }

    /// conjoin c as the context
    pub fn conjoin_constraint(&self, c: &C) -> Self {
        match self.kind() {
            TauKind::Proposition(c_old) => {
                let c_new = C::mk_conj(c.clone(), c_old.clone());
                Self::mk_prop_ty(c_new)
            }
            TauKind::IArrow(i, t) => {
                let t = t.conjoin_constraint(c);
                Self::mk_iarrow(*i, t)
            }
            TauKind::PTy(i, t) => {
                let t = t.conjoin_constraint(c);
                Self::mk_poly_ty(*i, t)
            }
            TauKind::Arrow(ts, t) => {
                let t = t.conjoin_constraint(c);
                let ts = ts.iter().map(|t| t.conjoin_constraint_to_arg(c)).collect();
                Self::mk_arrow(ts, t)
            }
        }
    }
    /// conjoin c to rty(self)
    pub fn conjoin_constraint_to_rty(&self, c: &C) -> Self {
        match self.kind() {
            TauKind::Proposition(c_old) => {
                let c_new = C::mk_conj(c_old.clone(), c.clone());
                Self::mk_prop_ty(c_new)
            }
            TauKind::IArrow(i, t) => {
                let t = t.conjoin_constraint(c);
                Self::mk_iarrow(*i, t)
            }
            TauKind::PTy(i, t) => {
                let t = t.conjoin_constraint(c);
                Self::mk_poly_ty(*i, t)
            }
            TauKind::Arrow(ts, t) => {
                let t = t.conjoin_constraint(c);
                Self::mk_arrow(ts.clone(), t)
            }
        }
    }
    /// returns the constraint that is equivalent to hold constraint |- t <= s
    /// and coefficient variables of the constraints that were introduced for
    /// checking polymorphic type substyping
    pub fn check_subtype(
        constraint: &C,
        t: &Tau<C>,
        s: &Tau<C>,
        coefficients: &mut Stack<Ident>,
    ) -> C {
        // V; θ ▹ [e/x]τ₁ ≤ τ₂     x ∉ Fv(θ)   {y: int | y ∈ V } ⊢ e : int
        // ------------------------------------------------------------ [AllL]
        //                          ∀x.τ₁ ≤ τ₂
        //
        // V ∪ {x}; θ ▹ τ₁ ≤ τ₂    x ∉ Fv(θ) ∪ FIV(τ₁)
        // ----------------------------------------- [AllR]
        //             V; θ ▹ τ₁ ≤  ∀x. τ₂
        match (t.kind(), s.kind()) {
            (TauKind::Proposition(c1), TauKind::Proposition(c2)) => {
                C::mk_implies_opt(C::mk_conj(constraint.clone(), c2.clone()), c1.clone()).unwrap()
            }
            (TauKind::IArrow(x1, t1), TauKind::IArrow(x2, t2)) => {
                let t2 = t2.rename(x2, x1);
                Tau::check_subtype(constraint, t1, &t2, coefficients)
            }
            (TauKind::Arrow(ts1, t1), TauKind::Arrow(ts2, t2)) => {
                // check ts2 <: ts1
                let mut result_constraint = Tau::check_subtype(constraint, t1, t2, coefficients);
                // ⋀ᵢ tᵢ ≺ ⋀ⱼt'ⱼ ⇔∀ t'ⱼ. ∃ tᵢ. tᵢ ≺ t'ⱼ
                let arg_constraint = C::mk_conj(constraint.clone(), t2.rty());
                for tj in ts1 {
                    let mut tmpc = C::mk_false();
                    for ti in ts2 {
                        tmpc = C::mk_disj(
                            tmpc,
                            Tau::check_subtype(&arg_constraint, ti, tj, coefficients),
                        );
                    }
                    result_constraint = C::mk_conj(result_constraint, tmpc);
                }
                result_constraint
            }
            // the order [AllR] -> [AllL] is important
            // since we instantiate the type by using s's free variables
            // [AllR]
            (_, TauKind::PTy(x, s)) => {
                let fresh = Ident::fresh();
                let sprime = s.rename(x, &fresh);
                Self::check_subtype(constraint, t, &sprime, coefficients)
            }
            // [AllL]
            (TauKind::PTy(_, _), _) => {
                let vars = s.fv();
                let t = t.instantiate(&vars, coefficients);
                Self::check_subtype(constraint, &t, s, coefficients)
            }
            (_, _) => panic!("fatal"),
        }
    }
    pub fn check_subtype_result(t: &Tau<C>, s: &Tau<C>) -> Option<C> {
        match (t.kind(), s.kind()) {
            (TauKind::Proposition(c1), TauKind::Proposition(c2)) => {
                Some(C::mk_implies_opt(c2.clone(), c1.clone()).unwrap())
            }
            (TauKind::IArrow(x1, t1), TauKind::IArrow(x2, t2)) => {
                let t2 = t2.rename(x2, x1);
                Tau::check_subtype_result(t1, &t2)
            }
            (TauKind::Arrow(ts1, t1), TauKind::Arrow(ts2, t2)) => {
                // check ts2 <: ts1
                if ts1.iter().zip(ts2.iter()).all(|(t1, t2)| t1 == t2) {
                    Tau::check_subtype_result(t1, t2)
                } else {
                    None
                }
            }
            (_, _) => panic!("fatal"),
        }
    }
    /// Create template without any polymorphic types
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
            TauKind::PTy(x, t) => t.clone_with_template(fvs),
            TauKind::Arrow(ts, t) => {
                let ts = ts.iter().map(|s| s.clone_with_template(fvs)).collect();
                let t = t.clone_with_template(fvs);
                Tau::mk_arrow(ts, t)
            }
        }
    }
    /// generates a refinement type that holds template variables for the prop_ty's constraints
    pub fn from_sty(sty: &SType, fvs: &HashSet<Ident>) -> Tau<fofml::Atom> {
        let b: Tau<fofml::Atom> = Tau::mk_bot(sty);
        let mut fvs = fvs.clone();
        b.clone_with_template(&mut fvs)
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
    pub fn alpha_renaming(&self) -> Self {
        match self.kind() {
            TauKind::Proposition(_) => self.clone(),
            TauKind::IArrow(x, t) => {
                let new_x = Ident::fresh();
                let t = t.rename(x, &new_x);
                let t = t.alpha_renaming();
                Tau::mk_iarrow(new_x, t)
            }
            TauKind::PTy(x, t) => {
                let new_x = Ident::fresh();
                let t = t.rename(x, &new_x);
                let t = t.alpha_renaming();
                Tau::mk_poly_ty(new_x, t)
            }
            TauKind::Arrow(ts, t) => {
                let ts = ts.iter().map(|t| t.alpha_renaming()).collect();
                let t = t.alpha_renaming();
                Tau::mk_arrow(ts, t)
            }
        }
    }
    pub fn mk_arrow(t: Vec<Tau<C>>, s: Tau<C>) -> Tau<C> {
        Tau::new(TauKind::Arrow(t, s))
    }
    pub fn optimize_trivial_intersection(&self) -> Self {
        match self.kind() {
            TauKind::Proposition(c) => Self::mk_prop_ty(c.clone()),
            TauKind::IArrow(x, t) => Self::mk_iarrow(*x, t.optimize_trivial_intersection()),
            TauKind::PTy(x, t) => Self::mk_poly_ty(*x, t.optimize_trivial_intersection()),
            TauKind::Arrow(ts, t) => {
                let t_fst = ts[0].clone();
                let mut ts: Vec<_> = ts
                    .iter()
                    .map(|t| t.optimize_trivial_intersection())
                    .filter(|t| !t.is_bot())
                    .collect();
                if ts.len() == 0 {
                    // t_fst must be bot ty where all bot types are filtered out.
                    ts.push(t_fst);
                }
                Tau::mk_arrow(ts, t.optimize_trivial_intersection())
            }
        }
    }
    pub fn prop<'a>(&'a self) -> &'a C {
        match self.kind() {
            TauKind::Proposition(c) => c,
            _ => panic!("program error"),
        }
    }
    pub fn iarrow<'a>(&'a self) -> (&'a Ident, &'a Self) {
        match self.kind() {
            TauKind::IArrow(x, t) => (x, t),
            _ => panic!("program error"),
        }
    }
    pub fn arrow<'a>(&'a self) -> (&'a Vec<Self>, &'a Self) {
        match self.kind() {
            TauKind::Arrow(ts, t) => (ts, t),
            _ => panic!("program error"),
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
        Tau::check_subtype_polymorphic(t1, t2)
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
            TauKind::PTy(x, t) => Tau::mk_poly_ty(*x, t.clone().into()),
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
            TauKind::PTy(v, x) => Tau::mk_poly_ty(*v, x.assign(model)),
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
            TauKind::PTy(x, t) => t.clone_with_rty_template(constraint, fvs),
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
            TauKind::PTy(_, t) => t.to_sty(),
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
    pub fn mk_poly_ty(arg: Ident, t: Tau<C>) -> Tau<C> {
        Tau::new(TauKind::PTy(arg, t))
    }
    pub fn is_proposition(&self) -> bool {
        matches!(self.kind(), TauKind::Proposition(_))
    }
    pub fn is_arrow(&self) -> bool {
        matches!(self.kind(), TauKind::Arrow(_, _))
    }
    pub fn is_poly_ty(&self) -> bool {
        matches!(self.kind(), TauKind::PTy(_, _))
    }
    pub fn order(&self) -> usize {
        match self.kind() {
            TauKind::Proposition(_) => 0,
            TauKind::IArrow(_, t) | TauKind::PTy(_, t) => std::cmp::max(1, t.order()),
            TauKind::Arrow(ts, y) => {
                // FIXIME: this is wrong definition
                let o1 = if ts.is_empty() { 0 } else { ts[0].order() };
                let o2 = y.order();
                std::cmp::max(o1 + 1, o2)
            }
        }
    }
    /// returns the set of polymorphic variables at the top of the type
    // FIXME: implement Ident iterator
    pub fn vars(&self) -> HashSet<Ident> {
        let mut vars = HashSet::new();
        let mut ty = self;
        loop {
            match ty.kind() {
                TauKind::PTy(x, t) => {
                    vars.insert(*x);
                    ty = t;
                }
                _ => break vars,
            }
        }
    }
    /// returns the body of the type.
    /// body means the type without polymorphic variables at the top of the type.
    // FIXME: implement Ident iterator
    pub fn ty(&self) -> Self {
        let mut ty = self;
        loop {
            match ty.kind() {
                TauKind::PTy(x, t) => {
                    ty = t;
                }
                _ => break ty.clone(),
            }
        }
    }
}
impl<C: Refinement> Tau<C> {
    pub fn poly(mut ty: Self) -> Self {
        let vars = ty.fv();
        for var in vars {
            ty = Self::mk_poly_ty(var, ty);
        }
        ty
    }
    pub fn body_ty(&self) -> Self {
        match self.kind() {
            TauKind::Proposition(_) | TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => self.clone(),
            TauKind::PTy(_, t) => t.body_ty(),
        }
    }
}

// optimization methods of Ty
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
            TauKind::PTy(x, t) => Ty::mk_poly_ty(*x, t.optimize_constraint_reduction()),
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
            TauKind::PTy(x, y) => {
                let y = y.optimize_intersection_trivial();
                Ty::mk_poly_ty(*x, y)
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
                let ts_new: Vec<_> = ts_new
                    .iter()
                    .map(|t| t.optimize_intersection_trivial())
                    .collect();

                Ty::mk_arrow(ts_new, t)
            }
        }
    }
    /// for all intersection types θ |- t1 /\ t2, this method tries to find a type t
    /// such that θ |- t <: t1 and θ |- t <: t2
    #[allow(dead_code)]
    fn optimize_reducing_intersection(&self) -> Self {
        debug!("optimize_reducing_intersection: {self}");

        fn try_generate_new_type(
            polarity: formula::Polarity,
            env: &mut HashSet<Ident>,
            constraint: &Constraint,
            ts: &[Ty],
        ) -> Vec<Ty> {
            let t = &ts[0].clone_with_template(env);
            let constraint = constraint.clone().into();
            let mut clauses = Vec::new();
            let mut coefficients = Stack::new();
            for s in ts.iter().cloned() {
                let c = match polarity {
                    Polarity::Positive => {
                        Tau::check_subtype(&constraint, t, &s.into(), &mut coefficients)
                    }
                    Polarity::Negative => {
                        Tau::check_subtype(&constraint, &s.into(), t, &mut coefficients)
                    }
                };
                // cannot handle polymorphic types
                if coefficients.iter().next().is_some() {
                    return ts.to_owned();
                }
                match c.to_chcs_or_pcsps() {
                    either::Either::Left(chcs) => {
                        for chc in chcs {
                            clauses.push(chc);
                        }
                    }
                    either::Either::Right(_) => panic!("program error"),
                }
            }
            let _ = match solver::chc::default_solver().solve(&clauses) {
                solver::chc::CHCResult::Sat(m) => m,
                solver::chc::CHCResult::Unsat => return ts.to_owned(),
                solver::chc::CHCResult::Unknown | solver::chc::CHCResult::Timeout => {
                    panic!("panic")
                }
            };
            let model = solver::interpolation::solve(&clauses, &Default::default());
            let t = t.assign(&model.model);
            vec![t]
        }

        fn go(
            polarity: formula::Polarity,
            env: &mut HashSet<Ident>,
            constraint: &Constraint,
            ty: &Ty,
        ) -> Ty {
            match ty.kind() {
                TauKind::Proposition(_) => ty.clone(),
                TauKind::IArrow(x, t) => {
                    let t = go(polarity, env, constraint, t);
                    Ty::mk_iarrow(*x, t)
                }
                TauKind::PTy(x, t) => {
                    let t = go(polarity, env, constraint, t);
                    Ty::mk_poly_ty(*x, t)
                }
                TauKind::Arrow(ts, t) => {
                    let t = go(polarity, env, constraint, t);
                    let constraint = Constraint::mk_conj(constraint.clone(), t.rty());
                    let ts: Vec<_> = ts
                        .iter()
                        .map(|t| go(polarity.rev(), env, &constraint, t))
                        .collect();
                    let ts = if ts.len() <= 1 {
                        ts
                    } else {
                        try_generate_new_type(polarity, env, &constraint, &ts)
                    };

                    Ty::mk_arrow(ts, t)
                }
            }
        }

        go(
            formula::Polarity::Positive,
            &mut HashSet::new(),
            &Constraint::mk_true(),
            self,
        )
    }

    pub fn optimize_non_poly(&self) -> Self {
        // Pass
        //  - optimize_constraint_reduction
        //  - optimize_intersection_trivial
        //  # - optimize_intersection_subsumption
        let t = self.clone();
        debug!("Ty::optimize before: {t}");
        let t = t.optimize_constraint_reduction();
        debug!("optimizeed by optimize_constraint_reduction: {t}");
        let t = t.optimize_intersection_trivial();
        debug!("optimizeed by optimize_intersection_trivial: {t}");
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

#[test]
fn test_optimize_reducing() {
    // ∀ z: x:int → (y: int → *[x=y]) ∧   (y: int → *[x=y+1]) → *[T]
    let x = Ident::fresh();
    let y = Ident::fresh();

    let t1 = Ty::mk_iarrow(
        y,
        Ty::mk_prop_ty(Constraint::mk_eq(Op::mk_var(x), Op::mk_var(y))),
    );
    let t2 = Ty::mk_iarrow(
        y,
        Ty::mk_prop_ty(Constraint::mk_eq(
            Op::mk_var(x),
            Op::mk_add(Op::one(), Op::mk_var(y)),
        )),
    );

    let t = Ty::mk_arrow(vec![t1, t2], Ty::mk_prop_ty(Constraint::mk_true()));
    let t = Ty::mk_iarrow(x, t);
    let t = t.optimize_reducing_intersection();
    match t.kind() {
        TauKind::IArrow(_, t) => match t.kind() {
            TauKind::Arrow(ts, _) => {
                println!("ts: {}", ts[0]);
                assert_eq!(ts.len(), 1)
            }
            _ => panic!("program error"),
        },
        _ => panic!("program error"),
    }
}

/// `generate_t_and_its_subtype_for_test` return the following two refinement types
///   - t: ∀ x₁, x₂. (y:int → •〈y =x₁+x₂〉)→z:int→ • 〈z=x₁+x₂〉
///   - s: ∀ x₃.(y:int→•〈y=x₃〉)→z:int→•〈z=x₃〉
/// Note that t ≤ s holds.
#[cfg(test)]
fn generate_t_and_its_subtype_for_test() -> (Ty, Ty) {
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
    (Ty::poly(t1), Ty::poly(t2))
}

#[cfg(test)]
fn generate_t_and_its_subtype_for_test2() -> (Ty, Ty) {
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
    (Ty::poly(t1), Ty::poly(t2))
}

// template for polymorphic types
pub fn generate_arithmetic_template(ints: &HashSet<Ident>, coefficients: &mut Stack<Ident>) -> Op {
    // linear template
    let c_id = Ident::fresh();
    let mut o = Op::mk_var(c_id);
    coefficients.push_mut(c_id);
    // linear expr
    for int in ints {
        let tmp = Ident::fresh();
        // o += c_i * x_i
        let t = Op::mk_bin_op(formula::OpKind::Mul, Op::mk_var(tmp), Op::mk_var(*int));
        o = Op::mk_add(o, t);
        coefficients.push_mut(tmp);
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
    let o = generate_arithmetic_template(&ints, &mut coefs);
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

/// given left = right, by transposing terms, returns (ident, op) where
/// ident in `vars`
/// assumption: no OpExpr::Ptr  (ops are `flatten`ed)
///
/// this is intended to be an auxiliary function for PTy::optimize_trivial_ty
fn preprocess_eq(left: &Op, right: &Op, vars: &HashSet<Ident>) -> Option<(Ident, Op)> {
    // 0 = right - left
    let right = Op::mk_sub(right.clone(), left.clone());
    let additions = right.expand_expr_to_vec();
    let mut result_ops = Op::mk_const(0);
    let mut already_found = None; // Option<(ident, is_neg)>
    fn check(c: &Op, o: &Op) -> Option<(Ident, bool)> {
        let is_neg = match c.kind() {
            OpExpr::Const(-1) => true,
            OpExpr::Const(1) => false,
            OpExpr::Const(_) | OpExpr::Op(_, _, _) | OpExpr::Var(_) | OpExpr::Ptr(_, _) => {
                return None
            }
        };
        match o.kind() {
            OpExpr::Var(x) => Some((*x, is_neg)),
            OpExpr::Op(_, _, _) | OpExpr::Const(_) | OpExpr::Ptr(_, _) => None,
        }
    }
    for v in additions {
        match v.kind() {
            OpExpr::Var(x) if already_found.is_none() && vars.contains(x) => {
                already_found = Some((*x, false));
            }
            OpExpr::Op(OpKind::Mul, o1, o2) => match check(o1, o2).or_else(|| check(o2, o1)) {
                Some((x, is_neg)) if already_found.is_none() && vars.contains(&x) => {
                    already_found = Some((x, is_neg))
                }
                Some(_) | None => result_ops = Op::mk_add(result_ops, v.clone()),
            },
            OpExpr::Op(_, _, _) | OpExpr::Var(_) | OpExpr::Const(_) => {
                result_ops = Op::mk_add(result_ops, v.clone())
            }
            OpExpr::Ptr(_, _) => panic!("assumption violated: ptrs are flattened"),
        }
    }
    already_found.map(|(ident, is_neg)| {
        (
            ident,
            // a little complicated, but if is_neg is true,
            // that is -x + ... = 0; therefore, ... will not be negated.
            if is_neg {
                result_ops
            } else {
                result_ops.negate()
            },
        )
    })
}

// search for x == y where x in vars and y's free variables are a set set of args
// if disjunctions appear, `search` won't search for eqs anymore.
fn search_eqs_from_constraint(
    c: &Constraint,
    pairs: &mut Stack<(Ident, Op)>,
    vars: &HashSet<Ident>,
) {
    match c.kind() {
        ConstraintExpr::Pred(PredKind::Eq, l) if l.len() == 2 => {
            debug!("eq: {} == {}", l[0], l[1]);
            let left = l[0].flatten();
            let right = l[1].flatten();
            match (left.kind(), right.kind()) {
                (OpExpr::Var(x), _) if vars.contains(x) && l[1].fv().is_disjoint(vars) => {
                    pairs.push_mut((*x, l[1].clone()))
                }
                (_, OpExpr::Var(x)) if vars.contains(x) && l[0].fv().is_disjoint(vars) => {
                    pairs.push_mut((*x, l[0].clone()))
                }
                (_, _) => match preprocess_eq(&left, &right, vars) {
                    Some((x, o)) if vars.contains(&x) && o.fv().is_disjoint(vars) => {
                        pairs.push_mut((x, o))
                    }
                    Some(_) | None => (),
                },
            };
        }
        ConstraintExpr::True | ConstraintExpr::False | ConstraintExpr::Pred(_, _) => (),
        ConstraintExpr::Conj(c1, c2) => {
            search_eqs_from_constraint(c1, pairs, vars);
            search_eqs_from_constraint(c2, pairs, vars);
        }
        ConstraintExpr::Disj(_, _) => (),
        ConstraintExpr::Quantifier(_, _, _) => (),
    }
}

#[test]
fn test_preprocess_eq() {
    use formula::Env;
    // x - 1 = 0  => x = 1 + 0
    let x = Ident::fresh();
    let left = Op::mk_sub(Op::mk_var(x), Op::one());
    let right = Op::zero();
    let mut var = HashSet::new();
    assert!(preprocess_eq(&left, &right, &var).is_none());
    var.insert(x);
    let (ident, o) = preprocess_eq(&left, &right, &var).unwrap();
    assert_eq!(ident, x);
    assert_eq!(o.eval(&Env::new()), Some(1))
}

impl Ty {
    pub fn check_subtype_polymorphic(t: &Self, s: &Self) -> bool {
        // . constraint
        let mut coefficients = Stack::new();
        debug!("check |- {t} <= {s}");
        let constraint = Tau::check_subtype(&Constraint::mk_true(), t, s, &mut coefficients);
        debug!("constraint: {constraint}");
        // 4. univ 5.existential quantifier 6. smt solver
        let mut sol = solver::smt::smt_solver(solver::SMTSolverType::Auto);
        let coefficients: HashSet<Ident> = coefficients.iter().cloned().collect();
        let mut vprime = HashSet::new();
        for fv in constraint.fv() {
            if !coefficients.contains(&fv) {
                vprime.insert(fv);
            }
        }
        debug!("vprime: {vprime:?}");
        let m = sol.solve_with_model(&constraint, &vprime, &coefficients);
        match &m {
            Ok(model) => debug!("model: {model}"),
            Err(_) => (),
        }
        m.is_ok()
    }
    /// This optimization tries to remove polymorphic variable by using equational constraints
    ///
    /// ## Example
    ///
    /// ∀x_18. (x_150: int -> ((x_19: int -> bool[(0 <= x_19) ∧ (x_18 <= 0)])-> bool[x_150 = x_18]))
    /// ---> x_150: int -> ((x_19: int -> bool[(0 <= x_19) ∧ (x_150 <= 0)])-> bool[T])
    ///
    fn optimize_trivial_ty(&self) -> Self {
        // Tr(*[θ], args, (xᵢ=oᵢ)ᵢ)
        //     = *[θₙ'] for each xᵢ=oᵢ,  θᵢ₊₁'=[oᵢ/xᵢ]θᵢ' if fv(oᵢ) ⊂ args, otherwise θᵢ'
        // Tr(x:int → τ, args, (xᵢ=oᵢ)ᵢ)
        //     = x:int → τ' where τ' = Tr(τ, x::args, eqs)
        // Tr(∧τᵢ → τ, args, eqs)
        //     = τᵢ' → τ'
        //        where
        //          τ' = Tr(τ, args, eqs)
        //        and
        //          τᵢ' = Tr(τᵢ, args, eqs)
        //

        type Eqs = Stack<(Ident, Op)>;
        fn tr(
            t: &Ty,
            args: &mut HashSet<Ident>,
            eqs: Eqs,
            vars: &HashSet<Ident>,
            toplevel: bool,
        ) -> Ty {
            match t.kind() {
                TauKind::Proposition(c) => {
                    let c = if !toplevel {
                        let mut c = c.clone();
                        debug!("translating: {c}");
                        debug!("args: {args:?}");
                        for (x, o) in eqs.iter() {
                            debug!("replace: {x} = {o}");
                            if o.fv().is_subset(args) {
                                c = c.subst(x, o);
                            }
                        }
                        c
                    } else {
                        c.clone()
                    };
                    Ty::mk_prop_ty(c)
                }
                TauKind::IArrow(x, t) => {
                    let should_remove = args.insert(*x);
                    let t = tr(t, args, eqs, vars, toplevel);
                    if should_remove {
                        args.remove(x);
                    }
                    Ty::mk_iarrow(*x, t)
                }
                TauKind::PTy(x, t) => {
                    let should_remove = args.insert(*x);
                    let t = tr(t, args, eqs, vars, toplevel);
                    if should_remove {
                        args.remove(x);
                    }
                    Ty::mk_poly_ty(*x, t)
                }
                TauKind::Arrow(ts, t) => {
                    let t = tr(t, args, eqs.clone(), vars, toplevel);
                    let ts = ts
                        .iter()
                        .map(|t| tr(t, args, eqs.clone(), vars, false))
                        .collect();
                    Ty::mk_arrow(ts, t)
                }
            }
        }
        fn eq(
            c: &Constraint,
            mut s: Stack<(Ident, Op)>,
            vars: &HashSet<Ident>,
        ) -> Stack<(Ident, Op)> {
            search_eqs_from_constraint(c, &mut s, vars);
            s
        }

        let mut args = HashSet::new();
        let vars: HashSet<Ident> = self.vars().into_iter().collect();
        let ty = &self.ty();
        // Make sure there is no variable name collison such as
        // // ∀z. (x: int → *[x = z]) → x: int → *[x = z]
        let ty = ty.alpha_renaming();
        let eqs = eq(&ty.rty_no_exists(), Stack::new(), &vars);

        title!("optimize_trivial_ty::tr");
        debug!("eqs");
        for (x, o) in eqs.iter() {
            debug!("- {x} = {o}");
        }

        let mut new_ty = tr(&ty, &mut args, eqs.clone(), &vars, true);

        fn check_if_removable(ty: &Ty, x: Ident, toplevel: bool) -> bool {
            match ty.kind() {
                TauKind::Proposition(_) if toplevel => true,
                TauKind::Proposition(c) => !c.fv().contains(&x),
                TauKind::IArrow(_, r) | TauKind::PTy(_, r) => check_if_removable(r, x, toplevel),
                TauKind::Arrow(ts, t) => {
                    for t in ts.iter() {
                        if !check_if_removable(t, x, false) {
                            return false;
                        }
                    }
                    check_if_removable(t, x, toplevel)
                }
            }
        }
        let mut eq_idents = HashMap::new();
        for (x, o) in eqs.iter() {
            eq_idents
                .entry(*x)
                .or_insert_with(|| Vec::new())
                .push(o.clone())
        }

        for (x, os) in eq_idents {
            if os.len() == 1 && check_if_removable(&new_ty, x, true) {
                new_ty = new_ty.subst(&x, &os[0])
            }
        }

        Ty::poly(new_ty)
    }

    /// Using equalities that appear in the argument position of the given type,
    /// this function instantiates some types.
    /// ex. ∀z. x: int -> (y: int -> *[z=x]) -> *[z >= x]
    ///   -> x:int -> (y: int -> *[T]) -> *[x >= x]
    pub fn generate_trivial_types_by_eq(&self) -> Vec<Self> {
        // collect eqs
        fn get_eqs_from_ty(ty: &Ty, eqs: &mut Stack<(Ident, Op)>, vars: &HashSet<Ident>) {
            match ty.kind() {
                TauKind::Proposition(c) => {
                    search_eqs_from_constraint(c, eqs, vars);
                }
                TauKind::IArrow(_, t) | TauKind::PTy(_, t) => {
                    get_eqs_from_ty(t, eqs, vars);
                }
                TauKind::Arrow(ts, t) => {
                    for t in ts.iter() {
                        get_eqs_from_ty(t, eqs, vars);
                    }
                    get_eqs_from_ty(t, eqs, vars);
                }
            }
        }
        if self.vars().len() != 1 {
            return Vec::new();
        }
        let mut eqs = Stack::new();
        get_eqs_from_ty(&self.ty(), &mut eqs, &self.vars());

        let mut result = Vec::new();
        for (v, eq) in eqs.iter() {
            if !self.vars().contains(v) {
                continue;
            }
            let t = self.ty().subst(v, eq);
            let pty = Ty::poly(t);
            result.push(pty);
        }
        if !result.is_empty() {
            title!("generate_trivial_types_by_eq");
            for t in result.iter() {
                debug!("- {t}");
            }
        }
        result
    }

    // replace with `Top` all the occurence of the clause in cnf which contains
    // ident in `var` (polymorphic).
    pub fn optimize_replace_top(&self) -> Self {
        debug!("optimize_replace_top: {self}");
        // check if `var` is not contained in args of `t`
        fn check(t: &Ty, var: &Ident, toplevel: bool) -> bool {
            match t.kind() {
                TauKind::Proposition(_) if toplevel => false,
                TauKind::Proposition(c) => c.fv().contains(var),
                TauKind::IArrow(x, _) | TauKind::PTy(x, _) if x == var => false,
                TauKind::IArrow(_, t) | TauKind::PTy(_, t) => check(t, var, toplevel),
                TauKind::Arrow(ts, t) => {
                    check(t, var, toplevel) || ts.iter().map(|t| check(t, var, false)).any(|y| y)
                }
            }
        }
        fn replace(t: &Ty, var: &Ident, toplevel: bool) -> Ty {
            match t.kind() {
                TauKind::Proposition(c) if toplevel => {
                    let (v, c) = c.to_pnf_raw();
                    let (mut c, replaced) = c.to_dnf().into_iter().fold(
                        (Constraint::mk_false(), 0), // how many times var appeared
                        |(result_constraint, already_replaced), dclause| {
                            let (c, already_replaced) = dclause.to_cnf().into_iter().fold(
                                (Constraint::mk_true(), already_replaced),
                                |(constraint, mut already_replaced), clause| {
                                    if clause.fv().contains(var) {
                                        already_replaced += 1;
                                        if already_replaced == 1 {
                                            // 1. transposing c * `var` <Pred> op
                                            // 2. check c can be evaluated to 1
                                            // 3. if so, returns `constraint` without conjoining clause;
                                            //    otherwise, conjoins the clause and constraint.
                                            //    also, already_replaced is enabled to avoid a contradiction
                                            //    (e.g. x != 0 /\ x = 0  ----> T /\ T)
                                            let clause_new = match clause.kind() {
                                                ConstraintExpr::Pred(_, l) if l.len() == 2 => {
                                                    let left = l[0].clone();
                                                    let right = l[1].clone();
                                                    let l = Op::mk_sub(left, right);
                                                    let vars = vec![*var];
                                                    let l = l.normalize(&vars);
                                                    let coef = &l[0];
                                                    coef.eval_with_empty_env().map_or(clause.clone(), |x| {
                                                        if x == 1 {
                                                            Constraint::mk_true()
                                                        } else {
                                                            clause.clone()
                                                        }
                                                    })
                                                }
                                                ConstraintExpr::Pred(_, _) |
                                                ConstraintExpr::True |
                                                ConstraintExpr::False  | // should not contain any variable
                                                ConstraintExpr::Conj(_, _) |
                                                ConstraintExpr::Disj(_, _) |
                                                ConstraintExpr::Quantifier(_, _, _) => panic!("program error"),
                                            };
                                            (Constraint::mk_conj(constraint, clause_new), already_replaced)
                                        } else {
                                            (Constraint::mk_conj(constraint, clause), already_replaced)
                                        }
                                    } else {
                                        (Constraint::mk_conj(constraint, clause), already_replaced)
                                    }
                                },
                            );
                            (Constraint::mk_disj(result_constraint, c), already_replaced)
                        },
                    );
                    if replaced == 1 {
                        for (q, x) in v {
                            c = Constraint::mk_quantifier(q, x, c);
                        }
                        Ty::mk_prop_ty(c)
                    } else {
                        t.clone()
                    }
                }
                TauKind::Proposition(_) => t.clone(),
                TauKind::IArrow(x, t) => {
                    let t = replace(t, var, toplevel);
                    Ty::mk_iarrow(*x, t)
                }
                TauKind::PTy(x, t) => {
                    let t = replace(t, var, toplevel);
                    Ty::mk_poly_ty(*x, t)
                }
                TauKind::Arrow(ts, t) => {
                    let ts = ts.iter().map(|t| replace(t, var, false)).collect();
                    let t = replace(t, var, toplevel);
                    Ty::mk_arrow(ts, t)
                }
            }
        }
        let mut ty = self.ty().clone();
        let mut replaced = false;
        for v in self.vars().iter() {
            if !check(&ty, v, true) && ty.rty().fv().contains(v) {
                // Should check everytime ty is generated?
                ty = replace(&ty, v, true);
                replaced = true;
            }
        }
        debug!("replaced: {replaced}, ty: {ty}");
        let new_pty = Ty::poly(ty);
        if replaced && Ty::check_subtype_polymorphic(&new_pty, self) {
            new_pty
        } else {
            self.clone()
        }
    }
    fn optimize_ty(&self) -> Self {
        let ty = self.ty().optimize_non_poly();
        Ty::poly(ty)
    }
    pub fn optimize(&self) -> Self {
        debug!("PTy optimize before: {self}");
        let pty = self.optimize_trivial_ty();
        debug!("PTy optimized by optimize_trivial_ty: {pty}");
        let pty = pty.optimize_ty();
        debug!("PTy optimized by ty optimize: {pty}");
        let pty = pty.optimize_replace_top();
        debug!("PTy optimized by optimize_replace_top: {pty}");
        pty.optimize_ty()
    }
}

#[test]
fn test_subtype_polymorphic() {
    let (t1, t2) = generate_t_and_its_subtype_for_test();
    println!("{t1} <= {t2}");
    assert!(Ty::check_subtype_polymorphic(&t1, &t2));
    assert!(Ty::check_subtype_polymorphic(&t2, &t1));
}

#[test]
fn test_subtype_polymorphic2() {
    let (t1, t2) = generate_t_and_its_subtype_for_test2();
    println!("{t1} <= {t2}");
    assert!(Ty::check_subtype_polymorphic(&t1, &t2));
    println!("ok");
    assert!(!Ty::check_subtype_polymorphic(&t2, &t1));
}

#[test]
fn test_subtype_polymorphic_negative2() {
    // ∀z. (((x: int -> *[z = x]) /\ (y: int -> *[y = (1 + z)]))-> (w: int -> *[w = z]))
    //     <: ∀z. ((v: int -> *[v = z])-> (w: int -> *[z = w]))

    let x = Ident::fresh();
    let y = Ident::fresh();
    let z = Ident::fresh();
    let w = Ident::fresh();
    let v = Ident::fresh();

    fn o(x: Ident) -> Op {
        Op::mk_var(x)
    }
    fn p(c: Constraint) -> Ty {
        Ty::mk_prop_ty(c)
    }

    let c1 = Constraint::mk_eq(o(z), o(x));
    let c2 = Constraint::mk_eq(o(y), Op::mk_add(o(z), Op::one()));
    let c3 = Constraint::mk_eq(o(w), o(z));
    let c4 = Constraint::mk_eq(o(v), o(z));

    let t1 = Ty::mk_iarrow(x, p(c1));
    let t2 = Ty::mk_iarrow(y, p(c2));
    let t3 = Ty::mk_iarrow(w, p(c3.clone()));
    let t = Ty::mk_arrow(vec![t1, t2], t3.clone());
    let t = Ty::poly(t);

    let t4 = Ty::mk_iarrow(v, p(c4));
    let s = Ty::mk_arrow_single(t4, t3);
    let s = Ty::poly(s);

    assert!(!Ty::check_subtype_polymorphic(&t, &s));
}

#[test]
fn test_optimize_polymorphic_ty() {
    let x_18 = Ident::fresh();
    let x_150 = Ident::fresh();
    let x_19 = Ident::fresh();
    let zero = Op::mk_const(0);
    let c1 = Constraint::mk_lt(zero.clone(), Op::mk_var(x_19));
    let c2 = Constraint::mk_lt(Op::mk_var(x_18), zero.clone());
    let c3 = Constraint::mk_conj(c1.clone(), c2.clone());
    let c4 = Constraint::mk_eq(Op::mk_var(x_150), Op::mk_var(x_18));
    let t1 = Ty::mk_iarrow(x_19, Ty::mk_prop_ty(c3.clone()));
    let t2 = Ty::mk_arrow_single(t1, Ty::mk_prop_ty(c4.clone()));
    let t3 = Ty::mk_iarrow(x_150, t2);
    let pty = Ty::poly(t3);
    println!("before: {pty}");
    let pty2 = pty.optimize_trivial_ty();
    println!("after: {pty2}");
    assert_eq!(pty2.vars().len(), 0);

    let c5 = Constraint::mk_eq(
        Op::mk_add(Op::mk_var(x_150), Op::one()),
        Op::mk_sub(Op::mk_var(x_18), Op::one()),
    );
    let t1 = Ty::mk_iarrow(x_19, Ty::mk_prop_ty(c3.clone()));
    let t2 = Ty::mk_arrow_single(t1, Ty::mk_prop_ty(c5.clone()));
    let t3 = Ty::mk_iarrow(x_150, t2);
    let pty = Ty::poly(t3);
    println!("before: {pty}");
    let pty2 = pty.optimize_trivial_ty();
    println!("after: {pty2}");
    assert_eq!(pty2.vars().len(), 0);
}

#[test]
fn test_optimize_polymorphic_ty_negative() {
    // ∀z. (x: int → *[x = z]) → x: int → *[x = z]
    let z = Ident::fresh();
    let x = Ident::fresh();

    let eq = Constraint::mk_eq(Op::mk_var(x), Op::mk_var(z));
    let eqt = Ty::mk_prop_ty(eq);
    let t = Ty::mk_iarrow(x, eqt);
    let t = Ty::mk_arrow_single(t.clone(), t);
    let p = Ty::poly(t);
    let p2 = p.optimize_trivial_ty();
    println!("before: {p}");
    println!("after: {p2}");
    assert_eq!(p2.vars().len(), p.vars().len());
}

#[test]
fn test_optimize_replace_top() {
    // ∀z. (x: int → *[x = 0]) → x: int → *[z = 0]
    let z = Ident::fresh();
    let x = Ident::fresh();

    let xeq = Constraint::mk_eq(Op::mk_var(x), Op::mk_const(0));
    let zeq = Constraint::mk_eq(Op::mk_var(z), Op::mk_const(0));
    let zeqt = Ty::mk_prop_ty(zeq.clone());
    let xeqt = Ty::mk_prop_ty(xeq.clone());
    let t1 = Ty::mk_iarrow(x, zeqt.clone());
    let t2 = Ty::mk_iarrow(x, xeqt.clone());
    let t = Ty::mk_arrow_single(t2.clone(), t1.clone());
    let p = Ty::poly(t);
    let p2 = p.optimize_replace_top();
    println!("before: {p}");
    println!("after: {p2}");
    assert!(p2.ty().rty_no_exists().eval_with_empty_env().unwrap());

    // ∀z. (x: int → *[x = 0]) → x: int → *[z = 0 /\ z != 0]
    let zneq = Constraint::mk_neq(Op::mk_var(z), Op::mk_const(0));
    let zneqeq = Constraint::mk_conj(zeq.clone(), zneq.clone());

    let zneqeqt = Ty::mk_prop_ty(zneqeq.clone());
    let t1 = Ty::mk_iarrow(x, zneqeqt.clone());
    let t2 = Ty::mk_iarrow(x, xeqt.clone());
    let t = Ty::mk_arrow_single(t2.clone(), t1.clone());
    let p = Ty::poly(t);
    let p2 = p.optimize_replace_top();
    println!("before: {p}");
    println!("after: {p2}");
    assert_eq!(p2.ty().rty_no_exists(), p.ty().rty_no_exists());

    // ∀z. (x: int → *[x = 0]) → x: int → *[x = 0 \/ (z = 0 /\ x = 1)]
    let xeq01 = Constraint::mk_conj(
        Constraint::mk_eq(Op::mk_var(z), Op::zero()),
        Constraint::mk_eq(Op::mk_var(x), Op::one()),
    );
    let c = Constraint::mk_disj(Constraint::mk_eq(Op::mk_var(x), Op::zero()), xeq01);
    let ct = Ty::mk_prop_ty(c.clone());
    let t1 = Ty::mk_iarrow(x, ct.clone());
    let t2 = Ty::mk_iarrow(x, xeqt.clone());
    let t = Ty::mk_arrow_single(t2.clone(), t1.clone());
    let p = Ty::poly(t);
    let p2 = p.optimize_replace_top();
    println!("before: {p}");
    println!("after: {p2}");
    let mut e = formula::Env::new();
    e.add(x, 1);
    assert!(p2.ty().rty_no_exists().eval(&e).unwrap());
}

/// Using equalities that appear in the argument position of the given type,
/// this function instantiates some types.
/// ex. ∀z. x: int -> (y: int -> *[z=x]) -> *[z >= x]
///   -> x:int -> (y: int -> *[T]) -> *[x >= x]
#[test]
fn test_generate_trivial_types_by_eq() {
    let z = Ident::fresh();
    let x = Ident::fresh();
    let y = Ident::fresh();

    let zgeqx = Constraint::mk_geq(Op::mk_var(z), Op::mk_var(x));
    let zeqx = Constraint::mk_eq(Op::mk_var(z), Op::mk_var(x));
    let t1 = Ty::mk_prop_ty(zgeqx);
    let t2 = Ty::mk_prop_ty(zeqx);
    let t3 = Ty::mk_iarrow(y, t2);
    let t4 = Ty::mk_arrow_single(t3, t1);
    let t5 = Ty::mk_iarrow(x, t4);
    let pty = Ty::poly(t5);
    println!("before: {pty}");
    let ptys = pty.generate_trivial_types_by_eq();
    assert_eq!(ptys.len(), 1);
    let pty = ptys[0].clone();
    println!("after: {pty}");
}

impl<C: Refinement> Tau<C> {
    pub fn instantiate(
        &self,
        ints: &HashSet<Ident>,
        coefficients: &mut Stack<Ident>,
        //all_coefficients: &mut HashSet<Ident>,
    ) -> Tau<C> {
        let (x, ty) = match self.kind() {
            TauKind::PTy(x, t) => (x, t),
            _ => return self.clone(),
        };
        crate::title!("instatiate_type");
        debug!("type={}", self);
        debug!("ints: {:?}", x);
        let ts = ty.alpha_renaming();
        let o = generate_arithmetic_template(ints, coefficients);
        debug!("template: {}", o);
        let ts = ts.subst(x, &o);
        debug!("instantiated: {}", ts);
        ts
    }
}

#[derive(Clone, Debug)]
pub struct TypeEnvironment<Type> {
    pub map: HashMap<Ident, Vec<Type>>,
}
pub type TyEnv = TypeEnvironment<Ty>;

impl<T: Pretty> Display for TypeEnvironment<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.pretty_display())
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

impl From<&TypeEnvironment<Tau<Constraint>>> for TypeEnvironment<Tau<fofml::Atom>> {
    fn from(env: &TypeEnvironment<Tau<Constraint>>) -> Self {
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

impl<T: PartialEq + Display> Default for TypeEnvironment<T> {
    fn default() -> Self {
        Self::new()
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
        self.map.remove(key);
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

impl<C: Refinement> TypeEnvironment<Tau<C>> {
    pub fn append(&mut self, x: &TypeEnvironment<Tau<C>>) {
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
                    self.map.insert(*k, v.to_vec());
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
            map.insert(*k, v.to_vec());
        }
        for (k, ts) in env2.map.iter() {
            match map.get_mut(k) {
                Some(vs) => {
                    for t in ts {
                        add_if_not_exist(vs, t.clone());
                    }
                }
                None => {
                    map.insert(*k, ts.to_vec());
                }
            }
        }
        TypeEnvironment { map }
    }
    pub fn add_top(&mut self, v: Ident, st: &SType) {
        self.add(v, Tau::mk_top(st));
    }

    pub fn add_bot(&mut self, v: Ident, st: &SType) {
        self.add(v, Tau::mk_bot(st));
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
                    if Ty::check_subtype_polymorphic(s, t) {
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
            let new_ts: Vec<_> = ts
                .iter()
                .flat_map(|t| {
                    let t = t.optimize();
                    let mut ts: Vec<_> = t
                        .generate_trivial_types_by_eq()
                        .into_iter()
                        // filter out non-polymophic type
                        .filter(|t| t.vars().is_empty())
                        .collect();
                    ts.push(t);
                    ts.into_iter()
                })
                .collect();

            new_map.insert(*k, new_ts);
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

    let t = Ty::mk_bot(&SType::mk_type_prop());
    let t2 = Ty::mk_top(&SType::mk_type_prop());
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
        TauKind::PTy(_x, _y) => {
            panic!("program error")
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
    to_fml(Goal::mk_true(), t)
}

// ψ↑τ
fn types<C: Refinement>(fml: Goal<C>, t: Tau<C>) -> Goal<C> {
    match t.kind() {
        TauKind::Proposition(c) => {
            let c = c.clone().negate().unwrap().into();
            Goal::mk_disj(c, fml)
        }
        TauKind::PTy(x, t) => {
            panic!("program error")
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
    ts.into_iter()
        .map(|t| {
            debug!("type_check: {} : {}", g, t);
            types(f.clone(), t).reduce()
        })
        .fold(C::mk_true(), |x, y| C::mk_conj(x, y))
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
