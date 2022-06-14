pub mod chc;
pub mod fofml;
pub mod hes;
pub mod pcsp;
pub mod ty;

use std::collections::HashSet;
use std::fmt;

use rpds::Stack;

pub use crate::formula::ty::*;
use crate::util::global_counter;
pub use crate::util::P;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum PredKind {
    Eq,
    Neq,
    Lt,
    Leq,
    Gt,
    Geq,
}

impl fmt::Display for PredKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                PredKind::Eq => "=",
                PredKind::Neq => "!=",
                PredKind::Lt => "<",
                PredKind::Leq => "<=",
                PredKind::Gt => ">",
                PredKind::Geq => ">=",
            }
        )
    }
}

impl PredKind {
    pub fn negate(&self) -> PredKind {
        match self {
            PredKind::Eq => PredKind::Neq,
            PredKind::Neq => PredKind::Eq,
            PredKind::Lt => PredKind::Geq,
            PredKind::Leq => PredKind::Gt,
            PredKind::Gt => PredKind::Leq,
            PredKind::Geq => PredKind::Lt,
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum OpKind {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}
pub trait Arithmetic:
    Clone + PartialEq + Rename + Fv<Id = Ident> + Subst<Id = Ident, Item = Self> + fmt::Display
{
}

impl<T> Arithmetic for T where
    T: Clone + PartialEq + Rename + Fv<Id = Ident> + Subst<Id = Ident, Item = Self> + fmt::Display
{
}

impl fmt::Display for OpKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                OpKind::Add => "+",
                OpKind::Sub => "-",
                OpKind::Mul => "*",
                OpKind::Div => "/",
                OpKind::Mod => "%",
            }
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QuantifierKind {
    Universal,
    Existential,
}

impl fmt::Display for QuantifierKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                QuantifierKind::Universal => "∀",
                QuantifierKind::Existential => "∃",
            }
        )
    }
}

impl QuantifierKind {
    fn negate(&self) -> QuantifierKind {
        match self {
            QuantifierKind::Existential => QuantifierKind::Universal,
            QuantifierKind::Universal => QuantifierKind::Existential,
        }
    }
}

#[derive(Debug)]
pub enum OpExpr<T> {
    Op(OpKind, OpBase<T>, OpBase<T>),
    Var(Ident),
    Const(i64),
}

impl<T> OpBase<T> {
    pub fn kind<'a>(&'a self) -> &'a OpExpr<T> {
        &*self.ptr
    }
}

#[derive(Debug)]
pub struct OpBase<T> {
    ptr: P<OpExpr<T>>,
    pub aux: T,
}

pub type Op = OpBase<()>;

impl<T> fmt::Display for OpBase<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use OpExpr::*;
        match self.kind() {
            Op(k, o1, o2) => write!(f, "{} {} {}", o1, k, o2),
            Var(i) => write!(f, "{}", i),
            Const(c) => write!(f, "{}", c),
        }
    }
}

impl<T: Clone> Clone for OpBase<T> {
    fn clone(&self) -> OpBase<T> {
        OpBase {
            ptr: self.ptr.clone(),
            aux: self.aux.clone(),
        }
    }
}

impl<T> Fv for OpBase<T> {
    type Id = Ident;
    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>) {
        match self.kind() {
            OpExpr::Op(_, x, y) => {
                x.fv_with_vec(fvs);
                y.fv_with_vec(fvs);
            }
            OpExpr::Var(x) => {
                fvs.insert(*x);
            }
            OpExpr::Const(_) => {}
        }
    }
}

impl<T> PartialEq for OpExpr<T> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (OpExpr::Op(op1, x1, y1), OpExpr::Op(op2, x2, y2)) => {
                op1 == op2 && x1 == x2 && y1 == y2
            }
            (OpExpr::Var(x), OpExpr::Var(y)) => x == y,
            (OpExpr::Const(x), OpExpr::Const(y)) => x == y,
            (_, _) => false,
        }
    }
}

impl<T> PartialEq for OpBase<T> {
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr
    }
}

impl From<Ident> for Op {
    fn from(x: Ident) -> Self {
        Op::mk_var(x)
    }
}

#[derive(Clone)]
pub struct IntegerEnvironment {
    imap: Stack<Ident>,
}

impl IntegerEnvironment {
    pub fn new() -> IntegerEnvironment {
        IntegerEnvironment { imap: Stack::new() }
    }
    pub fn exists(&self, id: &Ident) -> bool {
        for i in self.imap.iter() {
            if i == id {
                return true;
            }
        }
        false
    }
    pub fn variables(&self) -> Vec<Ident> {
        // assumes alpha-renamed
        self.imap.iter().copied().collect()
    }
    pub fn add(mut self, v: Ident) -> IntegerEnvironment {
        self.imap.push_mut(v);
        self
    }

    pub fn iter(&self) -> impl Iterator<Item = Ident> + '_ {
        self.imap.iter().copied()
    }
}

impl Op {
    pub fn new(expr: OpExpr<()>) -> Op {
        OpBase {
            ptr: P::new(expr),
            aux: (),
        }
    }
    pub fn mk_bin_op(op: OpKind, x: Op, y: Op) -> Op {
        Op::new(OpExpr::Op(op, x, y))
    }

    pub fn mk_add(x: Op, y: Op) -> Op {
        Op::new(OpExpr::Op(OpKind::Add, x, y))
    }

    pub fn mk_const(x: i64) -> Op {
        Op::new(OpExpr::Const(x))
    }

    pub fn mk_var(x: Ident) -> Op {
        Op::new(OpExpr::Var(x))
    }
}

impl<T> OpBase<T> {
    pub fn new_t(op: OpExpr<T>, aux: T) -> OpBase<T> {
        OpBase {
            ptr: P::new(op),
            aux,
        }
    }
    pub fn mk_bin_op_t(op: OpKind, x: OpBase<T>, y: OpBase<T>, aux: T) -> OpBase<T> {
        OpBase::new_t(OpExpr::Op(op, x, y), aux)
    }

    pub fn mk_add_t(x: OpBase<T>, y: OpBase<T>, aux: T) -> OpBase<T> {
        OpBase::new_t(OpExpr::Op(OpKind::Add, x, y), aux)
    }

    pub fn mk_const_t(x: i64, aux: T) -> OpBase<T> {
        OpBase::new_t(OpExpr::Const(x), aux)
    }

    pub fn mk_var_t(x: Ident, aux: T) -> OpBase<T> {
        OpBase::new_t(OpExpr::Var(x), aux)
    }
}

impl<T: Clone> Subst for OpBase<T> {
    type Item = OpBase<T>;
    type Id = Ident;
    fn subst(&self, id: &Ident, v: &Self) -> Self {
        match self.kind() {
            OpExpr::Op(k, x, y) => {
                Self::mk_bin_op_t(*k, x.subst(id, v), y.subst(id, v), self.aux.clone())
            }

            OpExpr::Var(id2) if id == id2 => v.clone(),
            _ => self.clone(),
        }
    }
}

impl<T: Clone> Rename for OpBase<T> {
    fn rename(&self, id: &Ident, id2: &Ident) -> Self {
        match self.kind() {
            OpExpr::Op(k, x, y) => {
                Self::mk_bin_op_t(*k, x.rename(id, id2), y.rename(id, id2), self.aux.clone())
            }

            OpExpr::Var(id3) if id == id3 => Self::mk_var_t(*id2, self.aux.clone()),
            _ => self.clone(),
        }
    }
}

pub trait Top {
    fn mk_true() -> Self;
    fn is_true(&self) -> bool;
}

pub trait Bot {
    fn mk_false() -> Self;
    fn is_false(&self) -> bool;
}

pub trait Logic: Top + Bot + Clone {
    fn mk_conj(x: Self, y: Self) -> Self;
    fn is_conj<'a>(&'a self) -> Option<(&'a Self, &'a Self)>;
    fn mk_disj(x: Self, y: Self) -> Self;
    fn is_disj<'a>(&'a self) -> Option<(&'a Self, &'a Self)>;

    fn to_cnf(&self) -> Vec<Self> {
        fn cross_or<C: Clone + Logic>(v1: &[C], v2: &[C]) -> Vec<C> {
            let mut v = Vec::new();
            for x in v1 {
                for y in v2 {
                    v.push(C::mk_disj(x.clone(), y.clone()));
                }
            }
            v
        }
        match self.is_conj() {
            Some((x, y)) => {
                let mut v1 = x.to_cnf();
                let mut v2 = y.to_cnf();
                v1.append(&mut v2);
                return v1;
            }
            None => (),
        }
        match self.is_disj() {
            Some((x, y)) => {
                let v1 = x.to_cnf();
                let v2 = y.to_cnf();
                return cross_or(&v1, &v2);
            }
            None => vec![self.clone()],
        }
    }
    fn to_dnf(&self) -> Vec<Self> {
        fn cross_and<C: Clone + Logic>(v1: &[C], v2: &[C]) -> Vec<C> {
            let mut v = Vec::new();
            for x in v1 {
                for y in v2 {
                    v.push(C::mk_conj(x.clone(), y.clone()));
                }
            }
            v
        }
        match self.is_disj() {
            Some((x, y)) => {
                let mut v1 = x.to_dnf();
                let mut v2 = y.to_dnf();
                v1.append(&mut v2);
                return v1;
            }
            None => (),
        }
        match self.is_conj() {
            Some((x, y)) => {
                let v1 = x.to_dnf();
                let v2 = y.to_dnf();
                return cross_and(&v1, &v2);
            }
            None => vec![self.clone()],
        }
    }
}

pub trait FirstOrderLogic: Logic {
    fn mk_quantifier_int(q: QuantifierKind, v: Ident, c: Self) -> Self;
    fn mk_exists_int(v: Ident, c: Self) -> Self {
        Self::mk_quantifier_int(QuantifierKind::Existential, v, c)
    }
    fn mk_univ_int(v: Ident, c: Self) -> Self {
        Self::mk_quantifier_int(QuantifierKind::Universal, v, c)
    }
}

pub trait Subst: Sized + Clone {
    type Item: Clone + fmt::Display;
    type Id;
    fn subst_multi(&self, substs: impl IntoIterator<Item = (Self::Id, Self::Item)>) -> Self {
        let mut itr = substs.into_iter();
        let (id, item) = match itr.next() {
            Some((id, item)) => (id, item),
            None => return self.clone(),
        };
        let mut ret = self.subst(&id, &item);
        for (ident, val) in itr {
            ret = ret.subst(&ident, &val);
        }
        ret
    }
    fn subst(&self, x: &Self::Id, v: &Self::Item) -> Self;
}

pub trait Rename: Sized {
    fn rename(&self, x: &Ident, y: &Ident) -> Self;
    // TODO: fix type xs
    fn rename_idents(&self, xs: &[(Ident, Ident)]) -> Self {
        assert!(!xs.is_empty());
        let mut c = self.rename(&xs[0].0, &xs[0].1);
        for (x, y) in &xs[1..] {
            c = c.rename(x, y);
        }
        c
    }
    fn rename_idents_with_slices(&self, xs: &[Ident], ys: &[Ident]) -> Self {
        assert!(xs.len() == ys.len());
        // TODO: Fix this bad impl
        let mut v = Vec::new();
        for (x, y) in xs.iter().zip(ys.iter()) {
            v.push((*x, *y))
        }
        self.rename_idents(&v)
    }
}

pub trait Fv {
    type Id;

    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>);

    fn fv(&self) -> HashSet<Self::Id> {
        let mut fvs = HashSet::new();
        self.fv_with_vec(&mut fvs);
        fvs
    }
}

#[derive(Debug, PartialEq)]
pub enum ConstraintExpr<Op> {
    True,
    False,
    Pred(PredKind, Vec<Op>),
    Conj(ConstraintBase<Op>, ConstraintBase<Op>),
    Disj(ConstraintBase<Op>, ConstraintBase<Op>),
    Quantifier(QuantifierKind, Variable, ConstraintBase<Op>),
}

pub type ConstraintBase<Op> = P<ConstraintExpr<Op>>;

pub type Constraint = ConstraintBase<Op>;

impl<O: fmt::Display> fmt::Display for ConstraintBase<O> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ConstraintExpr::*;
        match self.kind() {
            True => write!(f, "true"),
            False => write!(f, "false"),
            Pred(p, ops) => {
                if ops.len() == 2 {
                    return write!(f, "{} {} {}", ops[0], p, ops[1]);
                }
                write!(f, "{}(", p)?;
                if !ops.is_empty() {
                    write!(f, "{}", ops[0])?;
                    for op in &ops[1..] {
                        write!(f, ", {}", op)?;
                    }
                }
                write!(f, ")")
            }
            Conj(c1, c2) => write!(f, "({}) & ({})", c1, c2),
            Disj(c1, c2) => write!(f, "({}) | ({})", c1, c2),
            Quantifier(q, x, c) => write!(f, "{}{}.{}", q, x, c),
        }
    }
}

impl<O> Top for ConstraintBase<O> {
    fn mk_true() -> Self {
        Self::new(ConstraintExpr::True)
    }
    fn is_true(&self) -> bool {
        match self.kind() {
            ConstraintExpr::True => true,
            ConstraintExpr::Quantifier(QuantifierKind::Universal, _, c) => c.is_true(),
            ConstraintExpr::Conj(c1, c2) => c1.is_true() && c2.is_true(),
            ConstraintExpr::Disj(c1, c2) => c1.is_true() || c2.is_true(),
            _ => false,
        }
    }
}
impl<O> Bot for ConstraintBase<O> {
    fn mk_false() -> Self {
        Self::new(ConstraintExpr::False)
    }
    fn is_false(&self) -> bool {
        match self.kind() {
            ConstraintExpr::False => true,
            ConstraintExpr::Quantifier(QuantifierKind::Universal, _, c) => c.is_false(),
            ConstraintExpr::Conj(c1, c2) => c1.is_false() || c2.is_false(),
            ConstraintExpr::Disj(c1, c2) => c1.is_false() && c2.is_false(),
            _ => false,
        }
    }
}

impl<O> Logic for ConstraintBase<O> {
    fn mk_conj(x: Self, y: Self) -> Self {
        if x.is_true() {
            y
        } else if y.is_true() {
            x
        } else {
            Self::new(ConstraintExpr::Conj(x, y))
        }
    }
    fn is_conj<'a>(&'a self) -> Option<(&'a Self, &'a Self)> {
        match self.kind() {
            ConstraintExpr::Conj(x, y) => Some((x, y)),
            _ => None,
        }
    }
    fn mk_disj(x: Self, y: Self) -> Self {
        if x.is_true() || y.is_true() {
            Self::mk_true()
        } else if x.is_false() {
            y
        } else if y.is_false() {
            x
        } else {
            Self::new(ConstraintExpr::Disj(x, y))
        }
    }
    fn is_disj<'a>(&'a self) -> Option<(&'a Self, &'a Self)> {
        match self.kind() {
            ConstraintExpr::Disj(x, y) => Some((x, y)),
            _ => None,
        }
    }
}
impl<O> FirstOrderLogic for ConstraintBase<O> {
    fn mk_quantifier_int(q: QuantifierKind, v: Ident, c: Self) -> Self {
        Self::new(ConstraintExpr::Quantifier(
            q,
            Variable::mk(v, Type::mk_type_int()),
            c,
        ))
    }
}

impl<Op: Arithmetic> Subst for ConstraintBase<Op> {
    type Item = Op;
    type Id = Ident;
    // \theta[v/x]
    fn subst(&self, x: &Ident, v: &Op) -> Self {
        use ConstraintExpr::*;
        match self.kind() {
            True | False => self.clone(),
            Pred(k, ops) => {
                let mut new_ops = Vec::new();
                for op in ops.iter() {
                    new_ops.push(op.subst(x, v));
                }
                Self::mk_pred(*k, new_ops)
            }
            Conj(r, l) => Self::mk_conj(r.subst(x, v), l.subst(x, v)),
            Disj(r, l) => Self::mk_disj(r.subst(x, v), l.subst(x, v)),
            // assumption: vars are different each other ?
            Quantifier(q, var, cstr) => Self::mk_quantifier(*q, var.clone(), cstr.subst(x, v)),
        }
    }
}

impl<Op: PartialEq + Clone + Rename> Rename for ConstraintBase<Op> {
    // \theta[v/x]
    fn rename(&self, x: &Ident, y: &Ident) -> Self {
        use ConstraintExpr::*;
        match self.kind() {
            True | False => self.clone(),
            Pred(k, ops) => {
                let mut new_ops = Vec::new();
                for op in ops.iter() {
                    new_ops.push(op.rename(x, y));
                }
                Self::mk_pred(*k, new_ops)
            }
            Conj(r, l) => Self::mk_conj(r.rename(x, y), l.rename(x, y)),
            Disj(r, l) => Self::mk_disj(r.rename(x, y), l.rename(x, y)),
            // assumption: vars are different each other ?
            Quantifier(q, var, cstr) if &var.id != x && &var.id != y => {
                Self::mk_quantifier(*q, var.clone(), cstr.rename(x, y))
            }
            Quantifier(_, _, _) => panic!("assumption broken"),
        }
    }
}

pub trait Negation {
    fn negate(&self) -> Option<Self>
    where
        Self: Sized;
}
impl<Op: PartialEq + Clone> Negation for ConstraintBase<Op> {
    // negation sometimes cannot be performed (e.g. \not x)
    fn negate(&self) -> Option<Self> {
        match self.kind() {
            ConstraintExpr::False => Some(Self::mk_true()),
            ConstraintExpr::True => Some(Self::mk_false()),
            ConstraintExpr::Pred(p, v) => Some(Self::mk_pred(p.negate(), v.clone())),
            ConstraintExpr::Conj(c1, c2) => match (c1.clone().negate(), c2.clone().negate()) {
                (Some(c1), Some(c2)) => Some(Self::mk_disj(c1, c2)),
                _ => None,
            },
            ConstraintExpr::Disj(c1, c2) => match (c1.clone().negate(), c2.clone().negate()) {
                (Some(c1), Some(c2)) => Some(Self::mk_conj(c1, c2)),
                _ => None,
            },
            ConstraintExpr::Quantifier(q, v, c) => {
                let q = q.negate();
                c.clone()
                    .negate()
                    .map(|c| Self::mk_quantifier(q, v.clone(), c))
            }
        }
    }
}

impl<Op: Clone> ConstraintBase<Op> {
    pub fn mk_quantifier(q: QuantifierKind, v: Variable, c: Self) -> Self {
        Self::new(ConstraintExpr::Quantifier(q, v, c))
    }

    pub fn mk_pred(k: PredKind, v: Vec<Op>) -> Self {
        Self::new(ConstraintExpr::Pred(k, v))
    }
}
impl<Op: Clone + PartialEq> ConstraintBase<Op> {
    pub fn mk_implies(x: Self, y: Self) -> Self {
        x.negate().map(|x| Self::mk_disj(x, y)).unwrap()
    }
    // these methods are useful for generating constraints to make tests
    pub fn mk_bin_pred(k: PredKind, left: Op, right: Op) -> Self {
        match k {
            PredKind::Eq | PredKind::Leq | PredKind::Geq if left == right => Self::mk_true(),
            PredKind::Neq | PredKind::Lt | PredKind::Gt if left == right => Self::mk_false(),
            _ => Self::mk_pred(k, vec![left, right]),
        }
    }
    pub fn mk_lt(left: Op, right: Op) -> Self {
        Self::mk_bin_pred(PredKind::Lt, left, right)
    }
    pub fn mk_geq(left: Op, right: Op) -> Self {
        Self::mk_bin_pred(PredKind::Geq, left, right)
    }
    pub fn mk_eq(left: Op, right: Op) -> Self {
        Self::mk_bin_pred(PredKind::Eq, left, right)
    }
    pub fn mk_neq(left: Op, right: Op) -> Self {
        Self::mk_bin_pred(PredKind::Neq, left, right)
    }

    pub fn remove_quantifier(self) -> Self {
        match self.kind() {
            ConstraintExpr::True | ConstraintExpr::False | ConstraintExpr::Pred(_, _) => {
                self.clone()
            }
            ConstraintExpr::Conj(c1, c2) => Self::mk_conj(
                c1.clone().remove_quantifier(),
                c2.clone().remove_quantifier(),
            ),
            ConstraintExpr::Disj(c1, c2) => Self::mk_disj(
                c1.clone().remove_quantifier(),
                c2.clone().remove_quantifier(),
            ),
            ConstraintExpr::Quantifier(_, _, c) => c.clone().remove_quantifier(),
        }
    }
}
impl<Op: Clone + PartialEq + Rename> ConstraintBase<Op> {
    fn prenex_normal_form_raw(
        &self,
        env: &mut HashSet<Ident>,
    ) -> (Vec<(QuantifierKind, Variable)>, Self) {
        match self.kind() {
            ConstraintExpr::True | ConstraintExpr::False | ConstraintExpr::Pred(_, _) => {
                (Vec::new(), self.clone())
            }
            ConstraintExpr::Conj(c1, c2) => {
                let (mut v1, c1) = c1.prenex_normal_form_raw(env);
                let (mut v2, c2) = c2.prenex_normal_form_raw(env);
                v1.append(&mut v2);
                (v1, Self::mk_conj(c1, c2))
            }
            ConstraintExpr::Disj(c1, c2) => {
                let (mut v1, c1) = c1.prenex_normal_form_raw(env);
                let (mut v2, c2) = c2.prenex_normal_form_raw(env);
                v1.append(&mut v2);
                (v1, Self::mk_disj(c1, c2))
            }
            ConstraintExpr::Quantifier(q, x, c) => {
                let (x, c) = if env.contains(&x.id) {
                    // if env already contains the ident to be bound,
                    // we rename it to a fresh one.
                    let x2_ident = Ident::fresh();
                    let x2 = Variable::mk(x2_ident, x.ty.clone());
                    let c = c.rename(&x.id, &x2_ident);
                    (x2, c)
                } else {
                    (x.clone(), c.clone())
                };
                env.insert(x.id);
                let (mut v, c) = c.prenex_normal_form_raw(env);
                debug_assert!(v.iter().find(|(_, y)| { x.id == y.id }).is_none());
                v.push((*q, x.clone()));
                env.remove(&x.id);
                (v, c)
            }
        }
    }
    pub fn to_pnf(&self) -> Self {
        let (_, c) = self.prenex_normal_form_raw(&mut HashSet::new());
        c
    }
}
impl Constraint {
    pub fn variable_guard(v: Ident, op: Op) -> Self {
        let v = Op::mk_var(v);
        Self::mk_pred(PredKind::Eq, vec![v, op])
    }
}
impl<Op: PartialEq + Fv<Id = Ident>> Fv for ConstraintBase<Op> {
    type Id = Ident;

    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>) {
        match self.kind() {
            ConstraintExpr::True | ConstraintExpr::False => {}
            ConstraintExpr::Pred(_, ops) => {
                for op in ops.iter() {
                    op.fv_with_vec(fvs);
                }
            }
            ConstraintExpr::Conj(x, y) | ConstraintExpr::Disj(x, y) => {
                x.fv_with_vec(fvs);
                y.fv_with_vec(fvs);
            }
            ConstraintExpr::Quantifier(_, v, x) => {
                let already_contained = fvs.contains(&v.id);
                x.fv_with_vec(fvs);
                if !already_contained {
                    fvs.remove(&v.id);
                }
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Ident {
    id: u64,
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x_{}", self.id)
    }
}

impl Ident {
    pub fn fresh() -> Ident {
        let id = global_counter();
        Ident { id }
    }
    pub fn rename_idents(args: &Vec<Ident>, x: &Ident, y: &Ident) -> Vec<Ident> {
        args.iter()
            .map(|arg| if arg == x { *y } else { *arg })
            .collect()
    }
    /// assumption: string expression is x_\d+
    pub fn from_str(s: &str) -> Option<Ident> {
        debug!("Ident::from_str: {}", s);
        match (&s[2..]).parse() {
            Ok(id) => Some(Ident { id }),
            Err(_) => None,
        }
    }
}

impl From<u64> for Ident {
    fn from(id: u64) -> Self {
        Ident { id }
    }
}

#[derive(Debug, PartialEq)]
pub struct VariableS {
    pub id: Ident,
    pub ty: Type,
}
pub type Variable = P<VariableS>;

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.id, self.ty)
    }
}

impl Variable {
    pub fn mk(id: Ident, ty: Type) -> Variable {
        Variable::new(VariableS { id, ty })
    }
    pub fn id(&self) -> Ident {
        self.id
    }
    pub fn ty(&self) -> &Type {
        &self.ty
    }
    pub fn fresh(ty: Type) -> Variable {
        let id = Ident::fresh();
        Variable::new(VariableS { id, ty })
    }
    // methods for testing
    pub fn fresh_prop() -> Variable {
        Variable::fresh(Type::mk_type_prop())
    }
    pub fn fresh_int() -> Variable {
        Variable::fresh(Type::mk_type_int())
    }
    pub fn order(&self) -> usize {
        self.ty.order()
    }
}

#[derive(Clone, Debug)]
pub enum Fixpoint {
    Greatest,
    Least,
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Polarity {
    Positive,
    Negative,
}
impl Polarity {
    pub fn rev(self) -> Polarity {
        if self == Polarity::Positive {
            Polarity::Negative
        } else {
            Polarity::Positive
        }
    }
}
