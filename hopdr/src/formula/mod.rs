pub mod chc;
pub mod fofml;
pub mod hes;
pub mod pcsp;
pub mod ty;

use std::collections::HashSet;
use std::fmt;

use rpds::Stack;

pub use crate::formula::ty::*;
use crate::parse::ExprKind;
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
pub enum OpExpr {
    Op(OpKind, Op, Op),
    Var(Ident),
    Const(i64),
    // for tracking substitution, we memorize the old ident and replaced op
    Ptr(Ident, Op),
}

pub type Op = P<OpExpr>;
impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use OpExpr::*;
        match self.kind() {
            Op(k, o1, o2) => {
                // handle (0 - x)
                match (*k, o1.kind()) {
                    (OpKind::Sub, OpExpr::Const(0)) => write!(f, "(-{})", o2),
                    _ => write!(f, "({} {} {})", o1, k, o2),
                }
            }
            Var(i) => write!(f, "{}", i),
            Const(c) => write!(f, "{}", c),
            Ptr(_, o) => write!(f, "{}", o),
        }
    }
}
impl PartialEq for Op {
    fn eq(&self, other: &Self) -> bool {
        match (self.kind(), other.kind()) {
            (OpExpr::Op(o1, x1, y1), OpExpr::Op(o2, x2, y2)) => o1 == o2 && x1 == x2 && y1 == y2,
            (OpExpr::Var(x), OpExpr::Var(y)) => x == y,
            (OpExpr::Const(c), OpExpr::Const(c2)) => c == c2,
            (OpExpr::Ptr(_, y1), OpExpr::Ptr(_, y2)) => y1 == y2,
            (_, _) => false,
        }
    }
}

impl Fv for Op {
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
            OpExpr::Ptr(_, o) => o.fv_with_vec(fvs),
        }
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
    fn mk_ptr(x: Ident, o: Op) -> Op {
        Op::new(OpExpr::Ptr(x, o))
    }
    /// flattens Op expression by removing `OpExpr::Ptr` entry
    pub fn flatten(&self) -> Self {
        match self.kind() {
            OpExpr::Op(o, x, y) => {
                let x = x.flatten();
                let y = y.flatten();
                Op::mk_bin_op(*o, x, y)
            }
            OpExpr::Ptr(_, o) => o.flatten(),
            OpExpr::Const(_) | OpExpr::Var(_) => self.clone(),
        }
    }
    pub fn to_hes_format(&self) -> String {
        match self.kind() {
            OpExpr::Op(o, x, y) => {
                let s1 = x.to_hes_format();
                let s2 = y.to_hes_format();
                format!("({} {} {})", s1, o, s2)
            }
            OpExpr::Var(x) => {
                format!("{}", x)
            }
            OpExpr::Const(c) => {
                format!("{}", c)
            }
            OpExpr::Ptr(_, x) => x.to_hes_format(),
        }
    }
}
impl DerefPtr for Op {
    fn deref_ptr(&self, id: &Ident) -> Op {
        match self.kind() {
            OpExpr::Op(o, x, y) => {
                let x = x.deref_ptr(id);
                let y = y.deref_ptr(id);
                Op::mk_bin_op(*o, x, y)
            }
            OpExpr::Var(_) | OpExpr::Const(_) => self.clone(),
            OpExpr::Ptr(id2, _o) if id == id2 => Op::mk_var(*id),
            OpExpr::Ptr(id2, o) => Op::mk_ptr(*id2, o.deref_ptr(id)),
        }
    }
}

#[test]
fn test_op_deref_ptr() {
    let x = Ident::fresh();
    let o = Op::mk_add(Op::mk_const(1), Op::mk_var(x));
    let o2 = Op::mk_const(4);
    let o3 = o.subst(&x, &o2);
    let o4 = o3.deref_ptr(&x);
    assert_eq!(o4, o);
}

impl Subst for Op {
    type Item = Op;
    type Id = Ident;
    fn subst(&self, id: &Ident, v: &Op) -> Op {
        match self.kind() {
            OpExpr::Op(k, x, y) => Op::mk_bin_op(*k, x.subst(id, v), y.subst(id, v)),

            OpExpr::Var(id2) if id == id2 => Op::mk_ptr(*id, v.clone()),
            OpExpr::Ptr(x, o) => Op::mk_ptr(*x, o.subst(id, v)),
            _ => self.clone(),
        }
    }
}

impl Rename for Op {
    fn rename(&self, id: &Ident, id2: &Ident) -> Op {
        match self.kind() {
            OpExpr::Op(k, x, y) => Op::mk_bin_op(*k, x.rename(id, id2), y.rename(id, id2)),

            OpExpr::Var(id3) if id == id3 => Op::mk_var(*id2),
            OpExpr::Ptr(x, o) => Op::mk_ptr(*x, o.rename(id, id2)),
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
    type Item;
    type Id;
    // impl IntoIterator is better, but rust-analyzer fails
    // issue: - https://github.com/rust-lang/rust-analyzer/issues/10932
    //        - https://github.com/rust-lang/rust-analyzer/issues/12484
    fn subst_multi(&self, substs: &[(Self::Id, Self::Item)]) -> Self {
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

pub trait DerefPtr {
    fn deref_ptr(&self, id: &Ident) -> Self;
}

#[derive(Debug)]
pub enum ConstraintExpr {
    True,
    False,
    Pred(PredKind, Vec<Op>),
    Conj(Constraint, Constraint),
    Disj(Constraint, Constraint),
    Quantifier(QuantifierKind, Variable, Constraint),
}

pub type Constraint = P<ConstraintExpr>;

impl fmt::Display for Constraint {
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
            Conj(c1, c2) => write!(f, "({}) ∧ ({})", c1, c2),
            Disj(c1, c2) => write!(f, "({}) ∨ ({})", c1, c2),
            Quantifier(q, x, c) => write!(f, "{}{}.{}", q, x, c),
        }
    }
}

impl PartialEq for Constraint {
    fn eq(&self, other: &Self) -> bool {
        let r = match (self.kind(), other.kind()) {
            (ConstraintExpr::True, ConstraintExpr::True) => true,
            (ConstraintExpr::False, ConstraintExpr::False) => true,
            (ConstraintExpr::Pred(PredKind::Eq, l1), ConstraintExpr::Pred(PredKind::Eq, l2))
                if l1.len() == 2 && l2.len() == 2 =>
            {
                // x == y vs x == y
                // or x == y vs y == x
                (l1[0] == l2[0] && l1[1] == l2[1]) || (l1[0] == l2[1] && l1[1] == l2[0])
            }
            (ConstraintExpr::Pred(p1, l1), ConstraintExpr::Pred(p2, l2)) => p1 == p2 && l1 == l2,
            (ConstraintExpr::Conj(x1, y1), ConstraintExpr::Conj(x2, y2)) => x1 == x2 && y1 == y2,
            (ConstraintExpr::Disj(x1, y1), ConstraintExpr::Disj(x2, y2)) => x1 == x2 && y1 == y2,
            (ConstraintExpr::Quantifier(q1, x1, y1), ConstraintExpr::Quantifier(q2, x2, y2)) => {
                q1 == q2 && x1 == x2 && y1 == y2
            }
            (_, _) => false,
        };
        r
    }
}

impl Top for Constraint {
    fn mk_true() -> Constraint {
        Constraint::new(ConstraintExpr::True)
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
impl Bot for Constraint {
    fn mk_false() -> Constraint {
        Constraint::new(ConstraintExpr::False)
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

impl Logic for Constraint {
    fn mk_conj(x: Constraint, y: Constraint) -> Constraint {
        if x.is_true() {
            y
        } else if y.is_true() {
            x
        } else {
            Constraint::new(ConstraintExpr::Conj(x, y))
        }
    }
    fn is_conj<'a>(&'a self) -> Option<(&'a Constraint, &'a Constraint)> {
        match self.kind() {
            ConstraintExpr::Conj(x, y) => Some((x, y)),
            _ => None,
        }
    }
    fn mk_disj(x: Constraint, y: Constraint) -> Constraint {
        if x.is_true() || y.is_true() {
            Constraint::mk_true()
        } else if x.is_false() {
            y
        } else if y.is_false() {
            x
        } else {
            Constraint::new(ConstraintExpr::Disj(x, y))
        }
    }
    fn is_disj<'a>(&'a self) -> Option<(&'a Constraint, &'a Constraint)> {
        match self.kind() {
            ConstraintExpr::Disj(x, y) => Some((x, y)),
            _ => None,
        }
    }
}
impl FirstOrderLogic for Constraint {
    fn mk_quantifier_int(q: QuantifierKind, v: Ident, c: Constraint) -> Constraint {
        Constraint::new(ConstraintExpr::Quantifier(
            q,
            Variable::mk(v, Type::mk_type_int()),
            c,
        ))
    }
}

impl Subst for Constraint {
    type Item = Op;
    type Id = Ident;
    // \theta[v/x]
    fn subst(&self, x: &Ident, v: &Op) -> Constraint {
        use ConstraintExpr::*;
        match self.kind() {
            True | False => self.clone(),
            Pred(k, ops) => {
                let mut new_ops = Vec::new();
                for op in ops.iter() {
                    new_ops.push(op.subst(x, v));
                }
                Constraint::mk_pred(*k, new_ops)
            }
            Conj(r, l) => Constraint::mk_conj(r.subst(x, v), l.subst(x, v)),
            Disj(r, l) => Constraint::mk_disj(r.subst(x, v), l.subst(x, v)),
            // assumption: vars are different each other ?
            Quantifier(q, var, cstr) => {
                Constraint::mk_quantifier(*q, var.clone(), cstr.subst(x, v))
            }
        }
    }
}

impl Rename for Constraint {
    // \theta[v/x]
    fn rename(&self, x: &Ident, y: &Ident) -> Constraint {
        use ConstraintExpr::*;
        match self.kind() {
            True | False => self.clone(),
            Pred(k, ops) => {
                let mut new_ops = Vec::new();
                for op in ops.iter() {
                    new_ops.push(op.rename(x, y));
                }
                Constraint::mk_pred(*k, new_ops)
            }
            Conj(r, l) => Constraint::mk_conj(r.rename(x, y), l.rename(x, y)),
            Disj(r, l) => Constraint::mk_disj(r.rename(x, y), l.rename(x, y)),
            // assumption: vars are different each other ?
            Quantifier(q, var, cstr) if &var.id != x && &var.id != y => {
                Constraint::mk_quantifier(*q, var.clone(), cstr.rename(x, y))
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
impl Negation for Constraint {
    // negation sometimes cannot be performed (e.g. \not x)
    fn negate(&self) -> Option<Constraint> {
        match self.kind() {
            ConstraintExpr::False => Some(Constraint::mk_true()),
            ConstraintExpr::True => Some(Constraint::mk_false()),
            ConstraintExpr::Pred(p, v) => Some(Constraint::mk_pred(p.negate(), v.clone())),
            ConstraintExpr::Conj(c1, c2) => match (c1.clone().negate(), c2.clone().negate()) {
                (Some(c1), Some(c2)) => Some(Constraint::mk_disj(c1, c2)),
                _ => None,
            },
            ConstraintExpr::Disj(c1, c2) => match (c1.clone().negate(), c2.clone().negate()) {
                (Some(c1), Some(c2)) => Some(Constraint::mk_conj(c1, c2)),
                _ => None,
            },
            ConstraintExpr::Quantifier(q, v, c) => {
                let q = q.negate();
                c.clone()
                    .negate()
                    .map(|c| Constraint::mk_quantifier(q, v.clone(), c))
            }
        }
    }
}

impl Constraint {
    pub fn mk_quantifier(q: QuantifierKind, v: Variable, c: Constraint) -> Constraint {
        Constraint::new(ConstraintExpr::Quantifier(q, v, c))
    }
    pub fn mk_implies(x: Self, y: Self) -> Self {
        x.negate().map(|x| Self::mk_disj(x, y)).unwrap()
    }

    pub fn mk_pred(k: PredKind, v: Vec<Op>) -> Constraint {
        Constraint::new(ConstraintExpr::Pred(k, v))
    }

    // these methods are useful for generating constraints to make tests
    pub fn mk_bin_pred(k: PredKind, left: Op, right: Op) -> Constraint {
        match k {
            PredKind::Eq | PredKind::Leq | PredKind::Geq if left == right => Constraint::mk_true(),
            PredKind::Neq | PredKind::Lt | PredKind::Gt if left == right => Constraint::mk_false(),
            _ => Constraint::mk_pred(k, vec![left, right]),
        }
    }
    pub fn mk_lt(left: Op, right: Op) -> Constraint {
        Self::mk_bin_pred(PredKind::Lt, left, right)
    }
    pub fn mk_geq(left: Op, right: Op) -> Constraint {
        Self::mk_bin_pred(PredKind::Geq, left, right)
    }
    pub fn mk_eq(left: Op, right: Op) -> Constraint {
        Self::mk_bin_pred(PredKind::Eq, left, right)
    }
    pub fn mk_neq(left: Op, right: Op) -> Constraint {
        Self::mk_bin_pred(PredKind::Neq, left, right)
    }

    pub fn variable_guard(v: Ident, op: Op) -> Constraint {
        let v = Op::mk_var(v);
        Constraint::mk_pred(PredKind::Eq, vec![v, op])
    }

    pub fn remove_quantifier(self) -> Constraint {
        match self.kind() {
            ConstraintExpr::True | ConstraintExpr::False | ConstraintExpr::Pred(_, _) => {
                self.clone()
            }
            ConstraintExpr::Conj(c1, c2) => Constraint::mk_conj(
                c1.clone().remove_quantifier(),
                c2.clone().remove_quantifier(),
            ),
            ConstraintExpr::Disj(c1, c2) => Constraint::mk_disj(
                c1.clone().remove_quantifier(),
                c2.clone().remove_quantifier(),
            ),
            ConstraintExpr::Quantifier(_, _, c) => c.clone().remove_quantifier(),
        }
    }
    fn prenex_normal_form_raw(
        &self,
        env: &mut HashSet<Ident>,
    ) -> (Vec<(QuantifierKind, Variable)>, Constraint) {
        match self.kind() {
            ConstraintExpr::True | ConstraintExpr::False | ConstraintExpr::Pred(_, _) => {
                (Vec::new(), self.clone())
            }
            ConstraintExpr::Conj(c1, c2) => {
                let (mut v1, c1) = c1.prenex_normal_form_raw(env);
                let (mut v2, c2) = c2.prenex_normal_form_raw(env);
                v1.append(&mut v2);
                (v1, Constraint::mk_conj(c1, c2))
            }
            ConstraintExpr::Disj(c1, c2) => {
                let (mut v1, c1) = c1.prenex_normal_form_raw(env);
                let (mut v2, c2) = c2.prenex_normal_form_raw(env);
                v1.append(&mut v2);
                (v1, Constraint::mk_disj(c1, c2))
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
    pub fn to_pnf(&self) -> Constraint {
        let (_, c) = self.prenex_normal_form_raw(&mut HashSet::new());
        c
    }
    pub fn to_hes_format(&self) -> String {
        match self.kind() {
            ConstraintExpr::True => "true".to_string(),
            ConstraintExpr::False => "false".to_string(),
            ConstraintExpr::Pred(p, l) if l.len() == 2 => {
                let mut s = l[0].to_hes_format();
                s += match p {
                    PredKind::Eq => "=",
                    PredKind::Neq => "!=",
                    PredKind::Lt => "<",
                    PredKind::Leq => "<=",
                    PredKind::Gt => ">",
                    PredKind::Geq => ">=",
                };
                s += &l[1].to_hes_format();
                s
            }
            ConstraintExpr::Pred(_p, _l) => panic!("fatal"),
            ConstraintExpr::Disj(x, y) => {
                format!("( {} \\/ {} )", x.to_hes_format(), y.to_hes_format())
            }
            ConstraintExpr::Conj(x, y) => {
                format!("( {} /\\ {} )", x.to_hes_format(), y.to_hes_format())
            }
            ConstraintExpr::Quantifier(_, _, _) => unimplemented!(),
        }
    }
}
impl DerefPtr for Constraint {
    fn deref_ptr(&self, id: &Ident) -> Constraint {
        match self.kind() {
            ConstraintExpr::True | ConstraintExpr::False => self.clone(),
            ConstraintExpr::Pred(p, l) => {
                let l = l.iter().map(|o| o.deref_ptr(id)).collect();
                Constraint::mk_pred(*p, l)
            }
            ConstraintExpr::Conj(x, y) => {
                let x = x.deref_ptr(id);
                let y = y.deref_ptr(id);
                Constraint::mk_conj(x, y)
            }
            ConstraintExpr::Disj(x, y) => {
                let x = x.deref_ptr(id);
                let y = y.deref_ptr(id);
                Constraint::mk_disj(x, y)
            }
            ConstraintExpr::Quantifier(q, v, x) => {
                let x = x.deref_ptr(id);
                Constraint::mk_quantifier(*q, v.clone(), x)
            }
        }
    }
}
#[test]
fn test_constraint_deref_ptr() {
    let x = Ident::fresh();
    let o = Op::mk_add(Op::mk_const(1), Op::mk_var(x));
    let o2 = Op::mk_const(4);
    let c = Constraint::mk_lt(o, o2.clone());
    let c2 = c.subst(&x, &o2);
    let c3 = c2.deref_ptr(&x);
    assert_eq!(c, c3);
}
impl Fv for Constraint {
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

// // Generate Template with the configuration
// pub trait GreedyInstantiation<T> {
//     type SeedType: Subst<Id=Ident, Item=Op> + Clone;
//     fn subst_greedy(seed: SeedType, candidates: Vec<SeedType>) -> Self;
//     fn scope_variable(seed: &SeedType) -> HashSet<Ident>;
//     fn greedy_instantiate(seed: SeedType, scope_ints: &HashSet<Ident>) -> Self {
//         let mut fvs = Self::scope_variable(&seed);
//
//         debug!("fvs: {:?}", fvs);
//         debug!("ints: {:?}", scope_ints);
//
//         let mut patterns: Vec<Op> = Vec::new();
//         for int in scope_ints.iter() {
//             let o = Op::mk_var(*int);
//             if scope_ints.len() < 4 {
//                 for i in 0..patterns.len() {
//                     patterns.push(Op::mk_add(patterns[i].clone(), o.clone()));
//                 }
//             }
//             patterns.push(o);
//         }
//         patterns.push(Op::mk_const(0));
//
//         // instantiate fvs by ints
//         let mut gs = vec![seed.clone()];
//         for fv in fvs
//             .into_iter()
//             .map(|fv| )
//         {
//             let mut new_gs = Vec::new();
//             for op in patterns.iter() {
//                 for g in gs.iter() {
//                     if new_gs.len() > 100000 {
//                         panic!("explosion")
//                     }
//                     new_gs.push(g.subst(&fv, op));
//                 }
//             }
//             gs = new_gs;
//         }
//         assert!(gs.len() > 0);
//         Self::subst_greedy(seed, gs)
//         unimplemented!()
//     }
// }

impl From<crate::parse::Expr> for Constraint {
    fn from<'a>(e: crate::parse::Expr) -> Self {
        fn op<'a>(
            e: &'a crate::parse::Expr,
            env: &mut std::collections::HashMap<&'a String, Ident>,
        ) -> Op {
            match e.kind() {
                ExprKind::Var(v) => Op::mk_var(*env.get(v).unwrap()),
                ExprKind::Num(n) => Op::mk_const(*n),
                ExprKind::Op(o, x, y) => Op::mk_bin_op(*o, op(x, env), op(y, env)),
                _ => panic!("fatal"),
            }
        }
        fn go<'a>(
            e: &'a crate::parse::Expr,
            env: &mut std::collections::HashMap<&'a String, Ident>,
        ) -> Constraint {
            match e.kind() {
                ExprKind::True => Constraint::mk_true(),
                ExprKind::False => Constraint::mk_false(),
                ExprKind::Pred(p, x, y) => Constraint::mk_pred(*p, vec![op(x, env), op(y, env)]),
                ExprKind::And(x, y) => Constraint::mk_conj(go(x, env), go(y, env)),
                ExprKind::Or(x, y) => Constraint::mk_disj(go(x, env), go(y, env)),
                ExprKind::Univ(x, e) => {
                    let id = Ident::fresh();
                    let old = env.insert(x, id);
                    let c = Constraint::mk_univ_int(id, go(e, env));
                    match old {
                        Some(old) => assert!(env.insert(x, old).is_some()),
                        None => (),
                    }
                    c
                }
                ExprKind::Exist(_, _) => unimplemented!(),
                _ => panic!("fatal"),
            }
        }
        let fvs = e.fv();
        let mut env = std::collections::HashMap::new();
        for fv in fvs.iter() {
            let id = Ident::fresh();
            env.insert(fv, id);
        }
        go(&e, &mut env)
    }
}
