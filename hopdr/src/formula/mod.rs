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

#[derive(Debug, PartialEq)]
pub enum OpExpr {
    Op(OpKind, Op, Op),
    Var(Ident),
    Const(i64),
}

pub type Op = P<OpExpr>;
impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use OpExpr::*;
        match self.kind() {
            Op(k, o1, o2) => write!(f, "{} {} {}", o1, k, o2),
            Var(i) => write!(f, "{}", i),
            Const(c) => write!(f, "{}", c),
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
        }
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

    pub fn mk_const(x: i64) -> Op {
        Op::new(OpExpr::Const(x))
    }

    pub fn mk_var(x: Ident) -> Op {
        Op::new(OpExpr::Var(x))
    }
}
//impl PartialEq for Op {
//    fn eq(&self, other: &Self) -> bool {
//        match (self.kind(), other.kind()) {
//            (OpExpr::Op(o1, x1, y1), OpExpr::Op(o2, x2, y2)) => o1 == o2 && x1 == x2 && y1 == y2,
//            (OpExpr::Var(x1), OpExpr::Var(x2)) => x1 == x2,
//            (OpExpr::Const(c1), OpExpr::Const(c2)) => c1 == c2,
//            (_, _) => false,
//        }
//    }
//}

impl Subst for Op {
    type Item = Op;
    type Id = Ident;
    fn subst(&self, id: &Ident, v: &Op) -> Op {
        match self.kind() {
            OpExpr::Op(k, x, y) => Op::mk_bin_op(*k, x.subst(id, v), y.subst(id, v)),

            OpExpr::Var(id2) if id == id2 => v.clone(),
            _ => self.clone(),
        }
    }
}

impl Rename for Op {
    fn rename(&self, id: &Ident, id2: &Ident) -> Op {
        match self.kind() {
            OpExpr::Op(k, x, y) => Op::mk_bin_op(*k, x.rename(id, id2), y.rename(id, id2)),

            OpExpr::Var(id3) if id == id3 => Op::mk_var(*id2),
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

pub trait Logic {
    fn mk_conj(x: Self, y: Self) -> Self;
    fn mk_disj(x: Self, y: Self) -> Self;
}

pub trait Subst: Sized {
    type Item;
    type Id;
    fn subst_multi(&self, substs: &[(Self::Id, Self::Item)]) -> Self {
        assert!(!substs.is_empty());
        let mut ret = self.subst(&substs[0].0, &substs[0].1);
        for (ident, val) in &substs[1..] {
            ret = ret.subst(ident, val);
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
            Conj(c1, c2) => write!(f, "({}) & ({})", c1, c2),
            Disj(c1, c2) => write!(f, "({}) | ({})", c1, c2),
            Quantifier(q, x, c) => write!(f, "{}{}.{}", q, x, c),
        }
    }
}

impl Top for Constraint {
    fn mk_true() -> Constraint {
        Constraint::new(ConstraintExpr::True)
    }
    fn is_true(&self) -> bool {
        match self.kind() {
            ConstraintExpr::True => true,
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

    pub fn mk_quantifier_int(q: QuantifierKind, v: Ident, c: Constraint) -> Constraint {
        Constraint::new(ConstraintExpr::Quantifier(
            q,
            Variable::mk(v, Type::mk_type_int()),
            c,
        ))
    }

    pub fn mk_arrow(x: Constraint, y: Constraint) -> Option<Constraint> {
        x.negate().map(|x| Constraint::mk_disj(x, y))
    }

    pub fn mk_pred(k: PredKind, v: Vec<Op>) -> Constraint {
        Constraint::new(ConstraintExpr::Pred(k, v))
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
                x.fv_with_vec(fvs);
                fvs.remove(&v.id);
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
        println!("Ident::from_str: {}", s);
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
        write!(f, "x_{}: {}", self.id, self.ty)
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
    pub fn fresh_prop() -> Variable {
        Variable::fresh(Type::mk_type_prop())
    }
}

#[derive(Clone, Debug)]
pub enum Fixpoint {
    Greatest,
    Least,
}
