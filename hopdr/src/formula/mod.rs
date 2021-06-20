pub mod hes;
pub mod pcsp;
pub mod chc;
pub mod ty;

use std::{fmt};
use std::collections::HashSet;

use rpds::Stack;

pub use crate::formula::ty::*;
use crate::util::global_counter;
pub use crate::util::P;

#[derive(Clone, Copy, Debug)]
pub enum PredKind {
    Eq,
    Neq,
    Leq,
    Gt,
}

impl fmt::Display for PredKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                PredKind::Leq => "<=",
                PredKind::Gt => ">",
                PredKind::Eq => "=",
                PredKind::Neq => "!=",
            }
        )
    }
}

impl PredKind {
    pub fn negate(&self) -> PredKind {
        match self {
            PredKind::Eq => PredKind::Neq,
            PredKind::Neq => PredKind::Eq,
            PredKind::Leq => PredKind::Gt,
            PredKind::Gt => PredKind::Leq,
        }
    }
}
#[derive(Clone, Copy, Debug)]
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

#[derive(Clone, Copy, Debug)]
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
            },
            OpExpr::Var(x) => {
                fvs.insert(x.clone());
            },
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
        return false;
    }
    pub fn variables(&self) -> Vec<Ident> {
        // assumes alpha-renamed
        self.imap.iter().copied().collect()
    }
    pub fn add(mut self, v: Ident) -> IntegerEnvironment {
        self.imap.push_mut(v);
        self
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

impl Subst for Op {
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

            OpExpr::Var(id3) if id == id3 => Op::mk_var(id2.clone()),
            _ => self.clone(),
        }
    }
}

pub trait Top {
    fn mk_true() -> Self;
}

pub trait Conjunctive {
    fn mk_conj(x: Self, y: Self) -> Self;
}

pub trait Subst : Sized {
    fn subst_multi(&self, substs: &[(Ident, Op)]) -> Self {
        assert!(substs.len() > 0);
        let mut ret = self.subst(&substs[0].0, &substs[0].1);
        for (ident, val) in &substs[1..] {
            ret = ret.subst(ident, val);
        }
        ret
    }
    fn subst(&self, x: &Ident, v: &Op) -> Self;
    fn rename_variable(&self, x: &Ident, y: &Ident) -> Self {
        let op = Op::mk_var(y.clone());
        self.subst(x, &op)
    }
}

pub trait Rename : Sized {
    fn rename(&self, x: &Ident, y: &Ident) -> Self;
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
                if ops.len() > 0 {
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
}

impl Conjunctive for Constraint {
    fn mk_conj(x: Constraint, y: Constraint) -> Constraint {
        if x.is_true() {
            y
        } else if y.is_true() {
            x
        } else {
            Constraint::new(ConstraintExpr::Conj(x, y))
        }
    }
}

impl Subst for Constraint {
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
            Quantifier(q, var, cstr) => Constraint::mk_quantifier(*q, var.clone(), cstr.subst(x, v)),
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
            Quantifier(q, var, cstr) if &var.id != x && &var.id != y => Constraint::mk_quantifier(*q, var.clone(), cstr.rename(x, y)),
            Quantifier(q, var, cstr) => panic!("assumption broken"),
        }
    }
}

impl Constraint {
    pub fn is_true(&self) -> bool {
        match self.kind() {
            ConstraintExpr::True => true,
            _ => false,
        }
    }
    pub fn is_false(&self) -> bool {
        match self.kind() {
            ConstraintExpr::False => true,
            _ => false,
        }
    }
    pub fn mk_false() -> Constraint {
        Constraint::new(ConstraintExpr::False)
    }

    pub fn mk_quantifier(q: QuantifierKind, v: Variable, c: Constraint) -> Constraint {
        Constraint::new(ConstraintExpr::Quantifier(q, v, c))
    }

    pub fn mk_disj(x: Constraint, y: Constraint) -> Constraint {
        if x.is_true() {
            x
        } else if y.is_true() {
            y
        } else if x.is_false() {
            y
        } else if x.is_false() {
            x
        }else {
            Constraint::new(ConstraintExpr::Disj(x, y))
        }
    }

    // negation sometimes cannot be performed (e.g. \not x)
    pub fn negate(self) -> Option<Constraint> {
        match self.kind() {
            ConstraintExpr::False => Some(Constraint::mk_true()),
            ConstraintExpr::True => Some(Constraint::mk_false()),
            ConstraintExpr::Pred(p, v) => Some(Constraint::mk_pred(p.negate(), v.clone())),
            ConstraintExpr::Conj(c1, c2) => {
                match (c1.clone().negate(), c2.clone().negate()) {
                    (Some(c1), Some(c2)) => Some(Constraint::mk_disj(c1, c2)),
                    _ => None,
                }
            },
            ConstraintExpr::Disj(c1, c2) => {
                match (c1.clone().negate(), c2.clone().negate()) {
                    (Some(c1), Some(c2)) => Some(Constraint::mk_conj(c1, c2)),
                    _ => None,
                }
            },
            ConstraintExpr::Quantifier(q, v, c) => {
                let q = q.negate();
                c.clone().negate().map(|c| Constraint::mk_quantifier(q, v.clone(), c))
            }
        }
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
            ConstraintExpr::True | ConstraintExpr::False | ConstraintExpr::Pred(_, _) => self.clone(),
            ConstraintExpr::Conj(c1, c2) => Constraint::mk_conj(c1.clone().remove_quantifier(), c2.clone().remove_quantifier()),
            ConstraintExpr::Disj(c1, c2) => Constraint::mk_disj(c1.clone().remove_quantifier(), c2.clone().remove_quantifier()),
            ConstraintExpr::Quantifier(_, _, c) => c.clone().remove_quantifier(),
        }
    }

}
impl Fv for Constraint {
    type Id = Ident;

    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>) {
        match self.kind() {
            ConstraintExpr::True |  ConstraintExpr::False => {},
            ConstraintExpr::Pred(_, ops) => {
                for op in ops.iter() {
                    op.fv_with_vec(fvs);
                }
            }
            ConstraintExpr::Conj(x, y) | 
            ConstraintExpr::Disj(x , y) => {
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
        args.iter().map(|arg| {
            if arg == x {
                *y
            } else {
                *arg
            }
        }).collect()
    }
}

#[derive(Debug)]
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
        Variable::new(VariableS{ id ,ty })
    }
}

#[derive(Clone, Debug)]
pub enum Fixpoint {
    Greatest,
    Least,
}
