pub mod ty;
pub mod pcsp;

use std::{collections::HashSet, fmt};

use rpds::Stack;

pub use crate::formula::ty::*;
pub use crate::util::P;
use crate::util::{global_counter};


#[derive(Clone, Copy, Debug)]
pub enum PredKind {
    Eq,
    Neq,
    Leq,
    Gt
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
#[derive(Clone, Copy, Debug)]
pub enum OpKind {
    Add,
    Sub,
    Mul,
    Div,
    Mod
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

#[derive(Debug)]
pub enum OpExpr {
    Op(OpKind, Op, Op),
    Var(Ident),
    Const(i64),
}

pub type Op = P<OpExpr>;

#[derive(Clone)]
pub struct IntegerEnvironment {
    imap: Stack<Ident>,
}

impl IntegerEnvironment {
    pub fn new() -> IntegerEnvironment {
        IntegerEnvironment{ imap: Stack::new() }
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

    fn subst(&self, id: &Ident, v: &Op) -> Op {
        match self.kind() {
            OpExpr::Op(k, x, y) => 
                Op::mk_bin_op(*k, x.subst(id, v), y.subst(id, v)),
            
            OpExpr::Var(id2) if id == id2 => v.clone(),
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

pub trait Subst {
    fn subst(&self, x: &Ident, v: &Op) -> Self;
}

#[derive(Debug)]
pub enum ConstraintExpr {
    True,
    False,
    Pred(PredKind, Vec<Op>),
    Conj(Constraint, Constraint),
    Disj(Constraint, Constraint),
    Univ(Variable, Constraint),
}

pub type Constraint = P<ConstraintExpr>;

impl Top for Constraint {
    fn mk_true() -> Constraint {
        Constraint::new(ConstraintExpr::True)
    }
}

impl Conjunctive for Constraint {
    fn mk_conj(x: Constraint, y: Constraint) -> Constraint {
        Constraint::new(ConstraintExpr::Conj(x, y))
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
            },
            Conj(r, l) => Constraint::mk_conj(r.subst(x, v), l.subst(x, v)),
            Disj(r, l) => Constraint::mk_disj(r.subst(x, v), l.subst(x, v)),
            Univ(var, cstr) => 
                Constraint::mk_univ(var.clone(), cstr.subst(x, v)),
        }
    }
}

impl Constraint {
    pub fn mk_false() -> Constraint {
        Constraint::new(ConstraintExpr::False)
    }

    pub fn mk_univ(v: Variable, c: Constraint) -> Constraint {
        Constraint::new(ConstraintExpr::Univ(v, c))
    }

    pub fn mk_disj(x: Constraint, y: Constraint) -> Constraint {
        Constraint::new(ConstraintExpr::Disj(x, y))
    }

    pub fn mk_pred(k: PredKind, v: Vec<Op>) -> Constraint {
        Constraint::new(ConstraintExpr::Pred(k, v))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Ident {
    id: u64,
}

impl Ident {
    pub fn fresh() -> Ident {
        let id = global_counter();
        Ident { id }
    }
}

#[derive(Debug)]
pub struct VariableS {
    pub id: Ident,
    pub ty: Type,
}
pub type Variable = P<VariableS>;

impl Variable {
    pub fn mk(id: Ident, ty: Type) -> Variable {
        Variable::new(VariableS{ id, ty })
    }
    pub fn id(&self) -> Ident {
        self.id
    }
    pub fn ty(&self) -> &Type {
        &self.ty
    }
}

#[derive(Clone, Debug)]
pub enum Fixpoint {
    Greatest,
    Least,
}
