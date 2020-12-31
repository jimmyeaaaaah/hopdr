use crate::util::P;
use crate::formula::{Op, Pred};

type Ident = String;

#[derive(Clone, Debug)]
pub enum Expr {
    Var(Ident),
    Num(i64),
    True,
    False,
    Op(Op, P<Expr>, P<Expr>),
    Pred(Pred, P<Expr>, P<Expr>),
    App(P<Expr>, P<Expr>),
    And(P<Expr>, P<Expr>),
    Or(P<Expr>, P<Expr>),
}

#[derive(Clone, Debug)]
pub enum SimpleType {
    Proposition,
    Integer,
    Arrow(P<SimpleType>, P<SimpleType>)
}

#[derive(Clone, Debug)]
pub struct Variable {
    pub id: Ident,
    pub ty: SimpleType,
}

#[derive(Clone, Debug)]
pub struct NuFormula {
    pub id: Ident,
    pub args: Vec<Variable>,
    pub expr: Expr,
}