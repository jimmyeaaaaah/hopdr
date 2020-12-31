pub mod parse;

use std::fmt;

#[derive(Copy, Clone, Debug)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Mod
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Op::Add => "+",
                Op::Sub => "-",
                Op::Mul => "*",
                Op::Div => "/",
                Op::Mod => "%",
            }
        )
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Pred {
    Eq,
    Neq,
    Leq,
    Gt
}

impl fmt::Display for Pred {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Pred::Le => "<=",
                Pred::Gt => ">",
                Pred::Eq => "=",
                Pred::Neq => "!=",
            }
        )
    }
}


#[derive(Clone, Debug)]
pub enum Constraint {
    True,
    False,
    Op(Op, Box<Constraint>, Box<Constraint>),
    Pred(Pred, Box<Constraint>, Box<Constraint>),
    Conj(Box<Constraint>, Box<Constraint>),
    Disj(Box<Constraint>, Box<Constraint>)
}

#[derive(Copy, Clone, Debug)]
pub struct Variable {
    id: u64,
}

#[derive(Clone, Debug)]
pub struct Clause {
    body: Vec<Variable>,
    constraint: Constraint,
    head: Variable
}
