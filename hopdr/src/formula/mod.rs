pub mod parse;

#[derive(Copy, Clone, Debug)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Mod
}

#[derive(Copy, Clone, Debug)]
pub enum Pred {
    Eq,
    Neq,
    Leq,
    Gt
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
