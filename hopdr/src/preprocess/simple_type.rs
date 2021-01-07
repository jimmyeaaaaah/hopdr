use std::fmt;
use crate::util::P;

#[derive(Clone, Debug)]
pub enum Type {
    Proposition,
    Integer,
    Arrow(P<Type>, P<Type>)
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Proposition => write!(f, "bool"),
            Type::Integer => write!(f, "integer"),
            Type::Arrow(x, y) => write!(f, "{} -> {}", x, y),
        }
    }
}
