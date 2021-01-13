use std::fmt;
use crate::util::P;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TypeKind {
    Proposition,
    Integer,
    Arrow(Type, Type)
}

impl fmt::Display for TypeKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeKind::Proposition => write!(f, "bool"),
            TypeKind::Integer => write!(f, "integer"),
            TypeKind::Arrow(x, y) => write!(f, "{} -> {}", x, y),
        }
    }
}

pub type Type = P<TypeKind>;