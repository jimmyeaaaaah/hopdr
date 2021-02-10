use crate::util::P;
use std::fmt;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TypeKind {
    Proposition,
    Integer,
    Arrow(Type, Type),
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

impl Type {
    // should be a singleton object..
    pub fn mk_type_prop() -> Type {
        Type::new(TypeKind::Proposition)
    }
    pub fn mk_type_int() -> Type {
        Type::new(TypeKind::Proposition)
    }
    pub fn mk_type_arrow(lhs: Type, rhs: Type) -> Type {
        Type::new(TypeKind::Arrow(lhs, rhs))
    }
}
