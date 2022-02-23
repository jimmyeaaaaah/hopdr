use crate::util::P;
use std::fmt;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TypeKind {
    Proposition,
    Integer,
    Arrow(Type, Type),
}

pub type Type = P<TypeKind>;
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TypeKind::Proposition => write!(f, "bool"),
            TypeKind::Integer => write!(f, "integer"),
            TypeKind::Arrow(x, y) => write!(f, "({} -> {})", x, y),
        }
    }
}

impl Type {
    // should be a singleton object..
    pub fn mk_type_prop() -> Type {
        Type::new(TypeKind::Proposition)
    }
    pub fn mk_type_int() -> Type {
        Type::new(TypeKind::Integer)
    }
    pub fn mk_type_arrow(lhs: Type, rhs: Type) -> Type {
        Type::new(TypeKind::Arrow(lhs, rhs))
    }
    pub fn is_int(&self) -> bool {
        match self.kind() {
            TypeKind::Integer => true,
            _ => false,
        }
    }
    pub fn is_prop(&self) -> bool {
        match self.kind() {
            TypeKind::Proposition => true,
            _ => false,
        }
    }
    pub fn order(&self) -> usize {
        match self.kind() {
            TypeKind::Proposition => 0,
            TypeKind::Integer => 0,
            TypeKind::Arrow(x, y) => std::cmp::max(x.order() + 1, y.order()),
        }
    }
}
