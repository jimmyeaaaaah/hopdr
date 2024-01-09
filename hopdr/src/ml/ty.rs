use crate::util::P;
use std::fmt;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum TypeKind {
    Proposition,
    Unit,
    Integer,
    Arrow(Type, Type),
    Tuple(Vec<Type>),
}

pub type Type = P<TypeKind>;
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TypeKind::Proposition => write!(f, "b"),
            TypeKind::Integer => write!(f, "i"),
            TypeKind::Unit => write!(f, "unit"),
            TypeKind::Arrow(x, y) => write!(f, "({} -> {})", x, y),
            TypeKind::Tuple(ts) => {
                write!(f, "(")?;
                let mut first = true;
                for t in ts.iter() {
                    if first {
                        first = false;
                    } else {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", t)?;
                }
                write!(f, ")")
            }
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
    pub fn mk_type_unit() -> Type {
        Type::new(TypeKind::Unit)
    }
    pub fn mk_type_arrow(lhs: Type, rhs: Type) -> Type {
        Type::new(TypeKind::Arrow(lhs, rhs))
    }
    pub fn mk_tuple(ts: Vec<Type>) -> Type {
        Type::new(TypeKind::Tuple(ts))
    }
    pub fn is_int(&self) -> bool {
        matches!(self.kind(), TypeKind::Integer)
    }
    pub fn is_prop(&self) -> bool {
        matches!(self.kind(), TypeKind::Proposition)
    }
    pub fn is_unit(&self) -> bool {
        matches!(self.kind(), TypeKind::Unit)
    }
    pub fn order(&self) -> usize {
        match self.kind() {
            TypeKind::Proposition => 0,
            TypeKind::Integer => 0,
            TypeKind::Unit => 0,
            TypeKind::Arrow(x, y) => std::cmp::max(x.order() + 1, y.order()),
            TypeKind::Tuple(ts) => ts.iter().map(|x| x.order()).max().unwrap(),
        }
    }
    pub fn arrow<'a>(&'a self) -> (&'a Self, &'a Self) {
        match self.kind() {
            TypeKind::Arrow(x, y) => (x, y),
            _ => panic!("not an arrow"),
        }
    }
}
