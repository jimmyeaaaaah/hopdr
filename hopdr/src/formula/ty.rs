use rpds::HashTrieMap;

use crate::util::P;
use std::fmt;

use super::{Ident, TeXFormat, TeXPrinter};

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
            TypeKind::Proposition => write!(f, "b"),
            TypeKind::Integer => write!(f, "i"),
            TypeKind::Arrow(x, y) => write!(f, "({} -> {})", x, y),
        }
    }
}

impl TeXFormat for Type {
    fn tex_fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TypeKind::Proposition => write!(f, "\\stypebool "),
            TypeKind::Integer => write!(f, "\\stypeint "),
            TypeKind::Arrow(x, y) => write!(f, "({} \\to {})", TeXPrinter(x), TeXPrinter(y)),
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

#[derive(Clone, Debug)]
pub struct Environment {
    map: HashTrieMap<Ident, Type>,
}

impl fmt::Display for Environment {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;
        for (i, t) in self.map.iter() {
            write!(f, "{}: {}, ", i, t)?;
        }
        write!(f, "]")
    }
}

impl<'a> Environment {
    pub fn new() -> Environment {
        Environment {
            map: HashTrieMap::new(),
        }
    }
    pub fn add(&mut self, id: Ident, ty: Type) {
        self.map = self.map.insert(id, ty);
    }
    pub fn del(&mut self, id: &Ident) {
        self.map = self.map.remove(id);
    }
    pub fn get(&self, id: &Ident) -> Option<Type> {
        self.map.get(id).cloned()
    }
}

pub fn generate_global_environment<C>(formulas: &Vec<super::hes::Clause<C>>) -> Environment {
    let mut env = Environment::new();
    for formula in formulas.iter() {
        env.add(formula.head.id, formula.head.ty.clone());
    }
    env
}
