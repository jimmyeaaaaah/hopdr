use crate::formula::{Ident, Type};

#[derive(Clone, Debug)]
pub struct Variable {
    pub id: Ident,
    pub name: String,
    pub ty: Option<Type>,
}

impl Variable {
    pub fn new(id: Ident, name: String) -> Variable {
        Variable { id, name, ty: None }
    }
    pub fn ty(mut self, ty: Type) -> Variable {
        self.ty = Some(ty);
        self
    }
}

pub type VariableMap = std::collections::HashMap<Ident, Variable>;
