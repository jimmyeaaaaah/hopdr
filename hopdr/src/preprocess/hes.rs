use std::{collections::HashMap, thread::current, unimplemented};
use std::cell::RefCell;


use crate::util::P;
use crate::formula::{Op, Pred};
use super::simple_type;
use crate::parse;

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
pub struct Variable {
    pub id: Ident,
    pub ty: simple_type::Type,
}

#[derive(Clone, Debug)]
pub struct Clause {
    pub id: Ident,
    pub args: Vec<Variable>,
    pub expr: Expr,
}


#[derive(Clone, Debug)]
pub struct ValidityChecking {
    pub formulas: Vec<Clause>,
    pub toplevel: Expr,
}

struct TypeVariable {
    id: u64 
}
static TYVAR_COUNTER: RefCell<u64> = RefCell::new(0);
impl TypeVariable {
    fn new() -> TypeVariable {
        let counter = TYVAR_COUNTER.borrow_mut();
        let id= *counter;
        *counter = *counter + 1;
        TypeVariable{id}
    }
}

enum TmpType {
    Proposition,
    Integer,
    Arrow(P<TmpType>, P<TmpType>),
    Var(TypeVariable)
}

impl TmpType {
    fn new_type_variable() -> TmpType {
        TmpType::Var(TypeVariable::new())
    }
    fn new_type_arrow(arg: TmpType, ret: TmpType) -> TmpType {
        TmpType::Arrow(P(arg), P(ret))
    }
}

impl Clause {
    fn from(vc: parse::Clause) -> Clause {
        unimplemented!()
    }
    fn gen_tmp_type(&self) -> TmpType {
        let ret_ty= TmpType::new_type_variable();
        let mut current_ty = ret_ty;
        for arg in self.args.iter() {
            let arg_ty = TmpType::new_type_variable();
            current_ty = TmpType::new_type_arrow(arg_ty, ret_ty);
        }
        current_ty
    }
}

struct Constraint {
    left: TmpType,
    right: TmpType
}

struct Environment {
    map: HashMap<Ident, TmpType>
}

impl Environment {
    fn new() -> Environment {
        Environment{map: HashMap::new()}
    }
    fn add(&mut self, id: Ident, ty: TmpType) {
        self.map.insert(id, ty);
    }
}

fn generate_global_environment(formulas: Vec<parse::Clause>) -> Environment {
    for formula in formulas.iter() {
        formula.
    }
    unimplemented!()
}

fn typing(formulas: Vec<parse::Clause>) -> Vec<Clause> {
    unimplemented!()
}

impl ValidityChecking {
    fn from(vc: parse::Problem) -> ValidityChecking {
       // simple type checking
       // gamma: type environment
       // unify
       match vc {
           parse::Problem::NuHFLZValidityChecking(vc) => {
                unimplemented!()
           }
       }
    }
}