use std::{collections::HashMap, thread::current, unimplemented};
use std::cell::RefCell;


use crate::util::P;
use crate::formula::{Op, Pred, Type as SimpleType};
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
    pub ty: SimpleType,
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
static mut TYVAR_COUNTER: u64 = 0;
impl TypeVariable {
    fn new() -> TypeVariable {
        let id = 
            unsafe {
                let tmp= TYVAR_COUNTER;
                TYVAR_COUNTER += 1;
                tmp
            };
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
}

impl parse::Expr {
    fn append_constraints(&self, ty: TmpType, env: &Environment, constraints: &mut Vec<Constraint>) {
        use parse::Expr::*;
       // match self {
       //     Var(x) => 
       // }
       unimplemented!()
    }
}

impl parse::Clause {
    fn gen_tmp_type(&self) -> TmpType {
        let ret_ty= TmpType::new_type_variable();
        let mut current_ty = ret_ty;
        for _arg in self.args.iter() {
            let arg_ty = TmpType::new_type_variable();
            current_ty = TmpType::new_type_arrow(arg_ty, current_ty);
        }
        current_ty
    }
    
    fn append_constraints(&self, env: &Environment, constraints: &mut Vec<Constraint>) {
        //self.expr.append_constraints(env, constraints);
    }
}

struct Environment<'a> {
    map: HashMap<&'a str, TmpType>
}

impl<'a> Environment<'a> {
    fn new() -> Environment<'a> {
        Environment{map: HashMap::new()}
    }
    fn add(&mut self, id: &'a str, ty: TmpType) {
        self.map.insert(id, ty);
    }
}

fn generate_global_environment<'a>(formulas: &'a Vec<parse::Clause>) -> Environment<'a> {
    let mut env = Environment::new();
    for formula in formulas.iter() {
        let ty = formula.gen_tmp_type();
        env.add(&formula.id, ty);
    }
    env
}


struct Constraint {
    left: TmpType,
    right: TmpType
}


fn typing(formulas: Vec<parse::Clause>) -> Vec<Clause> {
    let env = generate_global_environment(&formulas);
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