use std::{collections::HashMap, unimplemented};



use crate::util::{P, global_counter};
use crate::formula::{Op, PredKind, Type as SimpleType};
use crate::parse;

type Ident = String;

#[derive(Debug)]
pub enum Expr {
    Var(Ident),
    Num(i64),
    True,
    False,
    Op(Op, P<Expr>, P<Expr>),
    Pred(PredKind, P<Expr>, P<Expr>),
    App(P<Expr>, P<Expr>),
    And(P<Expr>, P<Expr>),
    Or(P<Expr>, P<Expr>),
}

#[derive(Clone, Debug)]
pub struct Variable {
    pub id: Ident,
    pub ty: SimpleType,
}

#[derive(Debug)]
pub struct Clause {
    pub id: Ident,
    pub args: Vec<Variable>,
    pub expr: Expr,
}


#[derive(Debug)]
pub struct ValidityChecking {
    pub formulas: Vec<Clause>,
    pub toplevel: Expr,
}

struct TypeVariable {
    id: u64 
}

impl TypeVariable {
    fn new() -> TypeVariable {
        let id = global_counter();
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
    fn from(_vc: parse::Clause) -> Clause {
        unimplemented!()
    }
}

impl parse::Expr {
    fn append_constraints(&self, _ty: TmpType, _env: &Environment, _constraints: &mut Vec<Constraint>) {
        
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
    
    fn append_constraints(&self, _env: &Environment, _constraints: &mut Vec<Constraint>) {
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
    let _env = generate_global_environment(&formulas);
    unimplemented!()
}

impl ValidityChecking {
    fn from(vc: parse::Problem) -> ValidityChecking {
       // simple type checking
       // gamma: type environment
       // unify
       match vc {
           parse::Problem::NuHFLZValidityChecking(_vc) => {
                unimplemented!()
           }
       }
    }
}