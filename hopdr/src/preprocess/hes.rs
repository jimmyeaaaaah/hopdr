use std::{collections::HashMap, unimplemented};

use rpds::HashTrieMap;

use crate::util::{P, global_counter};
use crate::formula::{OpKind, PredKind, Type as SimpleType};
use crate::parse;

type Ident = String;

#[derive(Debug)]
pub enum Expr {
    Var(Ident),
    Num(i64),
    True,
    False,
    Op(OpKind, P<Expr>, P<Expr>),
    Pred(PredKind, P<Expr>, P<Expr>),
    App(P<Expr>, P<Expr>),
    And(P<Expr>, P<Expr>),
    Or(P<Expr>, P<Expr>),
    Univ(Ident, P<Expr>)
}

#[derive(Clone, Debug)]
pub struct VariableS<Ty> {
    pub id: Ident,
    pub ty: Ty,
}
type Variable = VariableS<SimpleType>;

impl VariableS<TmpType> {
    fn new(id: Ident, ty: TmpType) -> VariableS<TmpType> {
        VariableS{ id, ty }
    }
}

#[derive(Debug)]
pub struct Clause<Ty> {
    pub id: VariableS<Ty>,
    pub args: Vec<Ident>,
    pub expr: Expr,
}

#[derive(Debug)]
pub struct ValidityChecking { 
    pub formulas: Vec<Clause<SimpleType>>,
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

enum TmpTypeKind {
    Proposition,
    Integer,
    Arrow(TmpType, TmpType),
    Var(TypeVariable)
}

type TmpType = P<TmpTypeKind>;


impl TmpType {
    fn new_type_variable() -> TmpType {
        TmpType::new(TmpTypeKind::Var(TypeVariable::new()))
    }
    fn new_type_arrow(arg: TmpType, ret: TmpType) -> TmpType {
        TmpType::new(TmpTypeKind::Arrow(arg, ret))
    }
}

impl Expr {
    pub fn from(e: parse::Expr) -> Expr {
        match e.into() {
            parse::ExprKind::Var(v) => Expr::Var(v),
            parse::ExprKind::Num(x) => Expr::Num(x),
            parse::ExprKind::True => Expr::True,
            parse::ExprKind::False => Expr::False,
            parse::ExprKind::Op(op, e1, e2) => Expr::Op(op, P::new(Expr::from(e1)), P::new(Expr::from(e2))),
            parse::ExprKind::Pred(p, e1, e2) => Expr::Pred(p, P::new(Expr::from(e1)), P::new(Expr::from(e2))),
            parse::ExprKind::App(e1, e2) => Expr::App(P::new(Expr::from(e1)), P::new(Expr::from(e2))),
            parse::ExprKind::And(e1, e2) => Expr::And(P::new(Expr::from(e1)), P::new(Expr::from(e2))),
            parse::ExprKind::Or(e1, e2) => Expr::Or(P::new(Expr::from(e1)), P::new(Expr::from(e2))),
            parse::ExprKind::Univ(x, e) => Expr::Univ(x, P::new(Expr::from(e))),
            _ => panic!("not implemented"),
            // parse::Expr::Fix(_, _, _) => {}
            // parse::Expr::Abs(_, _) => {}
            // parse::Expr::Exist(_, _) => {}
        }
    }
}

impl Clause<TmpType> {
    pub fn from(vc: parse::Clause) -> Clause<TmpType> {
        let t = vc.gen_tmp_type();
        let id = VariableS::new(vc.id, t);
        let expr = Expr::from(vc.expr);
        let c = Clause{id,args: vc.args, expr};
        c
    }
    fn append_constraints<'a>(&'a self, mut env: Environment<'a>, _constraints: &mut Vec<Constraint>) {
        let ret_ty= TmpType::new_type_variable();
        let mut current_ty = ret_ty;
        for arg in self.args.iter() {
            let arg_ty = TmpType::new_type_variable();
            current_ty = TmpType::new_type_arrow(arg_ty.clone(), current_ty);
            env.add(arg, arg_ty);
        }
    }
}


#[derive(Clone)]
struct Environment<'a> {
    map: HashTrieMap<&'a str, TmpType>
}

impl parse::Clause {
    fn gen_tmp_type(&self) -> TmpType {
        let ret_ty= TmpType::new_type_variable();
        //let mut current_ty = ret_ty;
        //for _arg in self.args.iter() {
        //    let arg_ty = TmpType::new_type_variable();
        //    current_ty = TmpType::new_type_arrow(arg_ty, current_ty);
        //}
        ret_ty 
    }
    
}

impl parse::Clause {
}

impl<'a> Environment<'a> {
    fn new() -> Environment<'a> {
        Environment{map: HashTrieMap::new()}
    }
    fn add(&mut self, id: &'a str, ty: TmpType) {
        self.map.insert(id, ty);
    }
}

fn generate_global_environment<'a>(formulas: &'a Vec<Clause<TmpType>>) -> Environment<'a> {
    let mut env = Environment::new();
    for formula in formulas.iter() {
        env.add(&formula.id.id, formula.id.ty.clone());
    }
    env
}


struct Constraint {
    left: TmpType,
    right: TmpType
}


fn typing(formulas: Vec<parse::Clause>) -> Vec<Clause<SimpleType>> {
    let formulas = formulas.into_iter().map(|x| Clause::<TmpType>::from(x)).collect();
    let env = generate_global_environment(&formulas);
    let mut constraints = Vec::new();
    for clause in formulas.iter() {
        clause.append_constraints(env.clone(), &mut constraints);
    }
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