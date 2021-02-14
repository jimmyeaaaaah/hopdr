use std::{collections::HashMap, unimplemented};

use rpds::{HashTrieMap, Stack};

use super::hes::{ExprKind, Expr, Clause, ValidityChecking, VariableS};
use crate::formula;
use crate::formula::{Type as SimpleType};
use crate::parse;

type InVar = VariableS<parse::Ident, SimpleType>;
type OutVar = VariableS<formula::Ident, SimpleType>;

type In = ValidityChecking<parse::Ident, SimpleType>;
type Out = ValidityChecking<formula::Ident, SimpleType>;

type InClause = Clause<parse::Ident, SimpleType>;
type OutClause = Clause<formula::Ident, SimpleType>;

pub fn alpha_renaming(input: In) -> Out {
    let env = Environment::new();
    let env = alpha_rename_clauses(env, &input.clauses);
    for clause in input.clauses.iter() {
        alpha_rename_clause(env.clone(), clause);
    }
    unimplemented!()
}

type Environment<'a> = HashTrieMap<&'a parse::Ident, formula::Ident>;

//struct Context {
//    map: HashMap<formula::Ident, parse::Ident>,
//}
//
//impl Context {
//    fn new() -> Context {
//        Context{ map: HashMap::new() }
//    }
//    fn insert(&mut self, k: formula::Ident, v: parse::Ident) {
//        self.map.insert(k, v).unwrap();
//    }
//    fn add<'a>(&'a mut self, v: &parse::Ident) -> (&'a formula::Ident, &'a parse::Ident) {
//        let k = formula::Ident::fresh();
//        // should not be cloned
//        self.insert(k.clone(), v.clone());
//        self.map.get_key_value(&k).unwrap()
//    }
//    fn lookup(&self, k: &formula::Ident) -> &parse::Ident {
//        //&self.map.get(k).unwrap().1
//        unimplemented!()
//    }
//}

fn alpha_rename_expr(env: Environment, expr: &Expr<parse::Ident>) -> Expr<formula::Ident>  {
    unimplemented!()
}

fn alpha_rename_clause(env: Environment, c: &InClause) -> OutClause {
    use ExprKind::*;
    //let expr = c.expr;
    //match expr.kind() {
    //    Var(i) => Var
    //}
    unimplemented!()
}

fn alpha_rename_clauses<'a>(mut env: Environment<'a>, c: &'a [InClause]) -> Environment<'a> {
    for clause in c.iter() {
        let k = formula::Ident::fresh();
        env = env.insert(&clause.id.id, k);
    }
    env
}