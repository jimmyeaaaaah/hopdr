

use rpds::{HashTrieMap};

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
    let clauses = input.clauses.iter().map(|clause| {
        alpha_rename_clause(env.clone(), clause)
    }).collect();
    let toplevel = alpha_rename_expr(env, &input.toplevel);
    Out{ clauses, toplevel }
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

fn alpha_rename_expr(env: Environment, expr: &Expr<parse::Ident, SimpleType>) -> Expr<formula::Ident, SimpleType>  {
    let f = alpha_rename_expr;
    use ExprKind::*;
    match expr.kind() {
        Var(i) => Expr::mk_var(env.get(i).unwrap().clone()),
        Num(x) => Expr::mk_num(x.clone()), 
        True => Expr::mk_true(),
        False => Expr::mk_false(),
        Op(op, e1, e2) => Expr::mk_op(op.clone(), f(env.clone(), e1), f(env, e2)),
        Pred(p, e1, e2) => Expr::mk_pred(p.clone(), f(env.clone(), e1), f(env, e2)),
        App(e1, e2) => Expr::mk_app(f(env.clone(), e1), f(env, e2)),
        And(e1, e2) => Expr::mk_and(f(env.clone(), e1), f(env, e2)),
        Or(e1, e2) => Expr::mk_or(f(env.clone(), e1), f(env, e2)),
        Univ(x, e) => {
            let id = formula::Ident::fresh();
            let env = env.insert(&x.id, id.clone());
            let v = VariableS{ id, ty: x.ty.clone() };
            Expr::mk_univ(v, f(env, e))
        }
    }
}

fn alpha_rename_clause<'a>(mut env: Environment<'a>, c: &'a InClause) -> OutClause {
    let args = Vec::new();
    for arg in c.args.iter() {
        let k = formula::Ident::fresh();
        env = env.insert(arg, k);
    }

    let id = env.get(&c.id.id).unwrap().clone();
    let ty = c.id.ty.clone();
    let id = VariableS{ id, ty };
    let expr = alpha_rename_expr(env, &c.expr);
    Clause{ args, id, expr }
}

fn alpha_rename_clauses<'a>(mut env: Environment<'a>, c: &'a [InClause]) -> Environment<'a> {
    for clause in c.iter() {
        let k = formula::Ident::fresh();
        env = env.insert(&clause.id.id, k);
    }
    env
}