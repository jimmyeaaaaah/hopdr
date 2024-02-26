use super::hes::{Clause, Expr, ExprKind, ValidityChecking, VariableS};
use super::{Context, IdentMap as Environment};
use crate::formula;
use crate::formula::Type as SimpleType;
use crate::parse;

type In = ValidityChecking<parse::Ident, SimpleType>;
type Out = ValidityChecking<formula::Ident, SimpleType>;

type InClause = Clause<parse::Ident, SimpleType>;
type OutClause = Clause<formula::Ident, SimpleType>;

pub fn alpha_renaming(input: In) -> (Out, Context) {
    let env = Environment::new();
    let env = alpha_rename_clauses(env, &input.clauses);
    let clauses = input
        .clauses
        .iter()
        .map(|clause| alpha_rename_clause(env.clone(), clause))
        .collect();
    let toplevel = alpha_rename_expr(env.clone(), &input.toplevel);
    let ctx = Context::new(env, input);
    (Out { clauses, toplevel }, ctx)
}

fn alpha_rename_expr(
    env: Environment,
    expr: &Expr<parse::Ident, SimpleType>,
) -> Expr<formula::Ident, SimpleType> {
    let f = alpha_rename_expr;
    use ExprKind::*;
    match expr.kind() {
        Var(i) => Expr::mk_var(*env.get(i).unwrap()),
        Num(x) => Expr::mk_num(*x),
        True => Expr::mk_true(),
        False => Expr::mk_false(),
        Op(op, e1, e2) => Expr::mk_op(*op, f(env.clone(), e1), f(env, e2)),
        Pred(p, e1, e2) => Expr::mk_pred(*p, f(env.clone(), e1), f(env, e2)),
        App(e1, e2) => Expr::mk_app(f(env.clone(), e1), f(env, e2)),
        And(e1, e2) => Expr::mk_and(f(env.clone(), e1), f(env, e2)),
        Or(e1, e2) => Expr::mk_or(f(env.clone(), e1), f(env, e2)),
        Univ(x, e) => {
            let id = formula::Ident::fresh();
            let mut env = env.clone();
            env.insert(x.id.clone(), id);
            let v = VariableS {
                id,
                ty: x.ty.clone(),
            };
            Expr::mk_univ(v, f(env, e))
        }
        Abs(x, e) => {
            let id = formula::Ident::fresh();
            let mut env = env.clone();
            env.insert(x.id.clone(), id);
            let v = VariableS {
                id,
                ty: x.ty.clone(),
            };
            Expr::mk_abs(v, f(env, e))
        }
    }
}

fn alpha_rename_clause(mut env: Environment, c: &InClause) -> OutClause {
    let mut args = Vec::new();
    for arg in c.args.iter() {
        let k = formula::Ident::fresh();
        env.insert(arg.clone(), k);
        args.push(k);
    }

    let id = *env.get(&c.id.id).unwrap();
    let ty = c.id.ty.clone();
    let id = VariableS { id, ty };
    let expr = alpha_rename_expr(env, &c.expr);
    Clause { args, id, expr }
}

fn alpha_rename_clauses(mut env: Environment, c: &[InClause]) -> Environment {
    for clause in c.iter() {
        let k = formula::Ident::fresh();
        env.insert(clause.id.id.clone(), k);
    }
    env
}
