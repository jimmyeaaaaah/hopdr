
use std::{collections::HashMap, unimplemented};

use rpds::{HashTrieMap, Stack};

use super::hes::{ExprKind, Expr, Clause, ValidityChecking, VariableS};
use crate::formula::{Ident, Type as SimpleType};

type V = VariableS<Ident, SimpleType>;

type InClause = Clause<Ident, SimpleType>;
type OutClause = Clause<V, SimpleType>;

type Environment = HashMap<Ident, V>;

fn translate(env: &mut Environment, e: &Expr<Ident>) -> Expr<V> {
    use ExprKind::*;
    match e.kind() {
        Var(v) => {
            Expr::mk_var(env.get(v).unwrap().clone())
        },
        Num(x) => Expr::mk_num(*x),
        True => Expr::mk_true(),
        False => Expr::mk_false(),
        Op(op, x, y) => Expr::mk_op(op.clone(), translate(env, x), translate(env, y)),
        Pred(p, x, y) => Expr::mk_pred(p.clone(), translate(env, x), translate(env, y)),
        App(x, y) => Expr::mk_app(translate(env, x), translate(env, y)),
        And(x, y) => Expr::mk_and(translate(env, x), translate(env, y)),
        Or(x, y) => Expr::mk_or(translate(env, x), translate(env, y)),
        Univ(x, y) => {
            env.insert(x.clone(), )
        }
    }
}