use super::hes::ValidityChecking;
use crate::formula;
use crate::formula::hes;
use crate::formula::{
    Bot, Ident, Logic, Type as SimpleType, TypeKind as SimpleTypeKind,
};
use std::collections::HashMap;

type In = ValidityChecking<formula::Ident, SimpleType>;
type Out = hes::Problem<formula::Constraint>;

pub fn transform(input: In) -> Out {
    let mut clauses = Vec::new();
    let mut env = HashMap::new();

    for clause in input.clauses.iter() {
        env.insert(clause.id.id, clause.id.ty.clone());
    }

    for clause in input.clauses {
        let c = transform_clause(clause, env.clone());
        env.insert(c.head.id, c.head.ty.clone());
        clauses.push(c);
    }
    let top = transform_expr(&input.toplevel, &mut env);
    Out { clauses, top }
}

type InClause = super::hes::Clause<formula::Ident, SimpleType>;
type OutClause = formula::hes::Clause<formula::Constraint>;
type InExpr = super::hes::Expr<formula::Ident, SimpleType>;
type OutExpr = formula::hes::Goal<formula::Constraint>;

enum EitherExpr {
    Op(formula::Op),
    Goal(OutExpr),
    Var(Ident),
    Constr(formula::Constraint),
}

impl EitherExpr {
    fn goal(self) -> OutExpr {
        match self {
            EitherExpr::Var(name) => OutExpr::mk_var(name),
            EitherExpr::Goal(g) => g,
            EitherExpr::Constr(c) => OutExpr::mk_constr(c),
            EitherExpr::Op(o) => OutExpr::mk_op(o),
        }
    }
    fn op(self) -> formula::Op {
        match self {
            EitherExpr::Op(o) => o,
            _ => panic!("program error"),
        }
    }
    fn mk_goal(c: OutExpr) -> EitherExpr {
        EitherExpr::Goal(c)
    }
    fn mk_op(x: formula::Op) -> EitherExpr {
        EitherExpr::Op(x)
    }
    fn mk_var(x: Ident) -> EitherExpr {
        EitherExpr::Var(x)
    }
    fn mk_constraint(x: formula::Constraint) -> EitherExpr {
        EitherExpr::Constr(x)
    }
    fn mk_conj(x: EitherExpr, y: EitherExpr) -> EitherExpr {
        match (x, y) {
            (EitherExpr::Constr(x), EitherExpr::Constr(y)) => {
                EitherExpr::mk_constraint(formula::Constraint::mk_conj(x, y))
            }
            (x, y) => {
                let x = x.goal();
                let y = y.goal();
                EitherExpr::mk_goal(OutExpr::mk_conj(x, y))
            }
        }
    }
    fn mk_disj(x: EitherExpr, y: EitherExpr) -> EitherExpr {
        match (x, y) {
            (EitherExpr::Constr(x), EitherExpr::Constr(y)) => {
                EitherExpr::mk_constraint(formula::Constraint::mk_disj(x, y))
            }
            (x, y) => {
                let x = x.goal();
                let y = y.goal();
                EitherExpr::mk_goal(OutExpr::mk_disj(x, y))
            }
        }
    }
}

fn transform_expr_inner(input: &InExpr, env: &mut HashMap<Ident, SimpleType>) -> EitherExpr {
    let f = transform_expr_inner;
    use super::hes::ExprKind::*;
    use formula::hes::Goal;
    use formula::Top;
    match input.kind() {
        Var(x) => {
            match env
                .get(x)
                .unwrap_or_else(|| panic!("failed to find: {}", x))
                .kind()
            {
                SimpleTypeKind::Integer => EitherExpr::mk_op(formula::Op::mk_var(*x)),
                _ => EitherExpr::mk_var(*x),
            }
        }
        App(e1, e2) => {
            let e1 = f(e1, env).goal();
            let e2 = f(e2, env).goal();
            EitherExpr::mk_goal(OutExpr::mk_app(e1, e2))
        }
        Num(x) => EitherExpr::mk_op(formula::Op::mk_const(*x)),
        True => EitherExpr::mk_constraint(formula::Constraint::mk_true()),
        False => EitherExpr::mk_constraint(formula::Constraint::mk_false()),
        Op(x, y, z) => {
            let e1 = transform_expr_inner(y, env).op();
            let e2 = transform_expr_inner(z, env).op();
            EitherExpr::mk_op(formula::Op::mk_bin_op(*x, e1, e2))
        }
        Pred(p, x, y) => {
            let x = transform_expr_inner(x, env).op();
            let y = transform_expr_inner(y, env).op();
            EitherExpr::mk_constraint(formula::Constraint::mk_pred(*p, vec![x, y]))
        }
        And(x, y) => {
            let x = transform_expr_inner(x, env);
            let y = transform_expr_inner(y, env);
            EitherExpr::mk_conj(x, y)
        }
        Or(x, y) => {
            let x = transform_expr_inner(x, env);
            let y = transform_expr_inner(y, env);
            EitherExpr::mk_disj(x, y)
        }
        Univ(x, y) => {
            let old = env.insert(x.id, x.ty.clone());
            let y = transform_expr_inner(y, env).goal();
            match old {
                Some(old) => {
                    env.insert(x.id, old);
                }
                None => {
                    env.remove(&x.id);
                }
            }
            EitherExpr::mk_goal(Goal::mk_univ(x.clone().into(), y))
        }
        Abs(x, y) => {
            let old = env.insert(x.id, x.ty.clone());
            let y = transform_expr_inner(y, env).goal();
            match old {
                Some(old) => {
                    env.insert(x.id, old);
                }
                None => {
                    env.remove(&x.id);
                }
            }
            EitherExpr::mk_goal(Goal::mk_abs(x.clone().into(), y))
        }
    }
}

fn transform_expr(
    expr: &InExpr,
    env: &mut HashMap<Ident, SimpleType>,
) -> formula::hes::Goal<formula::Constraint> {
    transform_expr_inner(expr, env).goal()
}

fn append_args(mut body: InExpr, args: &[Ident], mut t: SimpleType) -> InExpr {
    let mut variables = Vec::new();
    for arg in args {
        let (arg_ty, ret_t) = match t.kind() {
            formula::TypeKind::Arrow(x, y) => (x.clone(), y.clone()),
            _ => panic!("program error"),
        };
        let v = crate::preprocess::hes::VariableS {
            id: *arg,
            ty: arg_ty.clone(),
        };
        t = ret_t;
        variables.push(v);
    }
    variables.reverse();
    for v in variables {
        body = InExpr::mk_abs(v, body);
    }
    body
}

fn transform_clause(input: InClause, mut env: HashMap<Ident, SimpleType>) -> OutClause {
    let input_expr = append_args(input.expr, &input.args, input.id.ty.clone());
    let body = transform_expr(&input_expr, &mut env);
    OutClause::new(body, input.id.into())
}
