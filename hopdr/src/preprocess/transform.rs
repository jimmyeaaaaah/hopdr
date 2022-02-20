use super::hes::ValidityChecking;
use crate::formula;
use crate::formula::hes;
use crate::formula::{Bot, Conjunctive, Ident, Type as SimpleType, Variable};

type In = ValidityChecking<formula::Ident, SimpleType>;
type Out = hes::Problem<formula::Constraint>;

pub fn transform(input: In) -> Out {
    let mut clauses = Vec::new();

    for clause in input.clauses {
        let c = transform_clause(clause, &mut clauses);
        clauses.push(c);
    }
    let top = transform_expr(&input.toplevel, &mut clauses);
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
            EitherExpr::Var(c) => formula::Op::mk_var(c),
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

fn transform_expr_inner(input: &InExpr) -> EitherExpr {
    let f = transform_expr_inner;
    use super::hes::ExprKind::*;
    use formula::hes::Goal;
    use formula::Top;
    match input.kind() {
        Var(x) => EitherExpr::mk_var(*x),
        App(e1, e2) => {
            let e1 = f(e1).goal();
            let e2 = f(e2).goal();
            EitherExpr::mk_goal(OutExpr::mk_app(e1, e2))
        }
        Num(x) => EitherExpr::mk_op(formula::Op::mk_const(*x)),
        True => EitherExpr::mk_constraint(formula::Constraint::mk_true()),
        False => EitherExpr::mk_constraint(formula::Constraint::mk_false()),
        Op(x, y, z) => {
            let e1 = transform_expr_inner(y).op();
            let e2 = transform_expr_inner(z).op();
            EitherExpr::mk_op(formula::Op::mk_bin_op(*x, e1, e2))
        }
        Pred(p, x, y) => {
            let x = transform_expr_inner(x).op();
            let y = transform_expr_inner(y).op();
            EitherExpr::mk_constraint(formula::Constraint::mk_pred(*p, vec![x, y]))
        }
        And(x, y) => {
            let x = transform_expr_inner(x);
            let y = transform_expr_inner(y);
            EitherExpr::mk_conj(x, y)
        }
        Or(x, y) => {
            let x = transform_expr_inner(x);
            let y = transform_expr_inner(y);
            EitherExpr::mk_disj(x, y)
        }
        Univ(x, y) => {
            let y = transform_expr_inner(y).goal();
            EitherExpr::mk_goal(Goal::mk_univ(x.clone().into(), y))
        }
        Abs(x, y) => {
            let y = transform_expr_inner(y).goal();
            EitherExpr::mk_goal(Goal::mk_abs(x.clone().into(), y))
        }
    }
}

fn transform_expr(
    expr: &InExpr,
    _clauses: &mut Vec<OutClause>,
) -> formula::hes::Goal<formula::Constraint> {
    transform_expr_inner(expr).goal()
}

fn append_args(mut body: OutExpr, args: &[Ident], mut t: SimpleType) -> OutExpr {
    let mut variables = Vec::new();
    for arg in args {
        let (arg_ty, ret_t) = match t.kind() {
            formula::TypeKind::Arrow(x, y) => (x.clone(), y.clone()),
            _ => panic!("program error"),
        };
        let v = Variable::mk(*arg, arg_ty);
        t = ret_t;
        variables.push(v);
    }
    variables.reverse();
    for v in variables {
        body = OutExpr::mk_abs(v, body);
    }
    body
}

fn transform_clause(input: InClause, clauses: &mut Vec<OutClause>) -> OutClause {
    let body = transform_expr(&input.expr, clauses);
    let body = append_args(body, &input.args, input.id.ty.clone());
    OutClause::new(body, input.id.into())
}
