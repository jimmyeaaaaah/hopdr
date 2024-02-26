use crate::formula::{Constraint, Logic};
use crate::ml::*;

const OPTIMIZE_LIMIT: u64 = 1000;

fn handle_try_with<'a>(body: Expr, handler: Expr) -> Expr {
    match body.is_check_constraint() {
        Some(c) => Expr::mk_if(Expr::mk_constraint(c), handler, Expr::mk_unit()),
        None => Expr::mk_try_with(body, handler),
    }
}

fn handle_if(cond: Expr, then: Expr, els: Expr) -> Expr {
    // case if c1 then (if c2 then raise else ()) else ()
    match (cond.kind(), then.is_check_constraint(), els.kind()) {
        (ExprKind::Constraint(c), Some(c2), ExprKind::Unit) => Expr::mk_if(
            Expr::mk_constraint(Constraint::mk_conj(c.clone(), c2.clone())),
            Expr::mk_raise(),
            Expr::mk_unit(),
        ),
        _ => Expr::mk_if(cond, then, els),
    }
}

pub(super) fn peephole_optimize<'a>(mut p: Program<'a>) -> Program<'a> {
    fn f(s: &Expr) -> Expr {
        match s.kind() {
            ExprKind::Var(_)
            | ExprKind::Constraint(_)
            | ExprKind::Raise
            | ExprKind::Unit
            | ExprKind::Op(_) => s.clone(),
            ExprKind::Or(c1, c2) => {
                let c1 = f(c1);
                let c2 = f(c2);
                Expr::mk_or(c1, c2)
            }
            ExprKind::And(c1, c2) => {
                let c1 = f(c1);
                let c2 = f(c2);
                Expr::mk_and(c1, c2)
            }
            ExprKind::App(e1, e2) => match e1.kind() {
                ExprKind::Fun { ident, body } => f(body).subst(ident.ident, e2.clone()),
                _ => {
                    let e1 = f(e1);
                    let e2 = f(e2);
                    Expr::mk_app(e1, e2)
                }
            },
            ExprKind::IApp(e1, o) => match e1.kind() {
                ExprKind::Fun { ident, body } => body.isubst(ident.ident, o.clone()),
                _ => {
                    let e1 = f(e1);
                    Expr::mk_iapp(e1, o.clone())
                }
            },
            ExprKind::Fun { ident, body } => {
                let body = f(body);
                Expr::mk_fun(ident.clone(), body)
            }
            ExprKind::If { cond, then, els } => {
                let cond = f(cond);
                let then = f(then);
                let els = f(els);
                handle_if(cond, then, els)
            }
            ExprKind::LetRand { ident, range, body } => {
                let body = f(body);
                Expr::mk_letrand(ident.clone(), range.clone(), body)
            }
            ExprKind::TryWith { body, handler } => {
                let body = f(body);
                let handler = f(handler);
                handle_try_with(body, handler)
            }
            ExprKind::Assert(e) => {
                let e = f(e);
                Expr::mk_assert(e)
            }
            ExprKind::Sequential { lhs, rhs } => {
                let lhs = f(lhs);
                let rhs = f(rhs);
                Expr::mk_sequential(lhs, rhs)
            }
            ExprKind::Tuple(args) => {
                let args = args.iter().map(f).collect();
                Expr::mk_tuple(args)
            }
            ExprKind::LetTuple { idents, body, cont } => {
                let body = f(body);
                let cont = f(cont);
                // the follwing call of pred is not a tail recursion.
                //    let () = pred(x, y, z) in ()
                // we transform this to pred(x, y, z) so that we can reduce the
                // possibility of stack-overflow, and also optimize the memory-usage.
                if idents.len() == 0 {
                    if matches!(cont.kind(), ExprKind::Unit) {
                        body
                    } else {
                        Expr::mk_sequential(body, cont)
                    }
                } else {
                    Expr::mk_let_tuple(idents.clone(), body, cont)
                }
            }
        }
    }

    // simplify constraints
    fn simplify_constraints(e: &Expr) -> Expr {
        match e.kind() {
            ExprKind::Var(_) | ExprKind::Raise | ExprKind::Unit => e.clone(),
            ExprKind::Constraint(c) => Expr::mk_constraint(c.simplify()),
            ExprKind::Or(e1, e2) => Expr::mk_or(simplify_constraints(e1), simplify_constraints(e2)),
            ExprKind::And(e1, e2) => {
                Expr::mk_and(simplify_constraints(e1), simplify_constraints(e2))
            }
            ExprKind::App(e1, e2) => {
                Expr::mk_app(simplify_constraints(e1), simplify_constraints(e2))
            }
            ExprKind::IApp(e1, e2) => Expr::mk_iapp(simplify_constraints(e1), e2.simplify()),
            ExprKind::Fun { ident, body } => {
                Expr::mk_fun(ident.clone(), simplify_constraints(body))
            }
            ExprKind::Op(o) => Expr::mk_op(o.simplify()),
            ExprKind::If { cond, then, els } => Expr::mk_if(
                simplify_constraints(cond),
                simplify_constraints(then),
                simplify_constraints(els),
            ),
            ExprKind::LetRand { ident, range, body } => {
                Expr::mk_letrand(ident.clone(), range.clone(), simplify_constraints(body))
            }
            ExprKind::TryWith { body, handler } => {
                Expr::mk_try_with(simplify_constraints(body), simplify_constraints(handler))
            }
            ExprKind::Assert(e) => Expr::mk_assert(simplify_constraints(e)),
            ExprKind::Sequential { lhs, rhs } => {
                Expr::mk_sequential(simplify_constraints(lhs), simplify_constraints(rhs))
            }
            ExprKind::Tuple(args) => {
                let args = args.iter().map(simplify_constraints).collect();
                Expr::mk_tuple(args)
            }
            ExprKind::LetTuple { idents, body, cont } => Expr::mk_let_tuple(
                idents.clone(),
                simplify_constraints(body),
                simplify_constraints(cont),
            ),
        }
    }
    fn translate_expr(e: &Expr) -> Expr {
        let mut e = simplify_constraints(e);
        for _ in 0..OPTIMIZE_LIMIT {
            let e2 = f(&e);
            if e == e2 {
                return e;
            }
            e = e2;
        }
        e
    }
    p.functions = p
        .functions
        .into_iter()
        .map(|func| Function {
            body: translate_expr(&func.body),
            ..func
        })
        .collect();
    p.main = f(&p.main);
    p
}
