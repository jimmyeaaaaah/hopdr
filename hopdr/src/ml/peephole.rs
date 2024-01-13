use crate::ml::*;

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
                let cond = cond.clone();
                let then = f(then);
                let els = f(els);
                Expr::mk_if(cond, then, els)
            }
            ExprKind::LetRand { ident, range, body } => {
                let body = f(body);
                Expr::mk_letrand(ident.clone(), range.clone(), body)
            }
            ExprKind::TryWith { body, handler } => {
                let body = f(body);
                let handler = f(handler);
                Expr::mk_try_with(body, handler)
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
                if idents.len() == 0 && matches!(cont.kind(), ExprKind::Unit) {
                    body
                } else {
                    Expr::mk_let_tuple(idents.clone(), body, cont)
                }
            }
        }
    }
    p.functions = p
        .functions
        .into_iter()
        .map(|func| Function {
            body: f(&func.body),
            ..func
        })
        .collect();
    p.main = f(&p.main);
    p
}
