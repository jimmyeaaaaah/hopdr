use crate::ml::*;

pub(super) fn peephole_optimize<'a>(mut p: Program<'a>) -> Program<'a> {
    fn f(s: &Expr) -> Expr {
        match s.kind() {
            ExprKind::Var(_) | ExprKind::Constraint(_) | ExprKind::Raise | ExprKind::Unit => {
                s.clone()
            }
            ExprKind::Or(c1, c2) => {
                let c1 = f(c1);
                let c2 = f(c2);
                Expr::mk_or(c1, c2)
            }
            ExprKind::App(e1, e2) => match e1.kind() {
                ExprKind::Fun { ident, body } => body.subst(ident.ident, e2.clone()),
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
            ExprKind::LetRand { ident, body } => {
                let body = f(body);
                Expr::mk_letrand(ident.clone(), body)
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