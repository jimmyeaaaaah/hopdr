use super::alpha::alpha_renaming;
use super::eta;
#[allow(unused_imports)]
use super::extravar;
use super::forall_pass;
use super::ite_expand;
use super::remove_tmp_var;
use super::reorder_conj;
use super::safety;
use super::simplify_constr_op;
use super::transform::transform;
use super::typing::typing;
use super::Context;
use crate::formula;
use crate::formula::hes;
use crate::formula::{Fv, OpKind, PredKind, Type as SimpleType};
use crate::parse;
use crate::util::Unique;

use crate::parse::NuHFLzValidityChecking;
use std::collections::HashSet;
use std::fmt;

#[derive(Debug)]
pub enum ExprKind<Id, Ty> {
    Var(Id),
    Num(i64),
    True,
    False,
    Op(OpKind, Expr<Id, Ty>, Expr<Id, Ty>),
    Pred(PredKind, Expr<Id, Ty>, Expr<Id, Ty>),
    App(Expr<Id, Ty>, Expr<Id, Ty>),
    And(Expr<Id, Ty>, Expr<Id, Ty>),
    Or(Expr<Id, Ty>, Expr<Id, Ty>),
    Abs(VariableS<Id, Ty>, Expr<Id, Ty>),
    Univ(VariableS<Id, Ty>, Expr<Id, Ty>),
}
pub type Expr<Id, Ty> = Unique<ExprKind<Id, Ty>>;

impl<Ty: fmt::Display, Id: fmt::Display> fmt::Display for Expr<Id, Ty> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            ExprKind::Var(id) => write!(f, "{}", id),
            ExprKind::Op(op, e1, e2) => write!(f, "({} {} {})", e1, op, e2),
            ExprKind::Pred(pred, e1, e2) => write!(f, "({} {} {})", e1, pred, e2),
            ExprKind::App(e1, e2) => write!(f, "({} {})", e1, e2),
            ExprKind::And(e1, e2) => write!(f, "({} & {})", e1, e2),
            ExprKind::Or(e1, e2) => write!(f, "({} | {})", e1, e2),
            ExprKind::Num(x) => write!(f, "{}", x),
            ExprKind::True => write!(f, "true"),
            ExprKind::False => write!(f, "false"),
            ExprKind::Univ(id, e) => write!(f, "∀{}. {}", id, e),
            ExprKind::Abs(x, y) => write!(f, "\\{}. {}", x, y),
        }
    }
}

impl<Id, Ty> Expr<Id, Ty> {
    pub fn mk_var(x: Id) -> Expr<Id, Ty> {
        Expr::new(ExprKind::Var(x))
    }
    pub fn mk_num(x: i64) -> Expr<Id, Ty> {
        Expr::new(ExprKind::Num(x))
    }
    pub fn mk_true() -> Expr<Id, Ty> {
        Expr::new(ExprKind::True)
    }
    pub fn mk_false() -> Expr<Id, Ty> {
        Expr::new(ExprKind::False)
    }
    pub fn mk_op(op: OpKind, e1: Expr<Id, Ty>, e2: Expr<Id, Ty>) -> Expr<Id, Ty> {
        Expr::new(ExprKind::Op(op, e1, e2))
    }
    pub fn mk_pred(pred: PredKind, e1: Expr<Id, Ty>, e2: Expr<Id, Ty>) -> Expr<Id, Ty> {
        Expr::new(ExprKind::Pred(pred, e1, e2))
    }
    pub fn mk_app(e1: Expr<Id, Ty>, e2: Expr<Id, Ty>) -> Expr<Id, Ty> {
        Expr::new(ExprKind::App(e1, e2))
    }
    pub fn mk_and(e1: Expr<Id, Ty>, e2: Expr<Id, Ty>) -> Expr<Id, Ty> {
        Expr::new(ExprKind::And(e1, e2))
    }
    pub fn mk_or(e1: Expr<Id, Ty>, e2: Expr<Id, Ty>) -> Expr<Id, Ty> {
        Expr::new(ExprKind::Or(e1, e2))
    }
    pub fn mk_univ(v: VariableS<Id, Ty>, e: Expr<Id, Ty>) -> Expr<Id, Ty> {
        Expr::new(ExprKind::Univ(v, e))
    }
    pub fn mk_abs(v: VariableS<Id, Ty>, e: Expr<Id, Ty>) -> Expr<Id, Ty> {
        Expr::new(ExprKind::Abs(v, e))
    }
}

#[derive(Clone, Debug)]
pub struct VariableS<Id, Ty> {
    pub id: Id,
    pub ty: Ty,
}
impl<Id: fmt::Display, Ty: fmt::Display> fmt::Display for VariableS<Id, Ty> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.id, self.ty)
    }
}

impl From<VariableS<formula::Ident, SimpleType>> for formula::Variable {
    fn from(v: VariableS<formula::Ident, SimpleType>) -> formula::Variable {
        formula::Variable::mk(v.id, v.ty)
    }
}

impl<Id, Ty> VariableS<Id, Ty> {
    pub fn new(id: Id, ty: Ty) -> VariableS<Id, Ty> {
        VariableS { id, ty }
    }
}

#[derive(Debug)]
pub struct Clause<Id, Ty> {
    pub id: VariableS<Id, Ty>,
    pub args: Vec<Id>,
    pub expr: Expr<Id, Ty>,
}

#[derive(Debug)]
pub struct ValidityChecking<Id, Ty> {
    pub clauses: Vec<Clause<Id, Ty>>,
    pub toplevel: Expr<Id, Ty>,
}

impl<Id: fmt::Display, Ty: fmt::Display> fmt::Display for Clause<Id, Ty> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.id)?;
        for arg in self.args.iter() {
            write!(f, " {}", arg)?;
        }
        write!(f, " = {}", self.expr)
    }
}

fn quantify_validity_checking(vc: NuHFLzValidityChecking) -> NuHFLzValidityChecking {
    fn translate_expr(
        mut expr: parse::Expr,
        preds: &HashSet<String>,
        args: &HashSet<&str>,
    ) -> parse::Expr {
        let fvs = expr.fv();
        for fv in fvs.iter() {
            if !preds.contains(fv) && !args.contains(fv.as_str()) {
                expr = parse::Expr::mk_univ(fv.clone(), expr);
            }
        }
        expr
    }
    let preds: HashSet<String> = vc.formulas.iter().map(|x| x.id.clone()).collect();
    let toplevel = translate_expr(vc.toplevel, &preds, &HashSet::new());

    let mut formulas = Vec::new();
    for clause in vc.formulas {
        let parse::Clause {
            expr,
            id,
            args,
            fixpoint,
        } = clause;
        let arg_set = args.iter().map(|s| s.as_str()).collect();
        let expr = translate_expr(expr, &preds, &arg_set);
        formulas.push(parse::Clause {
            expr,
            id,
            args,
            fixpoint,
        });
    }
    NuHFLzValidityChecking { formulas, toplevel }
}

pub fn preprocess_for_typed_problem(
    problem: hes::Problem<formula::Constraint>,
) -> hes::Problem<formula::Constraint> {
    debug!("[problem]\n{}\n", problem);
    let problem = safety::transform(problem);
    debug!("[safety::transform]\n{}\n", problem);
    let problem = eta::transform(problem);
    let problem = forall_pass::transform(problem);
    let problem = reorder_conj::transform(problem);
    let problem = simplify_constr_op::transform(problem);
    let problem = ite_expand::transform(problem);
    let problem = remove_tmp_var::transform(problem);
    problem
}

pub fn preprocess(vc: parse::Problem) -> (hes::Problem<formula::Constraint>, Context) {
    match vc {
        parse::Problem::NuHFLZValidityChecking(vc) => {
            let vc = quantify_validity_checking(vc);
            let problem = typing(vc.formulas, vc.toplevel);
            let (problem, ctx) = alpha_renaming(problem);
            // let problem = extravar::transform(problem);
            let problem = transform(problem);
            let problem = preprocess_for_typed_problem(problem);
            (problem, ctx)
        }
    }
}
