use tempfile::{tempfile, NamedTempFile};

use std::{fs::File, time::Duration};

use crate::formula::{Constraint, ConstraintExpr, Op, OpExpr, OpKind, PredKind, Ident, Fv};
use super::util;

pub enum SMTResult {
    Sat,
    Unsat,
    Unknown,
    Timeout
}

#[derive(Copy, Clone)]
pub enum SMT2Style {
    Z3,
}

fn pred_to_smt2(p: &PredKind, args: &[String]) -> String {
    let args = args.join(" ");
    match p {
        PredKind::Eq => format!("(= {})", args),
        PredKind::Neq => format!("(not (= {}))", args),
        PredKind::Leq => format!("(<= {})", args),
        PredKind::Gt => format!("(> {})", args)
    }
}

fn opkind_2_smt2(o: &OpKind) -> &'static str {
    match o {
        OpKind::Add => "+",
        OpKind::Sub => "-",
        OpKind::Mul => "*",
        OpKind::Div => "/",
        OpKind::Mod => "%",
    }
}

fn ident_2_smt2(ident: &Ident) -> String {
    format!("x_{}", ident)
}

fn op_to_smt2(op: &Op) -> String {
    match op.kind() {
        OpExpr::Op(opkind, o1, o2) => {
            let o1 = op_to_smt2(o1);
            let o2 = op_to_smt2(o2);
            let k = opkind_2_smt2(opkind);
            format!("({} {} {})", k, o1, o2)
        }
        OpExpr::Var(x) => ident_2_smt2(x),
        OpExpr::Const(c) => format!("{}", c),
    }
}

fn constraint_to_smt2_inner(c: &Constraint, style: SMT2Style) -> String {
    let f = constraint_to_smt2_inner;
    match c.kind() {
        ConstraintExpr::True => {"true".to_string()},
        ConstraintExpr::False => {"false".to_string()}
        ConstraintExpr::Pred(p, l) => {
            let args = l.iter().map(|op| op_to_smt2(op)).collect::<Vec<_>>();
            pred_to_smt2(p, &args)
        },
        ConstraintExpr::Conj(c1, c2) => 
            format!("(and {} {})", f(c1, style), f(c2, style)),
        ConstraintExpr::Disj(c1, c2) => 
            format!("(or {} {})", f(c1, style), f(c2, style)),
        ConstraintExpr::Univ(x, c) => 
            format!("(forall (({} Int)) {})", ident_2_smt2(&x.id), f(c, style))
    }
}

fn constraint_to_smt2(c: &Constraint, style: SMT2Style) -> String {
    let fvs = c.fv();
    let c_s = constraint_to_smt2_inner(c, style);
    let c_s = 
    if fvs.len() > 0 {
        // (forall ((%s Int)) %s)
        let decls = fvs.into_iter().map(|ident| {
            format!("({} Int)", ident_2_smt2(&ident))
        }).collect::<Vec<_>>().join("");
        format!("(forall ({}) {})", decls, c_s)
    } else {
        c_s
    };
    format!("(assert {})\n(check-sat)\n", c_s)
}

fn save_smt2(smt_string: String) -> NamedTempFile {
    util::save_to_file(smt_string)
}

fn z3_solver(smt_string: String) -> SMTResult {
    let f = save_smt2(smt_string);
    let args = vec![f.path().to_str().unwrap()];
    let out = util::exec_with_timeout("z3", &args, Duration::from_secs(1));
    let s = std::str::from_utf8(&out).unwrap();
    if s.starts_with("sat") {
        SMTResult::Sat
    } else if s.starts_with("unsat") {
        SMTResult::Unsat
    } else {
        SMTResult::Unknown
    }
}

pub fn smt_solve(c: &Constraint) -> SMTResult {
    let smt2 = constraint_to_smt2(c, SMT2Style::Z3);
    z3_solver(smt2)
}