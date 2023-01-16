use tempfile::NamedTempFile;

use std::collections::{HashMap, HashSet};
use std::time::Duration;

use super::smt::{constraint_to_smt2_inner, encode_ident, z3_solver};
use super::util;
use super::{Model, SMTSolverType, SolverResult};
use crate::formula::{
    AlphaEquivalence, Constraint, ConstraintExpr, FirstOrderLogic, Fv, Ident, Logic, Op, OpExpr,
    OpKind, PredKind, QuantifierKind, Subst, Top,
};
use lexpr;
use lexpr::Value;

pub struct QESolver {}

pub fn qe_solver(ty: SMTSolverType) -> QESolver {
    match ty {
        SMTSolverType::Z3 | SMTSolverType::Auto => QESolver {},
        SMTSolverType::CVC => unimplemented!(),
    }
}

fn parse_variable(v: &str) -> Ident {
    assert!(v.starts_with('x'));
    Ident::from_str(&v[1..]).unwrap_or_else(|| panic!("parse fail"))
}

fn parse_opkind(v: &Value) -> OpKind {
    let x = v
        .as_symbol()
        .unwrap_or_else(|| panic!("parse error: {:?}", v));
    match x {
        "+" => OpKind::Add,
        "-" => OpKind::Sub,
        "*" => OpKind::Mul,
        _ => panic!("failed to handle operator: {}", x),
    }
}

fn parse_op(v: &Value) -> Op {
    match v {
        Value::Number(n) => Op::mk_const(n.as_i64().unwrap()),
        Value::Symbol(x) => Op::mk_var(parse_variable(x)),
        Value::Cons(cons) => {
            let car = cons.car();
            let opkind = parse_opkind(car);
            let args: Vec<_> = cons
                .cdr()
                .as_cons()
                .unwrap_or_else(|| panic!("parse error: {:?}", v))
                .iter()
                .map(|v| parse_op(v.car()))
                .collect();
            // TODO: args.len() > 3
            assert_eq!(args.len(), 2);
            Op::mk_bin_op(opkind, args[0].clone(), args[1].clone())
        }
        Value::Nil
        | Value::Null
        | Value::Bool(_)
        | Value::Char(_)
        | Value::String(_)
        | Value::Keyword(_)
        | Value::Bytes(_)
        | Value::Vector(_) => panic!("parse error"),
    }
}

#[test]
fn test_parse_op() {
    let s = "(+ x_x1 1)";
    let x = Ident::fresh();
    let o1 = Op::mk_add(Op::mk_var(x), Op::mk_const(1));
    let o2 = parse_op(&lexpr::from_str(s).unwrap());
    assert!(o1.alpha_equiv(&o2));

    let s = "(- x_x2 (+ x_x1 1))";
    let x1 = Ident::fresh();
    let x2 = Ident::fresh();
    let o1 = Op::mk_add(Op::mk_var(x1), Op::mk_const(1));
    let o1 = Op::mk_sub(Op::mk_var(x2), o1);
    let o2 = parse_op(&lexpr::from_str(s).unwrap());
    assert!(o1.alpha_equiv(&o2));
}

fn parse_constraint(v: &Value) -> Constraint {
    println!("parse_constraint: {v:?}");
    unimplemented!()
}

#[test]
fn test_parse_constraint() {
    let s = "(= x_x1 0)";
    let x = lexpr::from_str(s).unwrap();
    let c = parse_constraint(&x);
    let x = Ident::fresh();
    let c2 = Constraint::mk_eq(Op::mk_var(x), Op::mk_const(0));
}

impl QESolver {
    fn to_smt(&self, formula: &Constraint) -> String {
        let fvs = formula.fv();
        let declare_funs = fvs
            .iter()
            .map(|ident| format!("(declare-fun {} () Int)", encode_ident(ident)))
            .collect::<Vec<_>>()
            .join("\n");
        let c_str = constraint_to_smt2_inner(formula, SMTSolverType::Z3);

        format!(
            "{}\n (assert {})\n (apply (using-params qe))\n",
            declare_funs, c_str
        )
    }
    fn parse(&self, s: &str) -> Result<Constraint, lexpr::parse::Error> {
        let x = lexpr::from_str(s)?;
        let data = x.as_cons().unwrap().cdr().as_cons().unwrap().car();
        let cs: Vec<_> = match data {
            Value::Cons(x) => x
                .clone()
                .iter()
                .map(|x| x.car())
                .filter(|x| !x.is_symbol())
                .map(|v| parse_constraint(&v))
                .collect(),
            _ => panic!("parse error: qe smt2 formula {} ({:?})", s, x),
        };
        for c in cs {
            println!("{c:?}");
        }
        unimplemented!()
    }
    pub fn default_solver() -> QESolver {
        qe_solver(SMTSolverType::Z3)
    }
    pub fn solve(&self, formula: &Constraint) -> Constraint {
        let smt_string = self.to_smt(formula);
        let result = z3_solver(smt_string);
        self.parse(&result)
            .expect(&format!("qe result parse failed: {result}"))
    }
}

#[test]
fn test_z3_qe_result() {
    let s = "(goals
(goal
  (= x_x1 0)
  (>= x_x2 1)
  :precision precise :depth 1)
)";
    let z3_solver = qe_solver(SMTSolverType::Z3);
    let c = z3_solver.parse(s).unwrap();

    let x1 = Ident::fresh();
    let x2 = Ident::fresh();
    let c1 = Constraint::mk_eq(Op::mk_var(x1), Op::mk_const(0));
    let c2 = Constraint::mk_geq(Op::mk_var(x2), Op::mk_const(1));
    let c3 = Constraint::mk_conj(c1, c2);
    assert!(c.alpha_equiv(&c3));
}
