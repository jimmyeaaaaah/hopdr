/// This file contains auxiliary functions for handling csisat's input and output
use crate::formula::{Constraint, ConstraintExpr, Op, OpExpr, PredKind};
use crate::parse;

use std::collections::HashMap;
// There is also an infix syntax:
//
// query   ::  formula ; formula ; ... ; formula
//
// formula :: term '=' term
//          | term '<=' term
//          | term '<' term
//          | term '>=' term
//          | term '>' term
//          | formula '->' formula
//          | formula '<->' formula
//          | formula '&' formula
//          | formula '|' formula
//          | 'not' formula
//
// term    :: variable
//          | term '+' term
//          | term '-' term
//          | number '*' term
//          | '-' term
//          | function_symbol '(' term , ... , term ')'

fn op_to_csisat(o: &Op) -> String {
    match o.kind() {
        OpExpr::Op(opkind, o1, o2) => {
            let lhs = op_to_csisat(o1);
            let rhs = op_to_csisat(o2);
            let k = opkind.to_string();
            format!("({lhs} {k} {rhs})")
        }
        OpExpr::Var(v) => v.to_string(),
        OpExpr::Const(c) => c.to_string(),
        OpExpr::Ptr(_, o) => op_to_csisat(o),
    }
}

pub(super) fn constraint_to_csisat(c: &Constraint) -> String {
    match c.kind() {
        ConstraintExpr::True => "0 = 0".to_string(),
        ConstraintExpr::False => "0 < 0".to_string(),
        ConstraintExpr::Pred(p, l) if l.len() == 2 => {
            let lhs = op_to_csisat(&l[0]);
            let rhs = op_to_csisat(&l[1]);
            if *p == PredKind::Neq {
                return format!("(not ({lhs} = {rhs}))");
            }
            let p = p.to_string();
            format!("({lhs} {p} {rhs})")
        }
        ConstraintExpr::Pred(_, _) => {
            unimplemented!("interpolation by csisat for formulas that contain a predicate that takes more than two is not supported");
        }
        ConstraintExpr::Conj(c1, c2) => {
            let lhs = constraint_to_csisat(c1);
            let rhs = constraint_to_csisat(c2);
            format!("({lhs} & {rhs})")
        }
        ConstraintExpr::Disj(c1, c2) => {
            let lhs = constraint_to_csisat(c1);
            let rhs = constraint_to_csisat(c2);
            format!("({lhs} | {rhs})")
        }
        ConstraintExpr::Quantifier(_, _, c) => constraint_to_csisat(c),
    }
}

fn parse_expression_to_constraint(e: &parse::Expr) -> Constraint {
    use crate::formula::*;
    fn expr<'a>(e: &'a parse::Expr, env: &mut HashMap<&'a str, Ident>) -> Constraint {
        match e.kind() {
            parse::ExprKind::True => Constraint::mk_true(),
            parse::ExprKind::False => Constraint::mk_false(),
            parse::ExprKind::Pred(p, left, right) => {
                let left = arith(left, env);
                let right = arith(right, env);
                Constraint::mk_pred(*p, vec![left, right])
            }
            parse::ExprKind::And(left, right) => {
                let left = expr(left, env);
                let right = expr(right, env);
                Constraint::mk_conj(left, right)
            }
            parse::ExprKind::Or(left, right) => {
                let left = expr(left, env);
                let right = expr(right, env);
                Constraint::mk_disj(left, right)
            }
            parse::ExprKind::Var(_) | parse::ExprKind::Num(_) | parse::ExprKind::Op(_, _, _) => {
                panic!("program error")
            }
            parse::ExprKind::App(_, _)
            | parse::ExprKind::Fix(_, _, _)
            | parse::ExprKind::Abs(_, _)
            | parse::ExprKind::Univ(_, _)
            | parse::ExprKind::Exist(_, _) => panic!("program error"),
        }
    }
    fn arith<'a>(e: &'a parse::Expr, env: &mut HashMap<&'a str, Ident>) -> Op {
        match e.kind() {
            parse::ExprKind::True
            | parse::ExprKind::False
            | parse::ExprKind::Pred(_, _, _)
            | parse::ExprKind::And(_, _)
            | parse::ExprKind::Or(_, _) => panic!("program error"),

            parse::ExprKind::Var(x) => match env.get(x.as_str()) {
                Some(v) => Op::mk_var(*v),
                None => {
                    let v = Ident::fresh();
                    env.insert(x, v);
                    Op::mk_var(v)
                }
            },
            parse::ExprKind::Num(v) => Op::mk_const(*v),
            parse::ExprKind::Op(o, x, y) => {
                let x = arith(x, env);
                let y = arith(y, env);
                Op::mk_bin_op(*o, x, y)
            }

            parse::ExprKind::App(_, _)
            | parse::ExprKind::Fix(_, _, _)
            | parse::ExprKind::Abs(_, _)
            | parse::ExprKind::Univ(_, _)
            | parse::ExprKind::Exist(_, _) => panic!("program error"),
        }
    }
    let mut env_map = HashMap::new();
    expr(e, &mut env_map)
}

#[test]
fn test_constraint_to_csisat() {
    use crate::formula::*;
    let x = Ident::fresh();
    let y = Ident::fresh();
    fn v(x: Ident) -> Op {
        Op::mk_var(x)
    }
    let o = Op::mk_add(v(x), v(y));
    let o2 = Op::mk_mul(v(x), Op::mk_const(2));
    let p = Constraint::mk_pred(PredKind::Geq, vec![o, o2]);
    let s = constraint_to_csisat(&p);
    assert!(s.len() > 0)
}

pub(super) fn parse(s: &str) -> Option<Constraint> {
    use nom::error::VerboseError;

    let e = parse::parse_expr::<VerboseError<&str>>(s).ok()?.1;
    Some(parse_expression_to_constraint(&e))
}

#[test]
fn parse_csisat() {
    let s = "2*x_0 <= 2";
    let c = parse(s);
    use crate::formula::*;
    match c.kind() {
        ConstraintExpr::Pred(p, l) if l.len() == 2 => {
            assert_eq!(*p, PredKind::Leq);
            assert_eq!(
                l[0],
                Op::mk_mul(Op::mk_const(2), Op::mk_var(Ident::from(0)))
            );
        }
        _ => panic!("program error"),
    }
}
