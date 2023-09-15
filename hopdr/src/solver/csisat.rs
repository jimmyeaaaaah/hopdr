/// This file contains auxiliary functions for handling csisat's input and output
use crate::formula::{Constraint, ConstraintExpr, Op, OpExpr};

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

fn constraint_to_csisat(c: &Constraint) -> String {
    match c.kind() {
        ConstraintExpr::True => "0 = 0".to_string(),
        ConstraintExpr::False => "0 != 0".to_string(),
        ConstraintExpr::Pred(p, l) if l.len() == 2 => {
            let lhs = op_to_csisat(&l[0]);
            let rhs = op_to_csisat(&l[1]);
            let p = p.to_string();
            format!("({lhs} {p} {rhs}")
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
