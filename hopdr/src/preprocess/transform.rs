use std::{mem::uninitialized, unimplemented};

use super::hes::{ValidityChecking, VariableS};
use crate::formula;
use crate::formula::hes;
use crate::formula::{Type as SimpleType};

type In = ValidityChecking<formula::Ident, SimpleType>;
type Out = hes::Problem;

pub fn transform(_input: In) -> Out {
    unimplemented!()
}

type InClause = super::hes::Clause<formula::Ident, SimpleType>;
type OutClause = formula::hes::Clause;
fn transform_clause(input: &InClause) -> OutClause {
    unimplemented!()
} 

type InExpr = super::hes::Expr<formula::Ident, SimpleType>;
type OutExpr = formula::hes::Goal;

enum EitherExpr {
    Const(formula::hes::Const),
    Atom(formula::hes::Atom),
    Goal(formula::hes::Goal),
    Op(formula::Op),
    Constraint(formula::Constraint)
}

impl EitherExpr {
    fn const_unwrap(self) -> formula::hes::Const {
        match self {
            EitherExpr::Const(c) => c,
            _ => panic!("failed to unwrap const")
        }
    }
    fn parse_atom(self, clauses: &mut Vec<OutClause>) -> (formula::hes::Atom, Option<(formula::Variable, formula::Constraint)>) {
        match self {
            EitherExpr::Const(c) => (formula::hes::Atom::mk_const(c), None),
            EitherExpr::Atom(a) => (a, None),
            EitherExpr::Op(o) => {
                let ty = SimpleType::mk_type_int();
                let v = formula::Variable::fresh( ty );
                let a = formula::hes::Atom::mk_var(v.id);
                let c = formula::Constraint::variable_guard(v.id, o);
                (a, Some((v, c)))
            },
            EitherExpr::Constraint(c) => {
                let fvs = c.fv();
                unimplemented!()
            }
            _ => panic!("program error")
        }
    }
    fn goal_unwrap(self) -> formula::hes::Goal {
        match self {
            EitherExpr::Goal(g) => g,
            _ => panic!("failed to unwrap EitherExpr")
        }
    }
    fn op_unwrap(self) -> formula::Op {
        match self {
            EitherExpr::Op(o) => o,
            EitherExpr::Const(c) if c.is_int() => formula::Op::mk_const(c.int()),
            _ => panic!("failed to unwrapEitherExpr")
        }
    }
    fn mk_const(c: formula::hes::Const) -> EitherExpr {
        EitherExpr::Const(c)
    }
    fn mk_atom(c: formula::hes::Atom) -> EitherExpr {
        EitherExpr::Atom(c)
    }
    fn mk_goal(c: formula::hes::Goal) -> EitherExpr {
        EitherExpr::Goal(c)
    }
    fn mk_op(x: formula::Op) -> EitherExpr {
        EitherExpr::Op(x)
    }
    fn mk_constraint(x: formula::Constraint) -> EitherExpr {
        EitherExpr::Constraint(x)
    }
}
fn transform_expr(input: &InExpr, clauses: &mut Vec<OutClause>) -> EitherExpr {
    use super::hes::ExprKind::*;
    use formula::hes::{Goal, Atom, Const};
    match input.kind() {
        Var(x) => {
            EitherExpr::Atom(Atom::mk_var(x.clone()))
        },
        App(e1, e2) => {
            let e1 = transform_expr(e1, clauses).atom_unwrap();
            let e2 = transform_expr(e2, clauses).atom_unwrap();
            EitherExpr::mk_atom(formula::hes::Atom::mk_app(e1, e2))
        },
        Num(x) => EitherExpr::mk_const(Const::mk_int(*x)),
        True => EitherExpr::mk_const(Const::mk_bool(true)),
        False => EitherExpr::mk_const(Const::mk_bool(false)),
        Op(x, y, z) => {
            let e1 = transform_expr(y, clauses).op_unwrap();
            let e2 = transform_expr(z, clauses).op_unwrap();
            EitherExpr::mk_op(formula::Op::mk_bin_op(x.clone(), e1, e2))
        }
        _ => unimplemented!()
        //True => {}
        //False => {}
        //Op(_, _, _) => {}
        //Pred(_, _, _) => {}
        //And(_, _) => {}
        //Or(_, _) => {}
        //Univ(_, _) => {}
    }
} 
