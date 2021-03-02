use std::{mem::uninitialized, unimplemented};

use super::hes::{ValidityChecking};
use crate::formula;
use crate::formula::hes;
use crate::formula::{Fv, Type as SimpleType, Variable, Ident, Subst};

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
    fn parse_atom(self, clauses: &mut Vec<OutClause>, constraints: &mut Vec<(formula::Variable, formula::Constraint)>) 
        -> formula::hes::Atom {
        match self {
            EitherExpr::Const(c) => formula::hes::Atom::mk_const(c),
            EitherExpr::Atom(a) => a,
            EitherExpr::Op(o) => {
                let ty = SimpleType::mk_type_int();
                let v = formula::Variable::fresh( ty );
                let a = formula::hes::Atom::mk_var(v.id);
                let c = formula::Constraint::variable_guard(v.id, o);
                constraints.push((v, c));
                a
            },
            EitherExpr::Constraint(c) => {
                let fvs = c.fv();
                let mut args = Vec::new();
                // generate fresh names for alpha-renaming
                let mut body_c = c;
                for fv in fvs.iter() {
                    let id = Ident::fresh();
                    body_c = body_c.rename_variable(fv, &id);
                    args.push(id);
                }
                // these fvs must have type int.
                let ti = SimpleType::mk_type_int();
                let mut ret_t = SimpleType::mk_type_prop();
                for _ in args.iter() {
                    ret_t = SimpleType::mk_type_arrow(ti.clone(), ret_t);
                }
                let head_id = Ident::fresh();
                let head = Variable::mk(head_id.clone(), ret_t);
                let body = hes::Goal::mk_constr(body_c);
                let clause = hes::Clause::new(body, head, args);
                clauses.push(clause);

                let mut atom = hes::Atom::mk_var(head_id);
                for fv in fvs {
                    let v = hes::Atom::mk_var(fv);
                    atom = hes::Atom::mk_app(atom, v);
                }
                atom 
            }
            _ => panic!("program error")
        }
    }
    fn goal_unwrap(self) -> formula::hes::Goal {
        match self {
            EitherExpr::Goal(g) => g,
            EitherExpr::Atom(a) => formula::hes::Goal::mk_atom(a),
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
fn transform_expr(input: &InExpr, clauses: &mut Vec<OutClause>, constraints: &mut Vec<(formula::Variable, formula::Constraint)>) -> EitherExpr {
    use super::hes::ExprKind::*;
    use formula;
    use formula::Top;
    use formula::hes::{Goal, Atom, Const};
    match input.kind() {
        Var(x) => {
            EitherExpr::Atom(Atom::mk_var(x.clone()))
        },
        App(e1, e2) => {
            let e1 = transform_expr(e1, clauses, constraints).parse_atom(clauses, constraints);
            let e2 = transform_expr(e2, clauses, constraints).parse_atom(clauses, constraints);
            EitherExpr::mk_atom(formula::hes::Atom::mk_app(e1, e2))
        },
        Num(x) => EitherExpr::mk_const(Const::mk_int(*x)),
        True => EitherExpr::mk_constraint(formula::Constraint::mk_true()),
        False => EitherExpr::mk_constraint(formula::Constraint::mk_false()),
        Op(x, y, z) => {
            let e1 = transform_expr(y, clauses, constraints).op_unwrap();
            let e2 = transform_expr(z, clauses, constraints).op_unwrap();
            EitherExpr::mk_op(formula::Op::mk_bin_op(x.clone(), e1, e2))
        },
        Pred(p, x, y) => {
            let x = transform_expr(x, clauses, constraints).op_unwrap();
            let y = transform_expr(y, clauses, constraints).op_unwrap();
            EitherExpr::mk_constraint(formula::Constraint::mk_pred(p.clone(), vec![x, y]))
        },
        And(x, y) => {
            let x = transform_expr(x, clauses, constraints).goal_unwrap();
            let y = transform_expr(y, clauses, constraints).goal_unwrap();
            EitherExpr::mk_goal(Goal::mk_conj(x, y))
        },
        Or(x, y) => {
            let x = transform_expr(x, clauses, constraints).goal_unwrap();
            let y = transform_expr(y, clauses, constraints).goal_unwrap();
            EitherExpr::mk_goal(Goal::mk_disj(x, y))
        },
        Univ(x, y) => {
            let y = transform_expr(y, clauses, constraints).goal_unwrap();
            EitherExpr::mk_goal(Goal::mk_univ(x.clone().into(), y))
        }
    }
} 
