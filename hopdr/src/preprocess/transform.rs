

use super::hes::{ValidityChecking};
use crate::formula;
use crate::formula::hes;
use crate::formula::{Fv, Type as SimpleType, Variable, Ident, Subst};

type In = ValidityChecking<formula::Ident, SimpleType>;
type Out = hes::Problem;

pub fn transform(input: In) -> Out {
    let mut clauses = Vec::new();

    for clause in input.clauses {
        let c = transform_clause(clause, &mut clauses);
        clauses.push(c);
    }
    let top = transform_expr(&input.toplevel, &mut clauses);
    Out{ clauses, top }
}

type InClause = super::hes::Clause<formula::Ident, SimpleType>;
type OutClause = formula::hes::Clause;

type InExpr = super::hes::Expr<formula::Ident, SimpleType>;
type OutExpr = formula::hes::Goal;

#[derive(Debug)]
enum EitherExpr {
    Var(formula::Ident),
    Const(formula::hes::Const),
    Op(formula::Op),
    Atom(formula::hes::Atom),
    Goal(formula::hes::Goal),
    Constraint(formula::Constraint)
}

impl EitherExpr {
    fn const_unwrap(self) -> formula::hes::Const {
        match self {
            EitherExpr::Const(c) => c,
            _ => panic!("failed to unwrap const")
        }
    }
    fn parse_atom(self, clauses: &mut Vec<OutClause>, constraints: &mut (Vec<formula::Variable>, Vec<formula::Constraint>)) 
        -> formula::hes::Atom {
        match self {
            EitherExpr::Const(c) => {
                match c.kind() {
                    formula::hes::ConstKind::Int(v) => {
                        EitherExpr::mk_op(formula::Op::mk_const(*v)).parse_atom(clauses, constraints)
                    }
                }
            },
            EitherExpr::Var(v) => formula::hes::Atom::mk_var(v),
            EitherExpr::Atom(a) => a,
            EitherExpr::Op(o) => {
                let ty = SimpleType::mk_type_int();
                let v = formula::Variable::fresh( ty );
                let a = formula::hes::Atom::mk_var(v.id);
                let c = formula::Constraint::variable_guard(v.id, o);
                constraints.0.push(v);
                constraints.1.push(c);
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
            EitherExpr::Constraint(c) => formula::hes::Goal::mk_constr(c),
            _ => panic!("failed to unwrap EitherExpr")
        }
    }
    fn op_unwrap(self) -> formula::Op {
        match self {
            EitherExpr::Op(o) => o,
            EitherExpr::Const(c) if c.is_int() => formula::Op::mk_const(c.int()),
            EitherExpr::Var(v) => formula::Op::mk_var(v),
            _ => panic!("failed to unwrapEitherExpr: {:?}", self)
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
fn transform_expr_inner(input: &InExpr, clauses: &mut Vec<OutClause>, constraints: &mut (Vec<formula::Variable>, Vec<formula::Constraint>)) -> EitherExpr {
    use super::hes::ExprKind::*;
    use formula;
    use formula::Top;
    use formula::hes::{Goal, Atom, Const};
    match input.kind() {
        Var(x) => {
            EitherExpr::Var(x.clone())
        },
        App(e1, e2) => {
            let e1 = transform_expr_inner(e1, clauses, constraints).parse_atom(clauses, constraints);
            let e2 = transform_expr_inner(e2, clauses, constraints).parse_atom(clauses, constraints);
            EitherExpr::mk_atom(formula::hes::Atom::mk_app(e1, e2))
        },
        Num(x) => EitherExpr::mk_const(Const::mk_int(*x)),
        True => EitherExpr::mk_constraint(formula::Constraint::mk_true()),
        False => EitherExpr::mk_constraint(formula::Constraint::mk_false()),
        Op(x, y, z) => {
            let e1 = transform_expr_inner(y, clauses, constraints).op_unwrap();
            let e2 = transform_expr_inner(z, clauses, constraints).op_unwrap();
            EitherExpr::mk_op(formula::Op::mk_bin_op(x.clone(), e1, e2))
        },
        Pred(p, x, y) => {
            let x = transform_expr_inner(x, clauses, constraints).op_unwrap();
            let y = transform_expr_inner(y, clauses, constraints).op_unwrap();
            EitherExpr::mk_constraint(formula::Constraint::mk_pred(p.clone(), vec![x, y]))
        },
        And(x, y) => {
            let x = transform_expr_inner(x, clauses, constraints).goal_unwrap();
            let y = transform_expr_inner(y, clauses, constraints).goal_unwrap();
            EitherExpr::mk_goal(Goal::mk_conj(x, y))
        },
        Or(x, y) => {
            let x = transform_expr_inner(x, clauses, constraints).goal_unwrap();
            let y = transform_expr_inner(y, clauses, constraints).goal_unwrap();
            EitherExpr::mk_goal(Goal::mk_disj(x, y))
        },
        Univ(x, y) => {
            let y = transform_expr_inner(y, clauses, constraints).goal_unwrap();
            EitherExpr::mk_goal(Goal::mk_univ(x.clone().into(), y))
        }
    }
} 

fn transform_expr(expr: &InExpr, clauses: &mut Vec<OutClause>) -> formula::hes::Goal {
    use formula::{Constraint, Top, Conjunctive};
    use formula::hes::Goal;
    let mut constraints = (Vec::new(), Vec::new());
    let g = transform_expr_inner(&expr, clauses, &mut constraints).goal_unwrap();
    
    let mut c = Constraint::mk_true();
    let (vs, cs) = constraints;
    for expr in cs {
        c = Constraint::mk_conj(expr, c);
    }
    let mut g = Goal::mk_disj(Goal::mk_constr(c.negate().unwrap()), g);
    for v in vs {
        g = Goal::mk_univ(v, g);
    }
    g
}

fn transform_clause(input: InClause, clauses: &mut Vec<OutClause>) -> OutClause {
    let body = transform_expr(&input.expr, clauses);
    OutClause::new(body, input.id.into(), input.args)
} 