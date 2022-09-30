use std::collections::HashMap;

use crate::formula::OpKind;

/// Given a linear integer arithmetic Constraint,
/// returns
///
///
use super::{Constraint, Fv, Ident, Logic, Negation, Op, PredKind, Top};

/// transform all the predicates to another constraint that only use `<`.
fn transform_predicate(c: &Constraint) -> Constraint {
    fn inner(p: PredKind, l: &Vec<Op>) -> Constraint {
        assert_eq!(l.len(), 2);
        let x = l[0].clone();
        let y = l[1].clone();
        fn lt(x: Op, y: Op) -> Constraint {
            Constraint::mk_bin_pred(PredKind::Lt, x, y)
        }
        fn inc(x: Op) -> Op {
            Op::mk_add(x, Op::mk_const(1))
        }
        match p {
            PredKind::Eq => {
                /*
                (assert (forall ((x Int) (y Int))
                        (and
                            (implies (= x y) (and (< y (+ 1 x)) (< x (+ 1 y))))
                            (implies (and (< y (+ 1 x)) (< x (+ 1 y)))  (= x y))
                        )
                ))
                (check-sat)
                 */
                let p1 = lt(y.clone(), inc(x.clone()));
                let p2 = lt(x, inc(y));
                Constraint::mk_conj(p1, p2)
            }
            PredKind::Neq => {
                // x != y <=> x < y \/ y < x
                let p1 = lt(x.clone(), y.clone());
                let p2 = lt(y, x);
                Constraint::mk_disj(p1, p2)
            }
            PredKind::Gt => lt(y, x),
            // x >= y  <=> x + 1 > y <=> y < x + 1
            PredKind::Geq => lt(y, inc(x)),
            PredKind::Lt => lt(x, y),
            // x <= y  <=> x < y + 1
            PredKind::Leq => lt(x, inc(y)),
        }
    }

    match c.kind() {
        crate::formula::ConstraintExpr::True | crate::formula::ConstraintExpr::False => c.clone(),
        crate::formula::ConstraintExpr::Pred(p, l) => inner(*p, l),
        crate::formula::ConstraintExpr::Conj(x, y) => {
            let x = transform_predicate(x);
            let y = transform_predicate(y);
            Constraint::mk_conj(x, y)
        }
        crate::formula::ConstraintExpr::Disj(x, y) => {
            let x = transform_predicate(x);
            let y = transform_predicate(y);
            Constraint::mk_disj(x, y)
        }
        crate::formula::ConstraintExpr::Quantifier(q, x, c) => {
            let c = transform_predicate(c);
            Constraint::mk_quantifier(*q, x.clone(), c)
        }
    }
}

// Pred(PredKind::Geq, x, y)
// 1. x - y >= 0
// 2. expand all the mult (add)
// 2. o1 + o2 + ...
// 3. expand all the expression like (o1 + o2) * x1
fn pred_to_vec(constr: &Constraint, m: &HashMap<Ident, usize>) -> Vec<Op> {
    debug!("pred_to_vec: {constr}");
    // Assumption: o only contains operation muls (if other ops exist, then it panics)
    // if o contains multiple variables in m, then returns None
    // otherwise, returns coefficient of the variable, and variable name if exists
    // for a constrant, the results should have a pair (o, None)
    fn parse_mult(o: &Op, m: &HashMap<Ident, usize>) -> Option<(Op, Option<Ident>)> {
        match o.kind() {
            crate::formula::OpExpr::Op(OpKind::Mul, o1, o2) => {
                let (coef1, v1) = parse_mult(o1, m)?;
                let (coef2, v2) = parse_mult(o2, m)?;
                match (v1, v2) {
                    (Some(_), Some(_)) => None,
                    (Some(v), None) | (None, Some(v)) => Some((Op::mk_mul(coef1, coef2), Some(v))),
                    (None, None) => Some((Op::mk_mul(coef1, coef2), None)),
                }
            }
            crate::formula::OpExpr::Var(v) if m.contains_key(v) => {
                Some((Op::mk_const(1), Some(*v)))
            }
            crate::formula::OpExpr::Var(_) | crate::formula::OpExpr::Const(_) => {
                Some((o.clone(), None))
            }
            crate::formula::OpExpr::Ptr(_, o) => parse_mult(o, m),
            crate::formula::OpExpr::Op(_, _, _) => panic!("program error"),
        }
    }
    // assumption v.len() == m.len() + 1
    // v's m[id]-th element is the coefficient for the variable `id`
    // v's m.len()-th element is the constant
    let mut result_vec = vec![Op::mk_const(0); m.len() + 1];
    let additions = match constr.kind() {
        super::ConstraintExpr::True => Vec::new(),
        super::ConstraintExpr::Pred(PredKind::Geq, l) if l.len() == 2 => {
            let x = l[0].clone();
            let y = l[1].clone();
            let z = Op::mk_bin_op(super::OpKind::Sub, x, y);
            z.expand_expr_to_vec()
        }
        super::ConstraintExpr::False => {
            // 0 >= 1
            let o = Op::mk_const(-1);
            o.expand_expr_to_vec()
        }
        super::ConstraintExpr::Pred(_, _)
        | super::ConstraintExpr::Conj(_, _)
        | super::ConstraintExpr::Disj(_, _)
        | super::ConstraintExpr::Quantifier(_, _, _) => panic!("program error: {}", constr),
    };
    let constant_index = m.len();
    for addition in additions {
        let (coef, v) = parse_mult(&addition, m).expect(&format!(
            "there is non-linear exprresion, which is note supported: {addition}\ngenerated from {constr}"
        ));
        let id = v.map_or(constant_index, |v| *m.get(&v).unwrap());
        result_vec[id] = Op::mk_add(result_vec[id].clone(), coef);
    }
    result_vec
}

/// returns a constraint that does not contain universal quantifiers
/// ### Assumption:
/// - c's free variables are considered to be bound by existential quantifiers
/// - c only contains universal quantifiers
/// - c only contains linear constraints
pub fn farkas_transform(c: &Constraint) -> Constraint {
    // translates the constraint to ∧ θᵢ where θᵢ has the form ¬ (∧ eᵢ ≥ 0).
    // Note that eᵢ is a linear expression.
    debug!("farkas input: {c}");

    // 1. prenex normal form of c
    let mut fv = c.fv();
    let (v, c2) = c.prenex_normal_form_raw(&mut fv);
    let mut univ_vars = HashMap::new();
    // now c2 is a quantifier free formula
    for (idx, (q, var)) in v.iter().enumerate() {
        assert_eq!(*q, super::QuantifierKind::Universal);
        assert!(var.ty.is_int());
        univ_vars.insert(var.id, idx);
    }
    // first replace all the predicates except for >= by constraints that only contain < (which will be negated below, so that will produce
    // <=s)
    let c2 = transform_predicate(&c2);
    debug!("transformed: {c2}");
    debug!("univ_vars: ");
    for (v, _) in univ_vars.iter() {
        debug!("- {v}");
    }

    // cnf = [θᵢ]
    let cnf = c2.to_cnf();

    // we transform cnf's element so that it has the form  ¬ (∧ eᵢ ≥ 0).
    let result_constraint = cnf
        .into_iter()
        .map(|clause| {
            let dnf = clause.to_dnf();
            // check if it is trivial or not
            let matrix: Vec<_> = dnf
                .into_iter()
                .map(|atom| pred_to_vec(&atom.negate().unwrap(), &univ_vars))
                .collect();
            let coefs: Vec<_> = (0..matrix.len()).map(|_| Ident::fresh()).collect();
            let mut result_constraint = Constraint::mk_true();
            for i in 0..univ_vars.len() {
                let mut o = Op::mk_const(0);
                for (j, vec) in matrix.iter().enumerate() {
                    o = Op::mk_add(Op::mk_mul(vec[i].clone(), Op::mk_var(coefs[j])), o);
                }
                let c = Constraint::mk_eq(o, Op::mk_const(0));
                result_constraint = Constraint::mk_conj(c, result_constraint);
            }
            // for constant part
            let constant_ident = Ident::fresh();
            let mut o = Op::mk_var(constant_ident); // r0
            let i = univ_vars.len(); // constant index
            for (j, vec) in matrix.iter().enumerate() {
                o = Op::mk_add(Op::mk_mul(vec[i].clone(), Op::mk_var(coefs[j])), o);
            }
            let c = Constraint::mk_eq(o, Op::mk_const(-1));
            result_constraint = Constraint::mk_conj(c, result_constraint);

            // add constraint for non-negativity
            for coef in coefs.iter().chain([constant_ident].iter()) {
                let c2 = Constraint::mk_geq(Op::mk_var(*coef), Op::mk_const(0));
                result_constraint = Constraint::mk_conj(result_constraint, c2);
            }

            result_constraint
        })
        .reduce(|x, y| Constraint::mk_conj(x, y))
        .unwrap_or(Constraint::mk_true());
    debug!("farkas result {result_constraint}");
    result_constraint
}

#[test]
fn test_farkas_transform() {
    use crate::formula::FirstOrderLogic;
    // example in Section 4.2.2. in the paper by Unno et al.(POPL 2012)
    let x = Ident::fresh();
    let y = Ident::fresh();
    let zv = Ident::fresh();

    let ip1 = Ident::fresh();
    let ip2 = Ident::fresh();
    let ip3 = Ident::fresh();
    let ip4 = Ident::fresh();

    println!("x: {x}");
    println!("y: {y}");
    println!("z: {zv}");

    println!("p1: {ip1}");
    println!("p2: {ip2}");
    println!("p3: {ip3}");
    println!("p4: {ip4}");

    let gen = |coefs: [Op; 4]| -> Constraint {
        let vars = [
            Op::mk_var(x),
            Op::mk_var(y),
            Op::mk_var(zv),
            Op::mk_const(1),
        ];
        let o = coefs
            .into_iter()
            .zip(vars.into_iter())
            .fold(Op::mk_const(0), |x, (coef, var)| {
                Op::mk_add(x, Op::mk_mul(coef.clone(), var.clone()))
            });
        Constraint::mk_bin_pred(PredKind::Geq, o, Op::mk_const(0))
    };
    let zero = Op::mk_const(0);
    let z = move || -> Op { zero.clone() };

    let p1 = move || -> Op { Op::mk_var(ip1) };
    let p2 = move || -> Op { Op::mk_var(ip2) };
    let p3 = move || -> Op { Op::mk_var(ip3) };
    let p4 = move || -> Op { Op::mk_var(ip4) };

    fn m(x: Op) -> Op {
        Op::mk_minus(x)
    }
    fn mul(x: Op, y: Op) -> Op {
        Op::mk_mul(x, y)
    }
    fn p(x: Op, y: Op) -> Op {
        Op::mk_add(x, y)
    }

    let table = [
        [p4(), z(), m(p4()), z()],
        [m(p4()), z(), p4(), z()],
        [
            mul(p1(), p4()),
            m(p(mul(p1(), p4()), p2())),
            p2(),
            p(mul(p1(), p4()), p2()),
        ],
        [
            m(mul(p1(), p4())),
            p(mul(p1(), p4()), p2()),
            m(p2()),
            m(p(mul(p1(), p4()), p2())),
        ],
        [Op::mk_const(1), Op::mk_const(-1), z(), Op::mk_const(-1)],
    ];
    let mut c = Constraint::mk_true();
    for row in table {
        let c1 = gen(row);
        println!("{c1}");
        c = Constraint::mk_conj(c, c1);
    }
    c = c.negate().unwrap();
    c = Constraint::mk_univ_int(zv, c);
    c = Constraint::mk_univ_int(y, c);
    c = Constraint::mk_univ_int(x, c);
    let c = farkas_transform(&c);
    println!("translated: {c}");
    let mut solver = crate::solver::smt::default_solver();
    let m = solver.solve_with_model(&c, &std::collections::HashSet::new(), &c.fv());
    let m = m.unwrap();
    println!("p1: {}", m.get(&ip1).unwrap());
    println!("p2: {}", m.get(&ip2).unwrap());
    println!("p4: {}", m.get(&ip4).unwrap());

    println!("{:?}", m.model);
    //assert!(false);
}

#[test]
fn test_farkas_transform2() {
    use crate::formula::*;
    let c = Constraint::mk_false();
    let c2 = farkas_transform(&c);
    println!("{c2}");

    let mut solver = crate::solver::smt::default_solver();
    assert!(solver.solve(&c2, &HashSet::new()).is_unsat());
}
#[test]
fn test_farkas_transform3() {
    // ∀x_17: i.((x_17 + 1) > 0) ∨ (x_17 <= 0)
    use crate::formula::*;
    let x17 = Ident::fresh();
    let c1 = Constraint::mk_bin_pred(
        PredKind::Gt,
        Op::mk_add(Op::mk_var(x17), Op::mk_const(1)),
        Op::mk_const(0),
    );
    let c2 = Constraint::mk_bin_pred(PredKind::Leq, Op::mk_var(x17), Op::mk_const(0));
    let c = Constraint::mk_disj(c1, c2);
    let c = Constraint::mk_univ_int(x17, c);
    let c2 = farkas_transform(&c);
    println!("{c2}");

    let mut solver = crate::solver::smt::default_solver();
    assert!(solver.solve(&c2, &HashSet::new()).is_sat());
}
