/// Given a linear integer arithmetic Constraint,
/// returns
///
///
use super::{Constraint, Fv, Logic, Op, PredKind};

fn transform_predicate(c: &Constraint) -> Constraint{
    fn inner(p: PredKind, l: &Vec<Op>) -> Constraint {
        assert_eq!(l.len(), 2);
        let x = l[0].clone();
        let y = l[1].clone();
        fn geq(x: Op, y: Op) -> Constraint {
            Constraint::mk_bin_pred(PredKind::Geq, x, y)
        }
        match p {
            PredKind::Eq => {
                let p1 = geq(x.clone(), y.clone());
                let p2 = geq(y.clone(), x.clone());
                Constraint::mk_conj(p1, p2)
            },
            PredKind::Neq => {
                /* 
                (assert (forall ((x Int) (y Int))
                    (and
                        (implies (not (= x y)) (or (>= y  (+ x 1)) (>= x (+ y 1))))
                        (implies (or (>= y (+ x 1)) (>= x (+ y 1))) (not (= x y)))
                    )
                ))
                (check-sat)
                */
                let p1 = geq(y.clone(), Op::mk_add(x.clone(), Op::mk_const(1)));
                let p2 = geq(x.clone(), Op::mk_add(y.clone(), Op::mk_const(1)));
                Constraint::mk_disj(p1, p2)
            },
            PredKind::Gt => {
                // x > y <=> x >= y + 1
                /*
                (assert (forall ((x Int) (y Int))
                        (and
                            (implies (> x y) (>= x (+ y 1)))
                            (implies (>= x (+ y 1)) (> x y))
                        )
                ))
                (check-sat)
                */
                geq(x, Op::mk_add(y.clone(), Op::mk_const(1)))
            },
            PredKind::Geq => geq(x, y),
            PredKind::Lt => {
                // x < y <=> y > x <=> y >= x + 1
                geq(y, Op::mk_add(x, Op::mk_const(0)))
            },
            PredKind::Leq => geq(y, x),
        }
    }

    match c.kind() {
        crate::formula::ConstraintExpr::True |
        crate::formula::ConstraintExpr::False => c.clone(),
        crate::formula::ConstraintExpr::Pred(p, l) => inner(p, l),
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

/// ### Assumption:
/// - c's free variables are considered to be bound by existential quantifiers
/// - c only contains universal quantifiers
/// - c only contains linear constraints
pub fn farkas_transform(c: &Constraint) -> Constraint {
    // translates the constraint to ∧ θᵢ where θᵢ has the form ¬ (∧ eᵢ ≥ 0).
    // Note that eᵢ is a linear expression.

    // 1. prenex normal form of c
    let mut fv = c.fv();
    let (v, c2) = c.prenex_normal_form_raw(&mut fv);
    // now c2 is a quantifier free formula
    for (q, _) in v.iter() {
        assert_eq!(*q, super::QuantifierKind::Universal);
    }

    // first replace all the predicates except for >= by constraints that only contain >= 


    // cnf = [θᵢ]
    let cnf = c2.to_cnf();

    // we transform cnf's element so that it has the form  ¬ (∧ eᵢ ≥ 0).
    let cnf = cnf.into_iter().map(|clause| {
        let dnf = clause.to_dnf();
        // we transform disjunction to not conjunction by de morgan dual
        // also, == is transformed to >= /\ <= 
        //       != is transformed to 
        let mut not_cnf = Vec::new();
        dnf.into_iter().map(|constr| {
            match constr.kind() {
                super::ConstraintExpr::True |
                super::ConstraintExpr::False => constr.clone(),
                super::ConstraintExpr::Pred(p, l) => {

                }
                super::ConstraintExpr::Quantifier(_, _, _) |
                super::ConstraintExpr::Conj(_, _) |
                super::ConstraintExpr::Disj(_, _) => panic!("program error"),
            }
        })
    })
    

    unimplemented!()
}
