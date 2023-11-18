use crate::formula::hes::{Goal, GoalKind};
use crate::formula::{Constraint, Ident, Op, PredKind};
use crate::ml::Range;

#[derive(Clone, Copy)]
pub struct Domain {
    lb: Option<i64>,
    ub: Option<i64>,
}

impl Domain {
    pub fn all() -> Domain {
        Domain { lb: None, ub: None }
    }
    pub fn join(self, other: Domain) -> Domain {
        unimplemented!()
    }
    pub fn meet(self, other: Domain) -> Domain {
        unimplemented!()
    }
}

fn handle_pred(p: PredKind, left: &Op, right: &Op) -> Domain {
    unimplemented!()
}

fn gen_bound(x: Ident, c: &Constraint) -> Domain {
    match c.kind() {
        crate::formula::ConstraintExpr::True | crate::formula::ConstraintExpr::False => {
            Domain::all()
        }
        crate::formula::ConstraintExpr::Pred(p, l) => {
            assert_eq!(l.len(), 2);
            handle_pred(*p, &l[0], &l[1])
        }
        crate::formula::ConstraintExpr::Conj(c1, c2) => {
            let d1 = gen_bound(x, c1);
            let d2 = gen_bound(x, c2);
            d1.join(d2)
        }
        crate::formula::ConstraintExpr::Disj(c1, c2) => {
            let d1 = gen_bound(x, c1);
            let d2 = gen_bound(x, c2);
            d1.meet(d2)
        }
        crate::formula::ConstraintExpr::Quantifier(_, y, _) if x == y.id => Domain::all(),
        crate::formula::ConstraintExpr::Quantifier(_, _, c) => gen_bound(x, c),
    }
}

pub fn analyze(x: Ident, g: &Goal<Constraint>) -> Range {
    unimplemented!()
}
