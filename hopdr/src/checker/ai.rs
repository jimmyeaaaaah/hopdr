use std::fmt::write;

use crate::formula::hes::{Goal, GoalKind};
use crate::formula::{Constraint, Fv, Ident, Op, PredKind};
use crate::ml::Range;

type LB = Option<i64>;
type UB = Option<i64>;

#[derive(Clone, Copy)]
pub struct Domain {
    lb: LB,
    ub: UB,
}

fn compare_lb(x: LB, y: LB) -> bool {
    match (x, y) {
        (Some(x), Some(y)) => x <= y,
        (None, _) => true,
        _ => false,
    }
}

fn compare_ub(x: UB, y: UB) -> bool {
    match (x, y) {
        (Some(x), Some(y)) => x <= y,
        (_, None) => true,
        _ => false,
    }
}

impl Domain {
    pub fn all() -> Domain {
        Domain { lb: None, ub: None }
    }
    pub fn lb(lb: i64) -> Domain {
        Domain {
            lb: Some(lb),
            ub: None,
        }
    }
    pub fn ub(ub: i64) -> Domain {
        Domain {
            ub: Some(ub),
            lb: None,
        }
    }
    pub fn interval(lb: i64, ub: i64) -> Domain {
        Domain {
            lb: Some(lb),
            ub: Some(ub),
        }
    }
    // self ⊔ other
    pub fn join(self, other: Domain) -> Domain {
        let lb = match (self.lb, other.lb) {
            (Some(x), Some(y)) => Some(x.min(y)),
            _ => None,
        };
        let ub = match (self.ub, other.ub) {
            (Some(x), Some(y)) => Some(x.max(y)),
            _ => None,
        };
        Domain { lb, ub }
    }
    // self ⊓ other
    pub fn meet(self, other: Domain) -> Domain {
        let lb = match (self.lb, other.lb) {
            (Some(x), Some(y)) => Some(x.max(y)),
            (Some(x), None) | (None, Some(x)) => Some(x),
            _ => None,
        };
        let ub = match (self.ub, other.ub) {
            (Some(x), Some(y)) => Some(x.min(y)),
            (Some(x), None) | (None, Some(x)) => Some(x),
            _ => None,
        };
        Domain { lb, ub }
    }
    pub fn is_bot(&self) -> bool {
        match (self.lb, self.ub) {
            (Some(x), Some(y)) => x >= y,
            _ => false,
        }
    }
}

impl PartialEq for Domain {
    fn eq(&self, other: &Self) -> bool {
        self.lb == other.lb && self.ub == other.ub
    }
}

impl PartialOrd for Domain {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self == other {
            return Some(std::cmp::Ordering::Equal);
        }
        let x1_x2 = compare_lb(self.lb, other.lb);
        let y1_y2 = compare_ub(self.ub, other.ub);
        let x2_x1 = compare_lb(other.lb, self.lb);
        let y2_y1 = compare_ub(other.ub, self.ub);
        // [x1, y1) < [x2, y2) iff x1 <= x2 /\ y2 <= y1
        if x1_x2 && y2_y1 {
            Some(std::cmp::Ordering::Greater)
        // [x1, y1) > [x2, y2) iff x2 <= x1 /\ y1 <= y2
        } else if x2_x1 && y1_y2 {
            Some(std::cmp::Ordering::Less)
        } else {
            None
        }
    }
}

impl std::fmt::Display for Domain {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        match self.lb {
            Some(x) => write!(f, "{}", x)?,
            None => write!(f, "-∞")?,
        }
        write!(f, ", ")?;
        match self.ub {
            Some(x) => write!(f, "{}", x)?,
            None => write!(f, "∞")?,
        }
        write!(f, ")")
    }
}

#[test]
fn test_domain() {
    let i = Domain::interval(1, 3);
    assert!(!i.is_bot());
    let j = Domain::interval(1, 1);
    assert!(j.is_bot());
    let k = Domain::interval(1, 2);
    assert!(k < i);
    assert!(j < i && j < k);

    assert!(k == i.meet(k));
    assert!(i == i.join(k));
    assert!(j == i.meet(j));
    assert!(i == i.join(j));
    assert!(j == k.meet(j));
    assert!(k == k.join(j));

    let all = Domain::all();

    assert!(all == all.join(j));
    println!("{} /\\ {} = {}", all, j, all.meet(j));
    assert!(j == all.meet(j));

    assert!(j < all);
    assert!(all <= all);
    assert!(all == all);
}

fn handle_pred(target: Ident, p: PredKind, left: &Op, right: &Op) -> Domain {
    let o = Op::mk_sub(left.clone(), right.clone());
    let norm = Op::solve_for_with_sign(&target, left, right);
    let (sign, r) = match norm {
        Some(v) => v,
        None => return Domain::all(),
    };
    if r.fv().len() != 0 {
        return Domain::all();
    }
    match p {
        PredKind::Eq => Domain::all(),
        PredKind::Neq => todo!(),
        PredKind::Lt => todo!(),
        PredKind::Leq => todo!(),
        PredKind::Gt => todo!(),
        PredKind::Geq => todo!(),
    }
}

fn gen_bound(x: Ident, c: &Constraint) -> Domain {
    match c.kind() {
        crate::formula::ConstraintExpr::True | crate::formula::ConstraintExpr::False => {
            Domain::all()
        }
        crate::formula::ConstraintExpr::Pred(p, l) => {
            assert_eq!(l.len(), 2);
            handle_pred(x, *p, &l[0], &l[1])
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
