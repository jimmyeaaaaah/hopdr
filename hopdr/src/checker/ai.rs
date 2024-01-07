use crate::formula::hes::{GoalBase, GoalKind};
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
    #[allow(dead_code)]
    pub fn is_bot(&self) -> bool {
        match (self.lb, self.ub) {
            (Some(x), Some(y)) => x >= y,
            _ => false,
        }
    }
    #[allow(dead_code)]
    /// returns the minimum value of the domain (in i64).
    pub fn min(&self) -> Option<i64> {
        if self.is_bot() {
            return None;
        }
        Some(match self.lb {
            Some(x) => x,
            None => std::i64::MIN,
        })
    }
    #[allow(dead_code)]
    /// returns the maximum value of the domain (in i64).
    pub fn max(&self) -> Option<i64> {
        if self.is_bot() {
            return None;
        }
        Some(match self.ub {
            Some(x) => x - 1,
            None => std::i64::MAX,
        })
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
    assert!(Some(1) == i.min());
    assert!(Some(2) == i.max());
    assert!(None == j.min());
    assert!(None == j.max());

    let all = Domain::all();

    assert!(all == all.join(j));
    println!("{} /\\ {} = {}", all, j, all.meet(j));
    assert!(j == all.meet(j));

    assert!(j < all);
    assert!(all <= all);
    assert!(all == all);
}
/// cx + d != 0 ---> cx + d = 0
fn handle_neq(c: i64, d: i64) -> Domain {
    if d % c != 0 {
        Domain::all()
    } else {
        Domain::interval(-d / c, -d / c + 1)
    }
}
/// cx + d < 0 ---> cx + d >= 0
fn handle_lt(c: i64, d: i64) -> Domain {
    if c < 0 {
        return handle_geq(-c, -d);
    }
    // x >= -d / c
    // x >= -3/4
    Domain::lb(-d / c)
}
/// cx + d <= 0 ---> cx + d > 0
fn handle_leq(c: i64, d: i64) -> Domain {
    if c < 0 {
        return handle_gt(-c, -d);
    }
    // x <= -d / c
    // 4x + 3 <= 0 ---> x > -3/4
    if d % c != 0 {
        Domain::lb(-d / c)
    } else {
        Domain::lb(-d / c)
    }
}
/// cx + d > 0
fn handle_gt(c: i64, d: i64) -> Domain {
    if c < 0 {
        return handle_leq(-c, -d);
    }
    // x <= -d / c
    Domain::ub(-d / c + 1)
}
/// cx + d >= 0
fn handle_geq(c: i64, d: i64) -> Domain {
    if c < 0 {
        return handle_lt(-c, -d);
    }
    if d % c != 0 {
        Domain::ub(-d / c + 1)
    } else {
        Domain::ub(-d / c)
    }
}

/// Given a atom left <pred> right, return the domain where the expr is **false**.
fn handle_pred(target: Ident, p: PredKind, left: &Op, right: &Op) -> Domain {
    let o = Op::mk_sub(left.clone(), right.clone());
    let fv = o.fv();
    if fv.len() != 1 || !fv.contains(&target) {
        return Domain::all();
    }
    let coefs = o.normalize(&vec![target]);
    let coefs = match coefs {
        Some(coefs) => coefs,
        None => return Domain::all(),
    };
    assert_eq!(coefs.len(), 2);
    let c = coefs[0].clone();
    let d = coefs[1].clone();
    // cx + d <pred> 0
    let d = match d.eval_with_empty_env() {
        Some(v) => v,
        None => return Domain::all(),
    };
    let c = match c.eval_with_empty_env() {
        Some(v) => v,
        None => return Domain::all(),
    };

    if c == 0 {
        return Domain::all();
    }

    match p {
        // cx == d -> x != d/c
        PredKind::Eq => Domain::all(),
        PredKind::Neq => handle_neq(c, d),
        PredKind::Lt => handle_lt(c, d),
        PredKind::Leq => handle_leq(c, d),
        PredKind::Gt => handle_gt(c, d),
        PredKind::Geq => handle_geq(c, d),
    }
}

#[test]
fn test_handle_pred() {
    use std::i64::MIN;
    use PredKind::*;
    let x = Ident::fresh();
    // 4 < x + x
    let o1 = Op::mk_const(4);
    let o2 = Op::mk_add(Op::mk_var(x), Op::mk_var(x));

    let preds = [Eq, Neq, Lt, Leq, Gt, Geq];
    // 4 >= x + x --> -2x + 4 >= 0 <=> 2x - 4 < 0 ----> 2x - 4 >= 0
    let mins = [MIN, 2, MIN, MIN, 2, 2];
    for (pred, mn) in preds.iter().zip(mins.iter()) {
        let d = handle_pred(x, *pred, &o1, &o2);
        println!("{d}");
        assert_eq!(d.min().unwrap(), *mn);
    }

    // 5 < x + x
    let o1 = Op::mk_const(5);
    let o2 = Op::mk_add(Op::mk_var(x), Op::mk_var(x));
    let mins = [MIN, MIN, MIN, MIN, 2, 2];
    for (pred, mn) in preds.iter().zip(mins.iter()) {
        let d = handle_pred(x, *pred, &o1, &o2);
        println!("{d}");
        assert_eq!(d.min().unwrap(), *mn);
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

fn analyze_inner<Aux>(x: Ident, g: &GoalBase<Constraint, Aux>) -> Domain {
    match g.kind() {
        GoalKind::Constr(c) => gen_bound(x, c),
        GoalKind::Op(_) => panic!("program error"),
        GoalKind::Var(_) | GoalKind::Abs(_, _) | GoalKind::App(_, _) => Domain::all(),
        GoalKind::Conj(g1, g2) => {
            let d1 = analyze_inner(x, g1);
            let d2 = analyze_inner(x, g2);
            d1.join(d2)
        }
        GoalKind::Disj(g1, g2) => {
            let d1 = analyze_inner(x, g1);
            let d2 = analyze_inner(x, g2);
            d1.meet(d2)
        }
        GoalKind::Univ(_, g) => analyze_inner(x, g),
    }
}

pub fn analyze<Aux>(x: Ident, g: &GoalBase<Constraint, Aux>) -> Range {
    let d = analyze_inner(x, g);
    let mut r = Range::new();
    if d.is_bot() {
        return r;
    }
    match d.lb {
        Some(x) => r = r.lb(x),
        None => (),
    }
    match d.ub {
        Some(x) => r = r.ub(x),
        None => (),
    }
    r
}
