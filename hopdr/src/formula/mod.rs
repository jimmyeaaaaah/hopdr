pub mod chc;
pub mod farkas;
pub mod fofml;
pub mod hes;
pub mod pcsp;
pub mod ty;

use std::collections::{HashMap, HashSet};
use std::fmt;

use rpds::Stack;

pub use crate::formula::ty::*;
use crate::parse::ExprKind;
use crate::util::global_counter;
use crate::util::Pretty;
pub use crate::util::P;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PredKind {
    Eq,
    Neq,
    Lt,
    Leq,
    Gt,
    Geq,
}

impl fmt::Display for PredKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.pretty_display())
    }
}

impl PredKind {
    pub fn negate(&self) -> PredKind {
        match self {
            PredKind::Eq => PredKind::Neq,
            PredKind::Neq => PredKind::Eq,
            PredKind::Lt => PredKind::Geq,
            PredKind::Leq => PredKind::Gt,
            PredKind::Gt => PredKind::Leq,
            PredKind::Geq => PredKind::Lt,
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum OpKind {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

impl fmt::Display for OpKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.pretty_display())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum QuantifierKind {
    Universal,
    Existential,
}

impl fmt::Display for QuantifierKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.pretty_display())
    }
}

impl QuantifierKind {
    fn negate(&self) -> QuantifierKind {
        match self {
            QuantifierKind::Existential => QuantifierKind::Universal,
            QuantifierKind::Universal => QuantifierKind::Existential,
        }
    }
    pub fn is_existential(&self) -> bool {
        matches!(self, Self::Existential)
    }
    pub fn is_universal(&self) -> bool {
        matches!(self, Self::Universal)
    }
    pub fn to_str(&self) -> &'static str {
        match self {
            QuantifierKind::Universal => "∀",
            QuantifierKind::Existential => "∃",
        }
    }
}

#[derive(Debug, Clone, Hash)]
pub enum OpExpr {
    Op(OpKind, Op, Op),
    Var(Ident),
    Const(i64),
    ITE(Constraint, Op, Op),
    // for tracking substitution, we memorize the old ident and replaced op
    // also this is a guard for optimization. you don't have to deref ptr to implement
    // optimization (otherwise, derivation procedure will break)
    Ptr(Ident, Op),
}

pub type Op = P<OpExpr>;
impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.pretty_display())
    }
}
impl PartialEq for Op {
    fn eq(&self, other: &Self) -> bool {
        match (self.kind(), other.kind()) {
            (OpExpr::Op(o1, x1, y1), OpExpr::Op(o2, x2, y2)) => o1 == o2 && x1 == x2 && y1 == y2,
            (OpExpr::Var(x), OpExpr::Var(y)) => x == y,
            (OpExpr::Const(c), OpExpr::Const(c2)) => c == c2,
            (OpExpr::Ptr(x1, y1), OpExpr::Ptr(x2, y2)) => x1 == x2 && y1 == y2,
            (_, _) => false,
        }
    }
}

impl Fv for Op {
    type Id = Ident;
    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>) {
        match self.kind() {
            OpExpr::Op(_, x, y) => {
                x.fv_with_vec(fvs);
                y.fv_with_vec(fvs);
            }
            OpExpr::Var(x) => {
                fvs.insert(*x);
            }
            OpExpr::ITE(x, y, z) => {
                x.fv_with_vec(fvs);
                y.fv_with_vec(fvs);
                z.fv_with_vec(fvs);
            }
            OpExpr::Const(_) => {}
            OpExpr::Ptr(_, o) => o.fv_with_vec(fvs),
        }
    }
}

impl From<Ident> for Op {
    fn from(x: Ident) -> Self {
        Op::mk_var(x)
    }
}

#[derive(Clone)]
pub struct IntegerEnvironment {
    imap: Stack<Ident>,
}

impl Default for IntegerEnvironment {
    fn default() -> Self {
        Self::new()
    }
}

impl IntegerEnvironment {
    pub fn new() -> IntegerEnvironment {
        IntegerEnvironment { imap: Stack::new() }
    }
    pub fn exists(&self, id: &Ident) -> bool {
        for i in self.imap.iter() {
            if i == id {
                return true;
            }
        }
        false
    }
    pub fn variables(&self) -> Vec<Ident> {
        // assumes alpha-renamed
        self.imap.iter().copied().collect()
    }
    pub fn push(mut self, v: Ident) -> IntegerEnvironment {
        self.imap.push_mut(v);
        self
    }

    pub fn iter(&self) -> impl Iterator<Item = Ident> + '_ {
        self.imap.iter().copied()
    }
}

impl Op {
    fn mk_bin_op_raw(op: OpKind, x: Op, y: Op) -> Op {
        Op::new(OpExpr::Op(op, x, y))
    }
    pub fn mk_bin_op(op: OpKind, x: Op, y: Op) -> Op {
        match op {
            OpKind::Add => Op::mk_add(x, y),
            OpKind::Sub => Op::mk_sub(x, y),
            OpKind::Mul => Op::mk_mul(x, y),
            OpKind::Div | OpKind::Mod => Op::mk_bin_op_raw(op, x, y),
        }
    }

    /// Checks if the given op is a constant, and equals to `c`
    pub fn check_const(&self, c: i64) -> bool {
        matches!(self.kind(), OpExpr::Const(c2) if c == *c2)
    }

    pub fn mk_add(x: Op, y: Op) -> Op {
        if x.check_const(0) {
            y
        } else if y.check_const(0) {
            x
        } else {
            match y.kind() {
                // assumes constant appears in the left-hand side of mul
                // this is true if you construct muls with mk_mul
                OpExpr::Op(OpKind::Mul, y, z) if y.check_const(-1) => Op::mk_sub(x, z.clone()),
                OpExpr::Const(c) if *c < 0 => Op::mk_sub(x, Op::mk_const(-c)),
                OpExpr::Op(_, _, _)
                | OpExpr::Const(_)
                | OpExpr::Var(_)
                | OpExpr::Ptr(_, _)
                | OpExpr::ITE(_, _, _) => Op::mk_bin_op_raw(OpKind::Add, x, y),
            }
        }
    }

    pub fn mk_sub(x: Op, y: Op) -> Op {
        if x.check_const(0) {
            Op::mk_minus(y)
        } else if y.check_const(0) {
            x
        } else {
            match y.kind() {
                // assumes constant appears in the left-hand side of mul
                // this is true if you construct muls with mk_mul
                OpExpr::Op(OpKind::Mul, y, z) if y.check_const(-1) => Op::mk_add(x, z.clone()),
                OpExpr::Const(c) if *c < 0 => Op::mk_add(x, Op::mk_const(-c)),
                OpExpr::Op(_, _, _)
                | OpExpr::Const(_)
                | OpExpr::Var(_)
                | OpExpr::Ptr(_, _)
                | OpExpr::ITE(_, _, _) => Op::mk_bin_op_raw(OpKind::Sub, x, y),
            }
        }
    }

    pub fn mk_mul(x: Op, y: Op) -> Op {
        use OpKind::*;
        if x.check_const(1) {
            y
        } else if y.check_const(1) {
            x
        } else if x.check_const(0) || y.check_const(0) {
            Op::mk_const(0)
        } else {
            match (x.kind(), y.kind()) {
                (OpExpr::Const(x), OpExpr::Const(y)) => Op::mk_const(x * y),
                (OpExpr::Const(c), OpExpr::Op(Mul, a, b))
                | (OpExpr::Op(Mul, a, b), OpExpr::Const(c)) => {
                    // place const in the left-hand side of OpExpr::Op
                    match (a.kind(), b.kind()) {
                        (OpExpr::Const(y), z) | (z, OpExpr::Const(y)) => {
                            Op::mk_mul(Op::mk_const(c * y), Op::new(z.clone()))
                        }
                        (_, _) => Op::mk_bin_op_raw(OpKind::Mul, x, y),
                    }
                }
                _ => Op::mk_bin_op_raw(OpKind::Mul, x, y),
            }
        }
    }

    pub fn mk_ite(c: Constraint, x: Op, y: Op) -> Op {
        if x == y {
            x
        } else {
            Op::new(OpExpr::ITE(c, x, y))
        }
    }

    pub fn mk_minus(x: Op) -> Op {
        Op::mk_bin_op_raw(OpKind::Sub, Op::mk_const(0), x)
    }

    pub fn mk_inc(x: Op) -> Op {
        Op::mk_add(x, Op::one())
    }

    pub fn mk_dec(x: Op) -> Op {
        Op::mk_sub(x, Op::one())
    }

    pub fn mk_const(x: i64) -> Op {
        Op::new(OpExpr::Const(x))
    }

    pub fn zero() -> Op {
        Op::mk_const(0)
    }

    pub fn one() -> Op {
        Op::mk_const(1)
    }

    pub fn mk_var(x: Ident) -> Op {
        Op::new(OpExpr::Var(x))
    }
    fn mk_ptr(x: Ident, o: Op) -> Op {
        Op::new(OpExpr::Ptr(x, o))
    }
    /// flattens Op expression by removing `OpExpr::Ptr` entry
    pub fn flatten(&self) -> Self {
        match self.kind() {
            OpExpr::Op(o, x, y) => {
                let x = x.flatten();
                let y = y.flatten();
                Op::mk_bin_op(*o, x, y)
            }
            OpExpr::Ptr(_, o) => o.flatten(),
            OpExpr::ITE(x, y, z) => {
                let x = x.flatten();
                let y = y.flatten();
                let z = z.flatten();
                Op::mk_ite(x, y, z)
            }
            OpExpr::Const(_) | OpExpr::Var(_) => self.clone(),
        }
    }
    pub fn to_hes_format(&self) -> String {
        match self.kind() {
            OpExpr::Op(o, x, y) => {
                let s1 = x.to_hes_format();
                let s2 = y.to_hes_format();
                format!("({} {} {})", s1, o, s2)
            }
            OpExpr::Var(x) => {
                format!("{}", x)
            }
            OpExpr::Const(c) => {
                format!("{}", c)
            }
            OpExpr::Ptr(_, x) => x.to_hes_format(),
            OpExpr::ITE(_, _, _) => unimplemented!(),
        }
    }
    pub fn negate(&self) -> Op {
        // check if self is `-1 * o`. if so, returns o. otherwise, returns -1 * self
        match self.kind() {
            OpExpr::Op(OpKind::Mul, o1, o2) => match o1.kind() {
                OpExpr::Const(-1) => o2.clone(),
                _ => Op::mk_mul(Op::mk_const(-1), self.clone()),
            },
            OpExpr::Op(_, _, _)
            | OpExpr::Var(_)
            | OpExpr::Const(_)
            | OpExpr::Ptr(_, _)
            | OpExpr::ITE(_, _, _) => Op::mk_mul(Op::mk_const(-1), self.clone()),
        }
    }
    // expand to term vectors which can be reduced to op by `add`.
    // that is, given `x + y`, expand_expr_to_vec returns [x, y]
    pub fn expand_expr_to_vec(&self) -> Option<Vec<Op>> {
        match self.kind() {
            OpExpr::Var(_) | OpExpr::Const(_) => Some(vec![self.clone()]),
            OpExpr::Ptr(_, o) => o.expand_expr_to_vec(),
            OpExpr::Op(OpKind::Add, o1, o2) => {
                let mut v1 = o1.expand_expr_to_vec()?;
                let mut v2 = o2.expand_expr_to_vec()?;
                v1.append(&mut v2);
                Some(v1)
            }
            OpExpr::Op(OpKind::Sub, o1, o2) => {
                let o2 = o2.negate();
                let mut v1 = o1.expand_expr_to_vec()?;
                let mut v2 = o2.expand_expr_to_vec()?;
                v1.append(&mut v2);
                Some(v1)
            }
            OpExpr::Op(OpKind::Mul, o1, o2) => {
                let v1 = o1.expand_expr_to_vec()?;
                let v2 = o2.expand_expr_to_vec()?;
                let mut new_v = Vec::new();
                for o1 in v1.iter() {
                    for o2 in v2.iter() {
                        new_v.push(Op::mk_bin_op(OpKind::Mul, o1.clone(), o2.clone()));
                    }
                }
                Some(new_v)
            }
            OpExpr::Op(_, _, _) | OpExpr::ITE(_, _, _) => None,
        }
    }
    /// expands the given op (e.g. (4 + 1) * ((2 - 3) + 2) -> (4 + 1) * (2 - 3) + (4 + 1) * 2 -> ((4 + 1) * 2 -  (4 + 1) * 3 + (4 + 1) * 2)
    pub fn expand_expr(&self) -> Option<Op> {
        let v = self.expand_expr_to_vec()?;
        assert!(!v.is_empty());
        let mut o = v[0].clone();
        for o2 in v[1..].iter() {
            o = Op::mk_add(o, o2.clone())
        }
        Some(o)
    }
    /// Given an linear op (of type Op) and a vector of variables x₁, …, xₙ,
    /// op.normalize returns a vector of Ops `v`.
    /// This method normalizes the given op to `o₀x₁ + ⋯ + o_n-1 xₙ `
    /// v[i] is the coefficient for xᵢ in the normalized `op`(i.e. oᵢ).
    /// v[n] is the constant part of `o_normalized` (i.e. o₀).
    pub fn normalize(&self, variables: &Vec<Ident>) -> Option<Vec<Op>> {
        fn parse_mult(o: &Op, m: &HashMap<Ident, usize>) -> Option<(Op, Option<Ident>)> {
            match o.kind() {
                crate::formula::OpExpr::Op(OpKind::Mul, o1, o2) => {
                    let (coef1, v1) = parse_mult(o1, m)?;
                    let (coef2, v2) = parse_mult(o2, m)?;
                    match (v1, v2) {
                        (Some(_), Some(_)) => None,
                        (Some(v), None) | (None, Some(v)) => {
                            Some((Op::mk_mul(coef1, coef2), Some(v)))
                        }
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
                OpExpr::ITE(_, _, _) | crate::formula::OpExpr::Op(_, _, _) => {
                    panic!("program error")
                }
            }
        }
        // assumption v.len() == m.len() + 1
        // v's m[id]-th element is the coefficient for the variable `id`
        // v's m.len()-th element is the constant
        let mut result_vec = vec![Op::mk_const(0); variables.len() + 1];
        let mut m = HashMap::new();
        for (i, v) in variables.iter().enumerate() {
            m.insert(*v, i);
        }
        let additions = self.expand_expr_to_vec()?;
        let constant_index = variables.len();
        for addition in additions {
            let (coef, v) = parse_mult(&addition, &m)?;
            let id = v.map_or(constant_index, |v| *m.get(&v).unwrap());
            result_vec[id] = Op::mk_add(result_vec[id].clone(), coef);
        }
        debug_assert!(result_vec.len() == variables.len() + 1);
        Some(result_vec)
    }

    /// normalize the given op o with respect to the given variable.
    /// returned vector of variables must starts with the variable
    fn normalize_with_focus(&self, on: &Ident) -> Option<(Vec<Ident>, Vec<Op>)> {
        let mut fv = self.fv();
        if !fv.contains(on) {
            return None;
        }
        fv.remove(on);

        let mut variables = vec![*on];
        for v in fv.into_iter() {
            variables.push(v);
        }
        let v = self.normalize(&variables)?;
        Some((variables, v))
    }
    /// This function solves the given linear equation `o1 <op> o2` w.r.t. x.
    /// To capture the sign of the solution, this function returns a pair of (bool, Op). (so that we can solve -x + 2 < 3, correctly).
    pub fn solve_for_with_sign(x: &Ident, o1: &Self, o2: &Self) -> Option<(bool, Op)> {
        let o = Op::mk_sub(o1.clone(), o2.clone());
        let (variables, mut v) = o.normalize_with_focus(x)?;
        // Of course, we can do more, but for now it's ok (like checking if we can divide "xi" by x_0)
        let coef = v[0].eval_with_empty_env();
        if coef == Some(1) {
            let mut r = Op::mk_minus(v.pop().unwrap());
            for (x, o) in variables.into_iter().zip(v.into_iter()).skip(1) {
                r = Op::mk_sub(r, Op::mk_mul(Op::mk_var(x), o));
            }
            Some((true, r))
        } else if coef == Some(-1) {
            let mut r = v.pop().unwrap();
            for (x, o) in variables.into_iter().zip(v.into_iter()).skip(1) {
                r = Op::mk_add(r, Op::mk_mul(Op::mk_var(x), o));
            }
            Some((false, r))
        } else {
            None
        }
    }
    pub fn solve_for(x: &Ident, o1: &Self, o2: &Self) -> Option<Op> {
        let (_, o) = Self::solve_for_with_sign(x, o1, o2)?;
        Some(o)
    }
}
#[test]
fn test_expansion() {
    // (x - 1) * (y + (z - w))
    let x = Ident::fresh();
    let y = Ident::fresh();
    let z = Ident::fresh();
    let w = Ident::fresh();
    let o1 = Op::mk_bin_op(OpKind::Sub, Op::mk_var(x), Op::mk_const(1));
    let o2 = Op::mk_add(
        Op::mk_var(y),
        Op::mk_bin_op(OpKind::Sub, Op::mk_var(x), Op::mk_var(w)),
    );
    let o = Op::mk_bin_op(OpKind::Mul, o1, o2);
    let o2 = o.expand_expr().unwrap();
    println!("{o}");
    println!("{o2}");

    assert_ne!(o, o2);

    let mut env = Env::new();
    env.add(x, 10);
    env.add(y, -11);
    env.add(z, 12);
    env.add(w, 13);
    let v = o.eval(&env).unwrap();
    let v2 = o2.eval(&env).unwrap();
    assert_eq!(v, v2);
}

#[test]
fn test_solve_for() {
    let x = Ident::fresh();
    let y = Ident::fresh();
    let z = Ident::fresh();
    println!("x: {x}");
    println!("y: {y}");

    // x = y
    let r = Op::solve_for(&y, &Op::mk_var(x), &Op::mk_var(y));
    assert!(r.is_some());
    let r = r.unwrap();
    println!("{}", r);
    match r.kind() {
        OpExpr::Var(z) if *z == x => (),
        _ => panic!(),
    }

    // 3 * (4 * x + 2 * y) - z = y
    let o1 = Op::mk_mul(Op::mk_const(4), Op::mk_var(x));
    let o2 = Op::mk_mul(Op::mk_const(2), Op::mk_var(y));
    let o3 = Op::mk_add(o1, o2);
    let o4 = Op::mk_mul(Op::mk_const(3), o3);
    let o5 = Op::mk_sub(o4, Op::mk_var(z));

    let r = Op::solve_for(&z, &o5, &Op::mk_var(y));
    assert!(r.is_some());
    println!("{}", r.unwrap());
}

impl DerefPtr for Op {
    fn deref_ptr(&self, id: &Ident) -> Op {
        match self.kind() {
            OpExpr::Op(o, x, y) => {
                let x = x.deref_ptr(id);
                let y = y.deref_ptr(id);
                Op::mk_bin_op(*o, x, y)
            }
            OpExpr::ITE(c, x, y) => {
                let c = c.deref_ptr(id);
                let x = x.deref_ptr(id);
                let y = y.deref_ptr(id);
                Op::mk_ite(c, x, y)
            }
            OpExpr::Var(_) | OpExpr::Const(_) => self.clone(),
            OpExpr::Ptr(id2, _o) if id == id2 => Op::mk_var(*id),
            OpExpr::Ptr(id2, o) => Op::mk_ptr(*id2, o.deref_ptr(id)),
        }
    }
}

#[test]
fn test_op_deref_ptr() {
    let x = Ident::fresh();
    let o = Op::mk_add(Op::mk_const(1), Op::mk_var(x));
    let o2 = Op::mk_const(4);
    let o3 = o.subst(&x, &o2);
    let o4 = o3.deref_ptr(&x);
    assert_eq!(o4, o);
}

#[test]
fn test_normalize() {
    // 5 x + 4 y + x + 2 (x + y + 1)
    // = 8 x + 6 y + 2
    let x = Ident::fresh();
    let y = Ident::fresh();
    let vars = vec![x, y];
    fn o(c: i64, id: Ident) -> Op {
        Op::mk_mul(Op::mk_const(c), Op::mk_var(id))
    }
    let o1 = o(5, x);
    let o2 = o(4, y);
    let o3 = o(1, x);
    let o4 = Op::mk_mul(
        Op::mk_const(2),
        Op::mk_add(Op::mk_const(1), Op::mk_add(Op::mk_var(x), Op::mk_var(y))),
    );
    let o = Op::mk_add(Op::mk_add(Op::mk_add(o1, o2), o3), o4);
    let v = o.normalize(&vars).unwrap();

    assert_eq!(v.len(), 3);

    let empty = Env::new();
    assert_eq!(v[0].eval(&empty).unwrap(), 8);
    assert_eq!(v[1].eval(&empty).unwrap(), 6);
    assert_eq!(v[2].eval(&empty).unwrap(), 2);
}

impl Subst for Op {
    type Item = Op;
    type Id = Ident;
    fn subst(&self, id: &Ident, v: &Op) -> Op {
        match self.kind() {
            OpExpr::Op(k, x, y) => Op::mk_bin_op(*k, x.subst(id, v), y.subst(id, v)),

            OpExpr::Var(id2) if id == id2 => Op::mk_ptr(*id, v.clone()),
            OpExpr::Ptr(x, o) => Op::mk_ptr(*x, o.subst(id, v)),
            OpExpr::ITE(c, x, y) => Op::mk_ite(c.subst(id, v), x.subst(id, v), y.subst(id, v)),
            OpExpr::Const(_) | OpExpr::Var(_) => self.clone(),
        }
    }
}

impl Rename for Op {
    fn rename(&self, id: &Ident, id2: &Ident) -> Op {
        match self.kind() {
            OpExpr::Op(k, x, y) => Op::mk_bin_op(*k, x.rename(id, id2), y.rename(id, id2)),

            OpExpr::Var(id3) if id == id3 => Op::mk_var(*id2),
            OpExpr::Ptr(x, o) => Op::mk_ptr(*x, o.rename(id, id2)),
            OpExpr::ITE(c, x, y) => {
                Op::mk_ite(c.rename(id, id2), x.rename(id, id2), y.rename(id, id2))
            }
            OpExpr::Const(_) | OpExpr::Var(_) => self.clone(),
        }
    }
}

impl AlphaEquivalence for Op {
    fn alpha_equiv_map(&self, other: &Self, map: &mut HashMap<Ident, Ident>) -> bool {
        let left = self.flatten();
        let right = other.flatten();
        match (left.kind(), right.kind()) {
            (OpExpr::Op(o1, x1, y1), OpExpr::Op(o2, x2, y2)) if o1 == o2 => {
                x1.alpha_equiv_map(x2, map) && y1.alpha_equiv_map(y2, map)
            }
            (OpExpr::Var(x1), OpExpr::Var(x2)) => match map.get(x1) {
                Some(x2_) => x2 == x2_,
                None => {
                    map.insert(*x1, *x2);
                    true
                }
            },
            (OpExpr::Const(c1), OpExpr::Const(c2)) => c1 == c2,
            (OpExpr::ITE(c, x, y), OpExpr::ITE(c2, x2, y2)) => {
                c.alpha_equiv_map(c2, map)
                    && x.alpha_equiv_map(x2, map)
                    && y.alpha_equiv_map(y2, map)
            }
            (_, _) => false,
        }
    }
}

pub trait Top {
    fn mk_true() -> Self;
    fn is_true(&self) -> bool;
}

pub trait Bot {
    fn mk_false() -> Self;
    fn is_false(&self) -> bool;
}

pub trait Logic: Top + Bot + Clone {
    fn mk_conj(x: Self, y: Self) -> Self;
    fn is_conj(&self) -> Option<(&Self, &Self)>;
    fn mk_disj(x: Self, y: Self) -> Self;
    fn is_disj(&self) -> Option<(&Self, &Self)>;

    fn to_cnf(&self) -> Vec<Self> {
        fn cross_or<C: Clone + Logic>(v1: &[C], v2: &[C]) -> Vec<C> {
            let mut v = Vec::new();
            for x in v1 {
                for y in v2 {
                    v.push(C::mk_disj(x.clone(), y.clone()));
                }
            }
            v
        }
        if let Some((x, y)) = self.is_conj() {
            let mut v1 = x.to_cnf();
            let mut v2 = y.to_cnf();
            v1.append(&mut v2);
            return v1;
        };
        match self.is_disj() {
            Some((x, y)) => {
                let v1 = x.to_cnf();
                let v2 = y.to_cnf();
                cross_or(&v1, &v2)
            }
            None => vec![self.clone()],
        }
    }
    fn to_dnf(&self) -> Vec<Self> {
        fn cross_and<C: Clone + Logic>(v1: &[C], v2: &[C]) -> Vec<C> {
            let mut v = Vec::new();
            for x in v1 {
                for y in v2 {
                    v.push(C::mk_conj(x.clone(), y.clone()));
                }
            }
            v
        }
        if let Some((x, y)) = self.is_disj() {
            let mut v1 = x.to_dnf();
            let mut v2 = y.to_dnf();
            v1.append(&mut v2);
            return v1;
        }
        match self.is_conj() {
            Some((x, y)) => {
                let v1 = x.to_dnf();
                let v2 = y.to_dnf();
                cross_and(&v1, &v2)
            }
            None => vec![self.clone()],
        }
    }
}

pub trait FirstOrderLogic: Logic {
    fn mk_quantifier_int(q: QuantifierKind, v: Ident, c: Self) -> Self;
    fn mk_exists_int(v: Ident, c: Self) -> Self {
        Self::mk_quantifier_int(QuantifierKind::Existential, v, c)
    }
    fn mk_univ_int(v: Ident, c: Self) -> Self {
        Self::mk_quantifier_int(QuantifierKind::Universal, v, c)
    }
}

pub trait Subst: Sized + Clone {
    type Item;
    type Id;
    // impl IntoIterator is better, but rust-analyzer fails
    // issue: - https://github.com/rust-lang/rust-analyzer/issues/10932
    //        - https://github.com/rust-lang/rust-analyzer/issues/12484
    fn subst_multi(&self, substs: &[(Self::Id, Self::Item)]) -> Self {
        let mut itr = substs.iter();
        let (id, item) = match itr.next() {
            Some((id, item)) => (id, item),
            None => return self.clone(),
        };
        let mut ret = self.subst(id, item);
        for (ident, val) in itr {
            ret = ret.subst(ident, val);
        }
        ret
    }
    fn subst(&self, x: &Self::Id, v: &Self::Item) -> Self;
}

pub trait Rename: Sized {
    fn rename(&self, x: &Ident, y: &Ident) -> Self;
    // TODO: fix type xs
    fn rename_idents(&self, xs: &[(Ident, Ident)]) -> Self {
        assert!(!xs.is_empty());
        let mut c = self.rename(&xs[0].0, &xs[0].1);
        for (x, y) in &xs[1..] {
            c = c.rename(x, y);
        }
        c
    }
    fn rename_idents_with_slices(&self, xs: &[Ident], ys: &[Ident]) -> Self {
        assert!(xs.len() == ys.len());
        // TODO: Fix this bad impl
        let mut v = Vec::new();
        for (x, y) in xs.iter().zip(ys.iter()) {
            v.push((*x, *y))
        }
        self.rename_idents(&v)
    }
}

pub trait Fv {
    type Id;

    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>);

    fn fv(&self) -> HashSet<Self::Id> {
        let mut fvs = HashSet::new();
        self.fv_with_vec(&mut fvs);
        fvs
    }
}

pub trait DerefPtr {
    fn deref_ptr(&self, id: &Ident) -> Self;
}

pub trait AlphaEquivalence {
    fn alpha_equiv_map(&self, other: &Self, map: &mut HashMap<Ident, Ident>) -> bool;
    fn alpha_equiv(&self, other: &Self) -> bool {
        self.alpha_equiv_map(other, &mut HashMap::new())
    }
}

#[derive(Debug, Hash)]
pub enum ConstraintExpr {
    True,
    False,
    Pred(PredKind, Vec<Op>),
    Conj(Constraint, Constraint),
    Disj(Constraint, Constraint),
    Quantifier(QuantifierKind, Variable, Constraint),
}

pub type Constraint = P<ConstraintExpr>;

impl fmt::Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.pretty_display())
    }
}

impl PartialEq for Constraint {
    fn eq(&self, other: &Self) -> bool {
        let r = match (self.kind(), other.kind()) {
            (ConstraintExpr::True, ConstraintExpr::True) => true,
            (ConstraintExpr::False, ConstraintExpr::False) => true,
            (ConstraintExpr::Pred(PredKind::Eq, l1), ConstraintExpr::Pred(PredKind::Eq, l2))
                if l1.len() == 2 && l2.len() == 2 =>
            {
                // x == y vs x == y
                // or x == y vs y == x
                (l1[0] == l2[0] && l1[1] == l2[1]) || (l1[0] == l2[1] && l1[1] == l2[0])
            }
            (ConstraintExpr::Pred(p1, l1), ConstraintExpr::Pred(p2, l2)) => p1 == p2 && l1 == l2,
            (ConstraintExpr::Conj(x1, y1), ConstraintExpr::Conj(x2, y2)) => x1 == x2 && y1 == y2,
            (ConstraintExpr::Disj(x1, y1), ConstraintExpr::Disj(x2, y2)) => x1 == x2 && y1 == y2,
            (ConstraintExpr::Quantifier(q1, x1, y1), ConstraintExpr::Quantifier(q2, x2, y2)) => {
                q1 == q2 && x1 == x2 && y1 == y2
            }
            (_, _) => false,
        };
        r
    }
}

impl Top for Constraint {
    fn mk_true() -> Constraint {
        Constraint::new(ConstraintExpr::True)
    }
    fn is_true(&self) -> bool {
        match self.kind() {
            ConstraintExpr::True => true,
            ConstraintExpr::Quantifier(QuantifierKind::Universal, _, c) => c.is_true(),
            ConstraintExpr::Conj(c1, c2) => c1.is_true() && c2.is_true(),
            ConstraintExpr::Disj(c1, c2) => c1.is_true() || c2.is_true(),
            _ => false,
        }
    }
}
impl Bot for Constraint {
    fn mk_false() -> Constraint {
        Constraint::new(ConstraintExpr::False)
    }
    fn is_false(&self) -> bool {
        match self.kind() {
            ConstraintExpr::False => true,
            ConstraintExpr::Quantifier(QuantifierKind::Universal, _, c) => c.is_false(),
            ConstraintExpr::Conj(c1, c2) => c1.is_false() || c2.is_false(),
            ConstraintExpr::Disj(c1, c2) => c1.is_false() && c2.is_false(),
            _ => false,
        }
    }
}

impl Logic for Constraint {
    fn mk_conj(x: Constraint, y: Constraint) -> Constraint {
        if x.is_false() || y.is_false() {
            Constraint::mk_false()
        } else if x.is_true() {
            y
        } else if y.is_true() {
            x
        } else {
            Constraint::new(ConstraintExpr::Conj(x, y))
        }
    }
    fn is_conj(&self) -> Option<(&Constraint, &Constraint)> {
        match self.kind() {
            ConstraintExpr::Conj(x, y) => Some((x, y)),
            _ => None,
        }
    }
    fn mk_disj(x: Constraint, y: Constraint) -> Constraint {
        if x.is_true() || y.is_true() {
            Constraint::mk_true()
        } else if x.is_false() {
            y
        } else if y.is_false() {
            x
        } else {
            Constraint::new(ConstraintExpr::Disj(x, y))
        }
    }
    fn is_disj(&self) -> Option<(&Constraint, &Constraint)> {
        match self.kind() {
            ConstraintExpr::Disj(x, y) => Some((x, y)),
            _ => None,
        }
    }
}
impl FirstOrderLogic for Constraint {
    fn mk_quantifier_int(q: QuantifierKind, v: Ident, c: Constraint) -> Constraint {
        Constraint::new(ConstraintExpr::Quantifier(
            q,
            Variable::mk(v, Type::mk_type_int()),
            c,
        ))
    }
}

impl Subst for Constraint {
    type Item = Op;
    type Id = Ident;
    // \theta[v/x]
    fn subst(&self, x: &Ident, v: &Op) -> Constraint {
        use ConstraintExpr::*;
        match self.kind() {
            True | False => self.clone(),
            Pred(k, ops) => {
                let mut new_ops = Vec::new();
                for op in ops.iter() {
                    new_ops.push(op.subst(x, v));
                }
                Constraint::mk_pred(*k, new_ops)
            }
            Conj(r, l) => Constraint::mk_conj(r.subst(x, v), l.subst(x, v)),
            Disj(r, l) => Constraint::mk_disj(r.subst(x, v), l.subst(x, v)),
            // assumption: vars are different each other ?
            Quantifier(q, var, cstr) => {
                Constraint::mk_quantifier(*q, var.clone(), cstr.subst(x, v))
            }
        }
    }
}

impl Rename for Constraint {
    // \theta[v/x]
    fn rename(&self, x: &Ident, y: &Ident) -> Constraint {
        use ConstraintExpr::*;
        match self.kind() {
            True | False => self.clone(),
            Pred(k, ops) => {
                let mut new_ops = Vec::new();
                for op in ops.iter() {
                    new_ops.push(op.rename(x, y));
                }
                Constraint::mk_pred(*k, new_ops)
            }
            Conj(r, l) => Constraint::mk_conj(r.rename(x, y), l.rename(x, y)),
            Disj(r, l) => Constraint::mk_disj(r.rename(x, y), l.rename(x, y)),
            // assumption: vars are different each other ?
            Quantifier(q, var, cstr) if &var.id != x && &var.id != y => {
                Constraint::mk_quantifier(*q, var.clone(), cstr.rename(x, y))
            }
            Quantifier(_, _, _) => panic!("assumption broken"),
        }
    }
}

impl AlphaEquivalence for Constraint {
    fn alpha_equiv_map(&self, other: &Self, map: &mut HashMap<Ident, Ident>) -> bool {
        match (self.kind(), other.kind()) {
            (ConstraintExpr::True, ConstraintExpr::True)
            | (ConstraintExpr::False, ConstraintExpr::False) => true,
            (ConstraintExpr::Pred(p1, l1), ConstraintExpr::Pred(p2, l2))
                if p1 == p2 && l1.len() == l2.len() =>
            {
                l1.iter()
                    .zip(l2.iter())
                    .all(|(x, y)| x.alpha_equiv_map(y, map))
            }
            (ConstraintExpr::Conj(x1, y1), ConstraintExpr::Conj(x2, y2))
            | (ConstraintExpr::Disj(x1, y1), ConstraintExpr::Disj(x2, y2)) => {
                x1.alpha_equiv_map(x2, map) && y1.alpha_equiv_map(y2, map)
            }
            (ConstraintExpr::Quantifier(q1, v1, x1), ConstraintExpr::Quantifier(q2, v2, x2))
                if q1 == q2 =>
            {
                // renaming to avoid shadowing
                let x = Ident::fresh();
                let x1 = x1.rename(&v1.id, &x);
                let x2 = x2.rename(&v2.id, &x);
                x1.alpha_equiv_map(&x2, map)
            }
            (_, _) => false,
        }
    }
}

#[test]
fn test_alpha_equivalence_for_constraint() {
    fn gen() -> Constraint {
        let x = Ident::fresh();
        let y = Ident::fresh();
        Constraint::mk_exists_int(
            y,
            Constraint::mk_conj(
                Constraint::mk_eq(Op::mk_var(x), Op::mk_var(y)),
                Constraint::mk_eq(Op::mk_var(x), Op::mk_add(Op::mk_var(y), Op::mk_const(1))),
            ),
        )
    }
    fn gen2() -> Constraint {
        let x = Ident::fresh();
        let y = Ident::fresh();
        let z = Ident::fresh();
        Constraint::mk_exists_int(
            y,
            Constraint::mk_conj(
                Constraint::mk_eq(Op::mk_var(x), Op::mk_var(y)),
                Constraint::mk_eq(Op::mk_var(x), Op::mk_add(Op::mk_var(z), Op::mk_const(1))),
            ),
        )
    }

    let c1 = gen();
    let c2 = gen();
    let c3 = gen2();
    assert!(c1.alpha_equiv(&c2));
    assert!(!c1.alpha_equiv(&c3));
}

pub trait Negation {
    fn negate(&self) -> Option<Self>
    where
        Self: Sized;
}
impl Negation for Constraint {
    // negation sometimes cannot be performed (e.g. \not x)
    fn negate(&self) -> Option<Constraint> {
        match self.kind() {
            ConstraintExpr::False => Some(Constraint::mk_true()),
            ConstraintExpr::True => Some(Constraint::mk_false()),
            ConstraintExpr::Pred(p, v) => Some(Constraint::mk_pred(p.negate(), v.clone())),
            ConstraintExpr::Conj(c1, c2) => match (c1.clone().negate(), c2.clone().negate()) {
                (Some(c1), Some(c2)) => Some(Constraint::mk_disj(c1, c2)),
                _ => None,
            },
            ConstraintExpr::Disj(c1, c2) => match (c1.clone().negate(), c2.clone().negate()) {
                (Some(c1), Some(c2)) => Some(Constraint::mk_conj(c1, c2)),
                _ => None,
            },
            ConstraintExpr::Quantifier(q, v, c) => {
                let q = q.negate();
                c.clone()
                    .negate()
                    .map(|c| Constraint::mk_quantifier(q, v.clone(), c))
            }
        }
    }
}

impl Constraint {
    pub fn mk_quantifier(q: QuantifierKind, v: Variable, c: Constraint) -> Constraint {
        Constraint::new(ConstraintExpr::Quantifier(q, v, c))
    }
    pub fn mk_implies(x: Self, y: Self) -> Self {
        x.negate().map(|x| Self::mk_disj(x, y)).unwrap()
    }

    pub fn mk_pred(k: PredKind, v: Vec<Op>) -> Constraint {
        Constraint::new(ConstraintExpr::Pred(k, v))
    }

    // these methods are useful for generating constraints to make tests
    pub fn mk_bin_pred(k: PredKind, left: Op, right: Op) -> Constraint {
        match k {
            PredKind::Eq | PredKind::Leq | PredKind::Geq if left == right => Constraint::mk_true(),
            PredKind::Neq | PredKind::Lt | PredKind::Gt if left == right => Constraint::mk_false(),
            _ => Constraint::mk_pred(k, vec![left, right]),
        }
    }
    pub fn mk_lt(left: Op, right: Op) -> Constraint {
        Self::mk_bin_pred(PredKind::Lt, left, right)
    }
    pub fn mk_leq(left: Op, right: Op) -> Constraint {
        Self::mk_bin_pred(PredKind::Leq, left, right)
    }
    pub fn mk_gt(left: Op, right: Op) -> Constraint {
        Self::mk_bin_pred(PredKind::Gt, left, right)
    }
    pub fn mk_geq(left: Op, right: Op) -> Constraint {
        Self::mk_bin_pred(PredKind::Geq, left, right)
    }
    pub fn mk_eq(left: Op, right: Op) -> Constraint {
        Self::mk_bin_pred(PredKind::Eq, left, right)
    }
    pub fn mk_neq(left: Op, right: Op) -> Constraint {
        Self::mk_bin_pred(PredKind::Neq, left, right)
    }

    pub fn variable_guard(v: Ident, op: Op) -> Constraint {
        let v = Op::mk_var(v);
        Constraint::mk_pred(PredKind::Eq, vec![v, op])
    }

    pub fn remove_quantifier(self) -> Constraint {
        match self.kind() {
            ConstraintExpr::True | ConstraintExpr::False | ConstraintExpr::Pred(_, _) => {
                self.clone()
            }
            ConstraintExpr::Conj(c1, c2) => Constraint::mk_conj(
                c1.clone().remove_quantifier(),
                c2.clone().remove_quantifier(),
            ),
            ConstraintExpr::Disj(c1, c2) => Constraint::mk_disj(
                c1.clone().remove_quantifier(),
                c2.clone().remove_quantifier(),
            ),
            ConstraintExpr::Quantifier(_, _, c) => c.clone().remove_quantifier(),
        }
    }
    /// env: current free variable
    fn prenex_normal_form_raw(
        &self,
        env: &mut HashSet<Ident>,
    ) -> (Vec<(QuantifierKind, Variable)>, Constraint) {
        match self.kind() {
            ConstraintExpr::True | ConstraintExpr::False | ConstraintExpr::Pred(_, _) => {
                (Vec::new(), self.clone())
            }
            ConstraintExpr::Conj(c1, c2) => {
                let (mut v1, c1) = c1.prenex_normal_form_raw(env);
                let (mut v2, c2) = c2.prenex_normal_form_raw(env);
                v1.append(&mut v2);
                (v1, Constraint::mk_conj(c1, c2))
            }
            ConstraintExpr::Disj(c1, c2) => {
                let (mut v1, c1) = c1.prenex_normal_form_raw(env);
                let (mut v2, c2) = c2.prenex_normal_form_raw(env);
                v1.append(&mut v2);
                (v1, Constraint::mk_disj(c1, c2))
            }
            ConstraintExpr::Quantifier(q, x, c) => {
                let (x, c) = if env.contains(&x.id) {
                    // if env already contains the ident to be bound,
                    // we rename it to a fresh one.
                    let x2_ident = Ident::fresh();
                    let x2 = Variable::mk(x2_ident, x.ty.clone());
                    let c = c.rename(&x.id, &x2_ident);
                    (x2, c)
                } else {
                    (x.clone(), c.clone())
                };
                env.insert(x.id);
                let (mut v, c) = c.prenex_normal_form_raw(env);
                debug_assert!(!v.iter().any(|(_, y)| { x.id == y.id }));
                v.push((*q, x));
                (v, c)
            }
        }
    }
    pub fn to_pnf(&self) -> Constraint {
        let (_, c) = self.prenex_normal_form_raw(&mut HashSet::new());
        c
    }
    pub fn replace_exists_with_fresh_var(&self) -> Constraint {
        match self.kind() {
            ConstraintExpr::True | ConstraintExpr::False | ConstraintExpr::Pred(_, _) => {
                self.clone()
            }
            ConstraintExpr::Conj(x, y) => {
                let left = x.replace_exists_with_fresh_var();
                let right = y.replace_exists_with_fresh_var();
                Constraint::mk_conj(left, right)
            }
            ConstraintExpr::Disj(x, y) => {
                let left = x.replace_exists_with_fresh_var();
                let right = y.replace_exists_with_fresh_var();
                Constraint::mk_disj(left, right)
            }
            ConstraintExpr::Quantifier(p, x, c) if *p == QuantifierKind::Existential => c
                .rename(&x.id, &Ident::fresh())
                .replace_exists_with_fresh_var(),
            _ => panic!("program error"),
        }
    }
    pub fn to_pnf_raw(&self) -> (Vec<(QuantifierKind, Variable)>, Constraint) {
        self.prenex_normal_form_raw(&mut HashSet::new())
    }
    pub fn to_hes_format(&self) -> String {
        match self.kind() {
            ConstraintExpr::True => "true".to_string(),
            ConstraintExpr::False => "false".to_string(),
            ConstraintExpr::Pred(p, l) if l.len() == 2 => {
                let mut s = l[0].to_hes_format();
                s += match p {
                    PredKind::Eq => "=",
                    PredKind::Neq => "!=",
                    PredKind::Lt => "<",
                    PredKind::Leq => "<=",
                    PredKind::Gt => ">",
                    PredKind::Geq => ">=",
                };
                s += &l[1].to_hes_format();
                s
            }
            ConstraintExpr::Pred(_p, _l) => panic!("fatal"),
            ConstraintExpr::Disj(x, y) => {
                format!("( {} \\/ {} )", x.to_hes_format(), y.to_hes_format())
            }
            ConstraintExpr::Conj(x, y) => {
                format!("( {} /\\ {} )", x.to_hes_format(), y.to_hes_format())
            }
            ConstraintExpr::Quantifier(_, _, _) => unimplemented!(),
        }
    }
    pub fn flatten(&self) -> Constraint {
        match self.kind() {
            ConstraintExpr::True | ConstraintExpr::False => self.clone(),
            ConstraintExpr::Pred(p, l) => {
                let l = l.iter().map(|o| o.flatten()).collect();
                Constraint::mk_pred(*p, l)
            }
            ConstraintExpr::Conj(c1, c2) => {
                let c1 = c1.flatten();
                let c2 = c2.flatten();
                Constraint::mk_conj(c1, c2)
            }
            ConstraintExpr::Disj(c1, c2) => {
                let c1 = c1.flatten();
                let c2 = c2.flatten();
                Constraint::mk_disj(c1, c2)
            }
            ConstraintExpr::Quantifier(q, x, c) => {
                let c = c.flatten();
                Constraint::mk_quantifier(*q, x.clone(), c)
            }
        }
    }
}

#[test]
fn test_prenex_normal_form() {
    // (∀x. x = 0) ∨ (∀x. x = 0)
    let x = Ident::fresh();
    let c = Constraint::mk_eq(Op::mk_var(x), Op::mk_const(0));
    let c2 = Constraint::mk_univ_int(x, c.clone());
    let c3 = Constraint::mk_disj(c2.clone(), c2);
    let (v, c5) = c3.prenex_normal_form_raw(&mut HashSet::new());
    println!("{c5}");
    assert_eq!(v.len(), 2);
    assert!(v[0].1.id != v[1].1.id);
}
impl DerefPtr for Constraint {
    fn deref_ptr(&self, id: &Ident) -> Constraint {
        match self.kind() {
            ConstraintExpr::True | ConstraintExpr::False => self.clone(),
            ConstraintExpr::Pred(p, l) => {
                let l = l.iter().map(|o| o.deref_ptr(id)).collect();
                Constraint::mk_pred(*p, l)
            }
            ConstraintExpr::Conj(x, y) => {
                let x = x.deref_ptr(id);
                let y = y.deref_ptr(id);
                Constraint::mk_conj(x, y)
            }
            ConstraintExpr::Disj(x, y) => {
                let x = x.deref_ptr(id);
                let y = y.deref_ptr(id);
                Constraint::mk_disj(x, y)
            }
            ConstraintExpr::Quantifier(q, v, x) => {
                let x = x.deref_ptr(id);
                Constraint::mk_quantifier(*q, v.clone(), x)
            }
        }
    }
}
#[test]
fn test_constraint_deref_ptr() {
    let x = Ident::fresh();
    let o = Op::mk_add(Op::mk_const(1), Op::mk_var(x));
    let o2 = Op::mk_const(4);
    let c = Constraint::mk_lt(o, o2.clone());
    let c2 = c.subst(&x, &o2);
    let c3 = c2.deref_ptr(&x);
    assert_eq!(c, c3);
}
impl Fv for Constraint {
    type Id = Ident;

    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>) {
        match self.kind() {
            ConstraintExpr::True | ConstraintExpr::False => {}
            ConstraintExpr::Pred(_, ops) => {
                for op in ops.iter() {
                    op.fv_with_vec(fvs);
                }
            }
            ConstraintExpr::Conj(x, y) | ConstraintExpr::Disj(x, y) => {
                x.fv_with_vec(fvs);
                y.fv_with_vec(fvs);
            }
            ConstraintExpr::Quantifier(_, v, x) => {
                let already_contained = fvs.contains(&v.id);
                x.fv_with_vec(fvs);
                if !already_contained {
                    fvs.remove(&v.id);
                }
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Ident {
    id: u64,
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.pretty_display())
    }
}

impl Ident {
    pub fn fresh() -> Ident {
        let id = global_counter();
        Ident { id }
    }
    pub fn rename_idents(args: &[Ident], x: &Ident, y: &Ident) -> Vec<Ident> {
        args.iter()
            .map(|arg| if arg == x { *y } else { *arg })
            .collect()
    }
    /// assumption: string expression is x_\d+
    pub fn parse_ident(s: &str) -> Option<Ident> {
        debug!("Ident::from_str: {}", s);
        match s[2..].parse() {
            Ok(id) => Some(Ident { id }),
            Err(_) => None,
        }
    }
    pub fn get_id(&self) -> u64 {
        self.id
    }
}

impl From<u64> for Ident {
    fn from(id: u64) -> Self {
        Ident { id }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct VariableS {
    pub id: Ident,
    pub ty: Type,
}
pub type Variable = P<VariableS>;

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.pretty_display())
    }
}

impl Variable {
    pub fn mk(id: Ident, ty: Type) -> Variable {
        Variable::new(VariableS { id, ty })
    }
    pub fn id(&self) -> Ident {
        self.id
    }
    pub fn ty(&self) -> &Type {
        &self.ty
    }
    pub fn fresh(ty: Type) -> Variable {
        let id = Ident::fresh();
        Variable::new(VariableS { id, ty })
    }
    // methods for testing
    pub fn fresh_prop() -> Variable {
        Variable::fresh(Type::mk_type_prop())
    }
    pub fn fresh_int() -> Variable {
        Variable::fresh(Type::mk_type_int())
    }
    pub fn order(&self) -> usize {
        self.ty.order()
    }
}

#[derive(Clone, Debug)]
pub enum Fixpoint {
    Greatest,
    Least,
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Polarity {
    Positive,
    Negative,
}
impl Polarity {
    pub fn rev(self) -> Polarity {
        if self == Polarity::Positive {
            Polarity::Negative
        } else {
            Polarity::Positive
        }
    }
}

//////// evaluation ////////
#[derive(Debug)]
pub struct Env {
    map: std::collections::HashMap<Ident, i64>,
}

impl Default for Env {
    fn default() -> Self {
        Self::new()
    }
}

impl Env {
    pub fn new() -> Self {
        Env {
            map: std::collections::HashMap::new(),
        }
    }

    pub fn add(&mut self, k: Ident, v: i64) {
        self.map.insert(k, v);
    }
}

impl OpKind {
    pub fn eval(&self, x: i64, y: i64) -> i64 {
        match self {
            OpKind::Add => x + y,
            OpKind::Sub => x - y,
            OpKind::Mul => x * y,
            OpKind::Div => x / y,
            OpKind::Mod => x % y,
        }
    }
    pub fn to_str(&self) -> &'static str {
        match self {
            OpKind::Add => "+",
            OpKind::Sub => "-",
            OpKind::Mul => "*",
            OpKind::Div => "/",
            OpKind::Mod => "%",
        }
    }
}

impl Op {
    pub fn eval(&self, env: &Env) -> Option<i64> {
        match self.kind() {
            OpExpr::Op(o, x, y) => {
                let xv = x.eval(env)?;
                let yv = y.eval(env)?;
                Some(o.eval(xv, yv))
            }
            OpExpr::Var(x) => env.map.get(x).cloned(),
            OpExpr::Const(c) => Some(*c),
            OpExpr::ITE(c, x, y) => {
                if c.eval(env)? {
                    x.eval(env)
                } else {
                    y.eval(env)
                }
            }
            OpExpr::Ptr(_, x) => x.eval(env),
        }
    }
    pub fn eval_with_empty_env(&self) -> Option<i64> {
        self.eval(&Env::new())
    }
    /// simplifies the expression and reduce Ptr
    pub fn simplify(&self) -> Op {
        if let Some(x) = self.eval(&Env::new()) {
            return Op::mk_const(x);
        }
        match self.kind() {
            OpExpr::Op(o, x, y) => {
                let x = x.simplify();
                let y = y.simplify();
                // handle (d - (-c * y))
                if o == &OpKind::Sub {
                    match y.kind() {
                        OpExpr::Op(OpKind::Mul, a, b) => {
                            match a.eval_with_empty_env() {
                                Some(v) if v < 0 => {
                                    let v = -v;
                                    return Op::mk_bin_op(
                                        OpKind::Add,
                                        x,
                                        Op::mk_bin_op(OpKind::Mul, Op::mk_const(v), b.clone()),
                                    );
                                }
                                _ => (),
                            };
                            match b.eval_with_empty_env() {
                                Some(v) if v < 0 => {
                                    let v = -v;
                                    return Op::mk_bin_op(
                                        OpKind::Add,
                                        x,
                                        Op::mk_bin_op(OpKind::Mul, Op::mk_const(v), a.clone()),
                                    );
                                }
                                _ => (),
                            };
                        }
                        _ => (),
                    }
                }
                Op::mk_bin_op(*o, x, y)
            }
            OpExpr::ITE(c, x, y) => {
                let c = c.simplify();
                let x = x.simplify();
                let y = y.simplify();
                Op::mk_ite(c, x, y)
            }
            OpExpr::Ptr(_, x) => x.simplify(),
            OpExpr::Var(_) | OpExpr::Const(_) => self.clone(),
        }
    }
}

#[test]
fn test_op_eval() {
    let x = Ident::fresh();
    let o = Op::mk_bin_op(
        OpKind::Sub,
        Op::mk_add(Op::mk_const(5), Op::mk_var(x)),
        Op::mk_const(3),
    );
    let mut env = Env::new();
    env.add(x, 10);
    let v = o.eval(&env).unwrap();
    assert_eq!(v, 12);
}

#[test]
fn test_op_simplify() {
    let x = Ident::fresh();
    let o = Op::mk_bin_op(
        OpKind::Sub,
        Op::mk_add(Op::mk_const(5), Op::mk_const(3)),
        Op::mk_var(x),
    );
    let o2 = Op::mk_bin_op(OpKind::Sub, Op::mk_const(8), Op::mk_var(x));
    let o = o.simplify();
    assert_eq!(o, o2);
}

impl PredKind {
    pub fn eval(&self, env: &Env, args: &[Op]) -> Option<bool> {
        assert!(args.len() == 2);
        let x = args[0].eval(env)?;
        let y = args[1].eval(env)?;
        match self {
            PredKind::Eq => x == y,
            PredKind::Neq => x != y,
            PredKind::Lt => x < y,
            PredKind::Leq => x <= y,
            PredKind::Gt => x > y,
            PredKind::Geq => x >= y,
        }
        .into()
    }
    pub fn to_str(&self) -> &'static str {
        match self {
            PredKind::Eq => "=",
            PredKind::Neq => "!=",
            PredKind::Lt => "<",
            PredKind::Leq => "<=",
            PredKind::Gt => ">",
            PredKind::Geq => ">=",
        }
    }
}

impl Constraint {
    /// if Fv(self) ⊂ dom(env) and self does not contain any quantifier, then eval must return Some(v)
    pub fn eval(&self, env: &Env) -> Option<bool> {
        match self.kind() {
            ConstraintExpr::True => Some(true),
            ConstraintExpr::False => Some(false),
            ConstraintExpr::Pred(p, l) => p.eval(env, l),
            ConstraintExpr::Conj(x, y) => {
                let x = x.eval(env)?;
                let y = y.eval(env)?;
                Some(x && y)
            }
            ConstraintExpr::Disj(x, y) => {
                let x = x.eval(env)?;
                let y = y.eval(env)?;
                Some(x || y)
            }
            ConstraintExpr::Quantifier(_, _, x) => x.eval(env),
        }
    }
    pub fn eval_with_empty_env(&self) -> Option<bool> {
        self.eval(&Env::new())
    }
    pub fn simplify_trivial(&self) -> Self {
        match self.eval_with_empty_env() {
            Some(b) if b => return Constraint::mk_true(),
            Some(_) => return Constraint::mk_false(),
            _ => (),
        };
        match self.kind() {
            ConstraintExpr::Conj(x, y) => {
                let x2 = x.simplify_trivial();
                let y2 = y.simplify_trivial();
                Constraint::mk_conj(x2, y2)
            }
            ConstraintExpr::Disj(x, y) => {
                let x = x.simplify_trivial();
                let y = y.simplify_trivial();
                Constraint::mk_disj(x, y)
            }
            ConstraintExpr::Quantifier(q, x, c) => {
                let c = c.simplify_trivial();
                let fvs = c.fv();
                if !fvs.contains(&x.id) {
                    c
                } else {
                    Constraint::mk_quantifier(*q, x.clone(), c)
                }
            }
            ConstraintExpr::Pred(p, l) => match p {
                PredKind::Eq if l.len() == 2 && l[0] == l[1] => Constraint::mk_true(),
                _ => {
                    let l = l.iter().map(|o| o.simplify()).collect();
                    Constraint::mk_pred(*p, l)
                }
            },
            ConstraintExpr::True | ConstraintExpr::False => self.clone(),
        }
    }
    // o1 <= o2 && o2 <= o1 => o1 == o2
    // o1 <= o2 && o1 > o2 -> remove it and conjoin false
    fn simplify_geq_geq(&self) -> Self {
        // dnf
        let dnf = self.to_dnf();
        // too big?
        if dnf.len() > 3 {
            return self.clone();
        }
        let mut result_constraint = Constraint::mk_false();
        for clause in dnf {
            let mut geq_track = Vec::new();
            // (left, right, flag) where flag is
            // used for tracking whether left == right has already conjoined.
            let mut eqs = Vec::new();
            let cnf = clause.to_cnf();
            for c in cnf.iter() {
                let (left, right) = match c.kind() {
                    ConstraintExpr::Pred(PredKind::Geq, xs) if xs.len() == 2 => {
                        let left = xs[0].clone();
                        let right = xs[1].clone();
                        (left, right)
                    }
                    ConstraintExpr::Pred(PredKind::Leq, xs) if xs.len() == 2 => {
                        let left = xs[1].clone();
                        let right = xs[0].clone();
                        (left, right)
                    }
                    _ => continue,
                };
                let mut geq_track_new = Vec::new();
                let mut inserted = false;
                for (l, r) in geq_track.into_iter() {
                    if left == r && right == l {
                        inserted = true;
                        eqs.push((left.clone(), right.clone(), false))
                    } else if left == l && right == r {
                        // already inserted
                        inserted = true;
                    }
                }
                if !inserted {
                    geq_track_new.push((left.clone(), right.clone()));
                }
                geq_track = geq_track_new;
            }
            let mut constraint = Constraint::mk_true();
            'outer: for c in cnf {
                match c.kind() {
                    ConstraintExpr::Pred(PredKind::Geq, xs)
                    | ConstraintExpr::Pred(PredKind::Leq, xs)
                        if xs.len() == 2 =>
                    {
                        let left = &xs[0];
                        let right = &xs[1];
                        for (l, r, flag) in eqs.iter_mut() {
                            if (left == l && right == r) || (left == r && right == l) {
                                if !*flag {
                                    let c = Constraint::mk_eq(left.clone(), right.clone());
                                    constraint = Constraint::mk_conj(c, constraint);
                                    *flag = true;
                                }
                                continue 'outer;
                            }
                        }
                        // no entry in eqs
                        constraint = Constraint::mk_conj(c.clone(), constraint);
                    }
                    ConstraintExpr::Pred(PredKind::Lt, xs) if xs.len() == 2 => {
                        let left = &xs[1];
                        let right = &xs[0];
                        // left < right
                        // check if right <= left exists

                        for (l, r) in geq_track.iter() {
                            if left == r && right == l {
                                constraint = Constraint::mk_false();
                                continue 'outer;
                            }
                        }
                        for (l, r, _) in eqs.iter() {
                            if (left == l && right == r) || (left == r && right == l) {
                                constraint = Constraint::mk_false();
                                continue 'outer;
                            }
                        }
                        constraint = Constraint::mk_conj(c.clone(), constraint);
                    }
                    ConstraintExpr::Pred(PredKind::Gt, xs) if xs.len() == 2 => {
                        let left = &xs[0];
                        let right = &xs[1];
                        // left < right
                        // check if right <= left exists

                        for (l, r) in geq_track.iter() {
                            if left == r && right == l {
                                constraint = Constraint::mk_false();
                                continue 'outer;
                            }
                        }
                        for (l, r, _) in eqs.iter() {
                            if (left == l && right == r) || (left == r && right == l) {
                                constraint = Constraint::mk_false();
                                continue 'outer;
                            }
                        }
                        constraint = Constraint::mk_conj(c.clone(), constraint);
                    }
                    _ => constraint = Constraint::mk_conj(c.clone(), constraint),
                };
            }
            result_constraint = Constraint::mk_disj(result_constraint, constraint);
        }
        result_constraint
    }
    /// x > 0 /\ x <= 1 -> x = 1
    /// This function can fail if the given op is not linear.
    pub fn simplify_by_finding_eq(&self) -> Option<Constraint> {
        fn update(
            pred: PredKind,
            x: Ident,
            v: i64,
            table: &mut HashMap<Ident, (Option<i64>, Option<i64>, HashSet<i64>, HashSet<usize>)>, // [x.0, x.1], neqs, clause indices
            idx: usize, // clause index
        ) {
            let entry = table
                .entry(x)
                .or_insert((None, None, HashSet::new(), HashSet::new()));
            // check if still it's valid range.
            match entry {
                (Some(x), Some(y), _, _) if *y > *x => return,
                _ => (),
            }
            let (left, right, neqs, idxs) = entry;
            idxs.insert(idx);
            match pred {
                PredKind::Eq => {
                    match left {
                        Some(x) if *x <= v => *left = Some(v),
                        None => *left = Some(v),
                        _ => (),
                    };
                    match right {
                        Some(x) if v <= *x => *right = Some(v),
                        None => *right = Some(v),
                        _ => (),
                    }
                }
                PredKind::Neq => {
                    neqs.insert(v);
                }
                // target_var < v
                // <=> target_var <= v - 1
                // target_var <= v
                // left <= target_var <= right
                PredKind::Lt | PredKind::Leq => {
                    let v = match pred {
                        PredKind::Lt => v - 1,
                        PredKind::Leq => v,
                        _ => panic!("err"),
                    };
                    match right {
                        Some(x) if v <= *x => *right = Some(v),
                        None => *right = Some(v),
                        _ => (),
                    }
                }
                PredKind::Gt | PredKind::Geq => {
                    let v = match pred {
                        PredKind::Gt => v + 1,
                        PredKind::Geq => v,
                        _ => panic!("err"),
                    };
                    match left {
                        Some(x) if *x <= v => *left = Some(v),
                        None => *left = Some(v),
                        _ => (),
                    }
                }
            }
        }
        let (qs, c) = self.to_pnf_raw();
        let dnf = c.to_dnf();
        let mut result_constraint = Constraint::mk_false();
        for dclause in dnf {
            let cnf = dclause.to_cnf();
            // HaseMap<(Ident, (Option<i64>, Option<i64>))>
            let mut table = HashMap::new();
            for (id, clause) in cnf.iter().enumerate() {
                let fvs = clause.fv();
                if fvs.len() != 1 {
                    continue;
                }
                let target_var = *fvs.iter().next().unwrap();

                match clause.kind() {
                    ConstraintExpr::Pred(pred, l) if l.len() == 2 => {
                        let left = &l[0];
                        let right = &l[1];
                        let normalized =
                            Op::mk_sub(left.clone(), right.clone()).normalize(&vec![target_var])?;

                        if let (Some(1), Some(x)) = (
                            normalized[0].eval_with_empty_env(),
                            normalized[1].eval_with_empty_env(),
                        ) {
                            // Note that we have to transpose v so that x <pred> v
                            update(*pred, target_var, -x, &mut table, id);
                        }
                    }
                    ConstraintExpr::Pred(_, _) | ConstraintExpr::True | ConstraintExpr::False => (),
                    ConstraintExpr::Conj(_, _)
                    | ConstraintExpr::Disj(_, _)
                    | ConstraintExpr::Quantifier(_, _, _) => todo!(),
                }
            }
            // check contradiction
            let mut is_false = false;
            let mut assignment = HashMap::new();
            let mut all_indices = HashSet::new();
            for (var, (left, right, neqs, indices)) in table.iter() {
                match (left, right) {
                    (Some(left), Some(right)) if left > right => {
                        is_false = true;
                        break;
                    }
                    (Some(left), Some(right)) if left == right && !neqs.contains(left) => {
                        assignment.insert(*var, *left);
                        all_indices.extend(indices.iter().cloned())
                    }
                    (_, _) => (),
                }
            }
            if !is_false {
                let mut new_dclause = Constraint::mk_true();
                for (x, v) in assignment.into_iter() {
                    let c = Constraint::mk_eq(Op::mk_var(x), Op::mk_const(v));
                    new_dclause = Constraint::mk_conj(c, new_dclause);
                }
                for (id, clause) in cnf.iter().enumerate() {
                    if !all_indices.contains(&id) {
                        new_dclause = Constraint::mk_conj(new_dclause, clause.clone());
                    }
                }

                result_constraint = Constraint::mk_disj(result_constraint, new_dclause);
            }
        }

        for (q, v) in qs {
            result_constraint = Constraint::mk_quantifier(q, v, result_constraint);
        }
        Some(result_constraint)
    }
    /// simplifies the same clause in cnf/dnf
    ///
    /// Examples
    /// - x = y /\ x + 1 = y \/ x = y /\ x + 1 = y ---> x = y /\ x + 1 = y
    /// - x = y /\ x = y \/ x = y /\ x = y ---> x = y
    fn simplify_same_clause(&self) -> Self {
        let (qs, pnf) = self.to_pnf_raw();

        let mut dclauses = Vec::new();
        let mut dnf = pnf.to_dnf();
        dnf.sort_by(|x, y| format!("{x}").cmp(&format!("{y}")));

        for dclause in dnf {
            let mut clauses = Vec::new();
            for clause in dclause.to_cnf() {
                // if clause has already been in dclauses, we only have to consider the case where
                // clause does not hold; i.e., we do not have to disjoin `dclause` further, so
                // just assume it as false.
                if dclauses.iter().find(|&c| c == &clause).is_some() {
                    clauses = vec![Constraint::mk_false()];
                    break;
                }
                if clauses.iter().find(|&c| c == &clause).is_none() {
                    clauses.push(clause.clone());
                }
            }
            clauses.sort_by(|x, y| format!("{x}").cmp(&format!("{y}")));
            let constraint = clauses
                .into_iter()
                .fold(Constraint::mk_true(), |x, y| Constraint::mk_conj(x, y));
            if dclauses.iter().find(|&c| c == &constraint).is_none() {
                dclauses.push(constraint.clone());
            }
        }
        dclauses.sort_by(|x, y| format!("{x}").cmp(&format!("{y}")));
        let mut result_constraint = dclauses
            .into_iter()
            .fold(Constraint::mk_false(), |x, y| Constraint::mk_disj(x, y));
        for (q, v) in qs {
            result_constraint = Constraint::mk_quantifier(q, v, result_constraint);
        }
        result_constraint
    }
    pub fn simplify(&self) -> Self {
        let c = self.simplify_trivial();
        let c = c.simplify_geq_geq();
        // skip if it fails
        let c = c.simplify_by_finding_eq().unwrap_or(c.clone());
        let c = c.simplify_trivial();
        let c = c.simplify_same_clause();
        c
    }
}

#[test]
fn test_simplify_geq_geq() {
    // x <= y && y +1 = 0 && y <= x
    let x = Ident::fresh();
    let y = Ident::fresh();
    let xgy = Constraint::mk_leq(Op::mk_var(x), Op::mk_var(y));
    let yp10 = Constraint::mk_eq(Op::mk_inc(Op::mk_var(y)), Op::zero());
    let ygx = Constraint::mk_leq(Op::mk_var(y), Op::mk_var(x));
    let c = Constraint::mk_conj(Constraint::mk_conj(xgy.clone(), yp10.clone()), ygx.clone());
    println!("before: {c}");
    let c = c.simplify_geq_geq();
    println!("after: {c}");
    let cnf = c.to_cnf();
    assert_eq!(cnf.len(), 2);

    // (x <= y \/ y + 1 = 0) /\ y <= x
    let c = Constraint::mk_conj(Constraint::mk_disj(xgy.clone(), yp10.clone()), ygx.clone());
    println!("before: {c}");
    let c = c.simplify_geq_geq();
    println!("after: {c}");
    let dnf = c.to_dnf();
    let mut existence = false;
    for clause in dnf {
        let cnf = clause.to_cnf();
        if cnf.len() == 1 {
            existence = true;
            assert_eq!(&cnf[0], &Constraint::mk_eq(Op::mk_var(x), Op::mk_var(y)));
        }
    }
    assert!(existence);
    // (x <= y \/ y + 1 = 0) /\ x > y
    let ygtx = Constraint::mk_gt(Op::mk_var(x), Op::mk_var(y));
    let c = Constraint::mk_conj(Constraint::mk_disj(xgy.clone(), yp10.clone()), ygtx.clone());
    println!("before: {c}");
    let c = c.simplify_geq_geq();
    println!("after: {c}");
    let dnf = c.to_dnf();
    assert_eq!(dnf.len(), 1);
    assert_eq!(dnf[0].to_cnf().len(), 2);
}

#[test]
fn test_simplify_by_finding_eq() {
    // x > 0 /\ x <= 1 /\ y = x => y = 1 /\ x = 1
    let x = Ident::fresh();
    let y = Ident::fresh();
    let xz = Constraint::mk_gt(Op::mk_var(x), Op::zero());
    let x1 = Constraint::mk_leq(Op::mk_var(x), Op::one());
    let yx = Constraint::mk_eq(Op::mk_var(x), Op::mk_var(y));
    let c = Constraint::mk_conj(Constraint::mk_conj(xz, x1), yx);
    println!("before {c}");
    let c = c.simplify_by_finding_eq().unwrap();
    println!("after {c}");
    let c = c.simplify();
    println!("simplified {c}");
    assert_eq!(c.to_cnf().len(), 2);

    // x > 0 /\ x <= 2 /\ y = x does not change
    let xz = Constraint::mk_gt(Op::mk_var(x), Op::zero());
    let x1 = Constraint::mk_leq(Op::mk_var(x), Op::mk_const(2));
    let yx = Constraint::mk_eq(Op::mk_var(x), Op::mk_var(y));
    let c = Constraint::mk_conj(Constraint::mk_conj(xz, x1), yx);
    println!("before {c}");
    let c = c.simplify_by_finding_eq().unwrap();
    println!("after {c}");
    let c = c.simplify();
    println!("simplified {c}");
    assert_eq!(c.to_cnf().len(), 3);

    // x > 0 /\ x = 0 /\ y = x does not change
    let mut e = Env::new();
    e.add(x, 5);
    e.add(y, 8);
    let xz = Constraint::mk_gt(Op::mk_var(x), Op::zero());
    let x1 = Constraint::mk_eq(Op::mk_var(x), Op::mk_const(0));
    let yx = Constraint::mk_eq(Op::mk_var(x), Op::mk_var(y));
    let c = Constraint::mk_conj(Constraint::mk_conj(xz, x1), yx);
    println!("before {c}");
    let c = c.simplify_by_finding_eq().unwrap();
    println!("after {c}");
    let c = c.simplify();
    println!("simplified {c}");
    assert!(!c.eval(&e).unwrap());

    // y >= 0 /\ x = 0 /\ y = x -> y >= 0 /\ y = 0 /\ x = 0
    let xz = Constraint::mk_geq(Op::mk_var(y), Op::zero());
    let x1 = Constraint::mk_eq(Op::mk_var(x), Op::mk_const(0));
    let yx = Constraint::mk_eq(Op::mk_var(x), Op::mk_var(y));
    let c = Constraint::mk_conj(Constraint::mk_conj(xz, x1), yx);
    println!("before {c}");
    let c = c.simplify_by_finding_eq().unwrap();
    println!("after {c}");
    let c = c.simplify();
    println!("simplified {c}");
    assert_eq!(c.to_cnf().len(), 3);

    // x < 1 /\ x >= 0 /\ y = x => y = 1 /\ x = 0
    let xz = Constraint::mk_lt(Op::mk_var(x), Op::one());
    let x1 = Constraint::mk_geq(Op::mk_var(x), Op::zero());
    let yx = Constraint::mk_eq(Op::mk_var(x), Op::mk_var(y));
    let c_ = Constraint::mk_conj(Constraint::mk_conj(xz, x1), yx);
    println!("before {c}");
    let c = c_.simplify_by_finding_eq().unwrap();
    println!("after {c}");
    let c = c.simplify();
    println!("simplified {c}");
    assert_eq!(c.to_cnf().len(), 2);

    // x < 1 /\ x >= 0 /\ y = x /\ x != 0 does not change
    let yx = Constraint::mk_neq(Op::mk_var(x), Op::zero());
    let c = Constraint::mk_conj(c_, yx);
    println!("before {c}");
    let c = c.simplify_by_finding_eq().unwrap();
    println!("after {c}");
    let c = c.simplify();
    println!("simplified {c}");
    assert_eq!(c.to_cnf().len(), 4);
}

#[test]
fn test_constraint_eval() {
    let x = Ident::fresh();
    let o = Op::mk_bin_op(
        OpKind::Sub,
        Op::mk_add(Op::mk_const(5), Op::mk_var(x)),
        Op::mk_const(3),
    );
    let c = Constraint::mk_eq(o.clone(), Op::mk_const(12));
    let mut env = Env::new();
    env.add(x, 10);
    let v = c.eval(&env).unwrap();
    assert!(v);

    let c = Constraint::mk_conj(
        Constraint::mk_false(),
        Constraint::mk_eq(o, Op::mk_const(12)),
    );
    let v = c.eval(&env).unwrap();
    assert!(!v);
}
#[test]
fn test_constraint_simplify() {
    let x = Ident::fresh();
    let o = Op::mk_bin_op(
        OpKind::Sub,
        Op::mk_add(Op::mk_const(5), Op::mk_const(3)),
        Op::mk_var(x),
    );
    let o2 = Op::mk_bin_op(OpKind::Sub, Op::mk_const(8), Op::mk_var(x));
    let o = o.simplify();

    let c = Constraint::mk_eq(o.clone(), Op::mk_const(12));
    let c2 = Constraint::mk_eq(o2.clone(), Op::mk_const(12));
    let c = c.simplify_trivial();
    assert_eq!(c, c2);

    let c = Constraint::mk_quantifier_int(
        QuantifierKind::Universal,
        Ident::fresh(),
        Constraint::mk_eq(o2.clone(), Op::mk_const(12)),
    );
    let c2 = Constraint::mk_eq(o2.clone(), Op::mk_const(12));
    let c = c.simplify_trivial();
    assert_eq!(c, c2);

    let lhs = Constraint::mk_eq(Op::mk_var(Ident::fresh()), Op::mk_const(0));
    let c = Constraint::mk_conj(lhs.clone(), Constraint::mk_eq(o.clone(), Op::mk_const(12)));
    let c2 = Constraint::mk_conj(lhs, Constraint::mk_eq(o2.clone(), Op::mk_const(12)));
    assert_eq!(c, c2);
}

#[test]
fn test_simplify_same_clause() {
    // x = y /\ x + 1 = y \/ x = y /\ x + 1 = y
    let x = Ident::fresh();
    let y = Ident::fresh();

    let xeqy = Constraint::mk_eq(Op::mk_var(x), Op::mk_var(y));
    let xp1eqy = Constraint::mk_eq(Op::mk_inc(Op::mk_var(x)), Op::mk_var(y));
    let c1 = Constraint::mk_conj(xeqy.clone(), xp1eqy.clone());
    let c2 = Constraint::mk_disj(c1.clone(), c1.clone());
    println!("before c2: {c2}");
    let c3 = c2.simplify_same_clause();
    println!("after c3: {c3}");
    assert_eq!(c3.to_dnf().len(), 1);

    // x = y /\ x + 1 = y \/ x = y /\ y + 1 = x
    let yp1eqx = Constraint::mk_eq(Op::mk_inc(Op::mk_var(y)), Op::mk_var(x));
    let c4 = Constraint::mk_conj(xeqy.clone(), yp1eqx.clone());
    let c5 = Constraint::mk_disj(c1.clone(), c4.clone());
    println!("before c5: {c5}");
    let c6 = c5.simplify_same_clause();
    println!("after c6: {c6}");
    assert_eq!(c6.to_dnf().len(), 2);

    // x = y /\ x = y \/ x = y /\ x = y
    let c7 = Constraint::mk_conj(xeqy.clone(), xeqy.clone());
    let c8 = Constraint::mk_disj(c7.clone(), c7.clone());
    println!("before c8: {c8}");
    let c9 = c8.simplify_same_clause();
    println!("after c9: {c9}");
    let dnf = c9.to_dnf();
    assert_eq!(dnf.len(), 1);
    assert_eq!(dnf[0].to_cnf().len(), 1);

    // x = y /\ x + 1 = y \/ y + 1 = x /\ x = y
    let c10 = Constraint::mk_conj(xp1eqy.clone(), xeqy.clone());
    let c_bef = Constraint::mk_disj(c1.clone(), c10.clone());
    println!("before c_bef: {c_bef}");
    let c_aft = c_bef.simplify_same_clause();
    println!("after c_aft: {c_aft}");
    let dnf = c_aft.to_dnf();
    assert_eq!(dnf.len(), 1);
    assert_eq!(dnf[0].to_cnf().len(), 2);

    // (x = y /\ x + 1 = y) \/ x = y \/ x + 1 = y
    let c11 = Constraint::mk_disj(xeqy.clone(), xp1eqy.clone());
    let c12 = Constraint::mk_disj(c11.clone(), c1.clone());
    let c_bef = c12.clone();
    println!("before : {c_bef}");
    let c_aft = c_bef.simplify_same_clause();
    println!("after c_aft: {c_aft}");
    let dnf = c_aft.to_dnf();
    assert_eq!(dnf.len(), 2);
    for c in dnf {
        assert_eq!(c.to_cnf().len(), 1);
    }
}

// // Generate Template with the configuration
// pub trait GreedyInstantiation<T> {
//     type SeedType: Subst<Id=Ident, Item=Op> + Clone;
//     fn subst_greedy(seed: SeedType, candidates: Vec<SeedType>) -> Self;
//     fn scope_variable(seed: &SeedType) -> HashSet<Ident>;
//     fn greedy_instantiate(seed: SeedType, scope_ints: &HashSet<Ident>) -> Self {
//         let mut fvs = Self::scope_variable(&seed);
//
//         debug!("fvs: {:?}", fvs);
//         debug!("ints: {:?}", scope_ints);
//
//         let mut patterns: Vec<Op> = Vec::new();
//         for int in scope_ints.iter() {
//             let o = Op::mk_var(*int);
//             if scope_ints.len() < 4 {
//                 for i in 0..patterns.len() {
//                     patterns.push(Op::mk_add(patterns[i].clone(), o.clone()));
//                 }
//             }
//             patterns.push(o);
//         }
//         patterns.push(Op::mk_const(0));
//
//         // instantiate fvs by ints
//         let mut gs = vec![seed.clone()];
//         for fv in fvs
//             .into_iter()
//             .map(|fv| )
//         {
//             let mut new_gs = Vec::new();
//             for op in patterns.iter() {
//                 for g in gs.iter() {
//                     if new_gs.len() > 100000 {
//                         panic!("explosion")
//                     }
//                     new_gs.push(g.subst(&fv, op));
//                 }
//             }
//             gs = new_gs;
//         }
//         assert!(gs.len() > 0);
//         Self::subst_greedy(seed, gs)
//         unimplemented!()
//     }
// }

impl From<crate::parse::Expr> for Constraint {
    fn from<'a>(e: crate::parse::Expr) -> Self {
        fn op<'a>(
            e: &'a crate::parse::Expr,
            env: &mut std::collections::HashMap<&'a String, Ident>,
        ) -> Op {
            match e.kind() {
                ExprKind::Var(v) => Op::mk_var(*env.get(v).unwrap()),
                ExprKind::Num(n) => Op::mk_const(*n),
                ExprKind::Op(o, x, y) => Op::mk_bin_op(*o, op(x, env), op(y, env)),
                _ => panic!("fatal"),
            }
        }
        fn go<'a>(
            e: &'a crate::parse::Expr,
            env: &mut std::collections::HashMap<&'a String, Ident>,
        ) -> Constraint {
            match e.kind() {
                ExprKind::True => Constraint::mk_true(),
                ExprKind::False => Constraint::mk_false(),
                ExprKind::Pred(p, x, y) => Constraint::mk_pred(*p, vec![op(x, env), op(y, env)]),
                ExprKind::And(x, y) => Constraint::mk_conj(go(x, env), go(y, env)),
                ExprKind::Or(x, y) => Constraint::mk_disj(go(x, env), go(y, env)),
                ExprKind::Univ(x, e) => {
                    let id = Ident::fresh();
                    let old = env.insert(x, id);
                    let c = Constraint::mk_univ_int(id, go(e, env));
                    match old {
                        Some(old) => assert!(env.insert(x, old).is_some()),
                        None => (),
                    }
                    c
                }
                ExprKind::Exist(_, _) => unimplemented!(),
                _ => panic!("fatal"),
            }
        }
        let fvs = e.fv();
        let mut env = std::collections::HashMap::new();
        for fv in fvs.iter() {
            let id = Ident::fresh();
            env.insert(fv, id);
        }
        go(&e, &mut env)
    }
}

/// TexPrint is inteded
pub trait TeXFormat {
    fn tex_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error>;
}

pub struct TeXPrinter<'a> {
    item: &'a dyn TeXFormat,
}

#[allow(non_snake_case)]
pub fn TeXPrinter<'a>(item: &'a dyn TeXFormat) -> TeXPrinter<'a> {
    TeXPrinter { item }
}

impl<'a> fmt::Display for TeXPrinter<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.item.tex_fmt(f)
    }
}

impl TeXFormat for Ident {
    fn tex_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "x_{{ {} }}", self.id)
    }
}

impl TeXFormat for OpKind {
    fn tex_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        let op = match self {
            OpKind::Add => " + ",
            OpKind::Sub => " - ",
            OpKind::Mul => r" \times ",
            OpKind::Div => r" \slash ",
            OpKind::Mod => r" \% ",
        };
        write!(f, "{op}")
    }
}

impl TeXFormat for Op {
    fn tex_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self.kind() {
            OpExpr::Op(o, o1, o2) => {
                write!(
                    f,
                    "({} {} {})",
                    TeXPrinter(o1),
                    TeXPrinter(o),
                    TeXPrinter(o2)
                )
            }
            OpExpr::Var(x) => {
                write!(f, " {} ", TeXPrinter(x))
            }
            OpExpr::Const(c) => {
                write!(f, " {c} ")
            }
            OpExpr::Ptr(_, o) => write!(f, "{}", TeXPrinter(o)),
            OpExpr::ITE(_, _, _) => unimplemented!(),
        }
    }
}
impl TeXFormat for PredKind {
    fn tex_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(
            f,
            "{}",
            match self {
                PredKind::Eq => "=",
                PredKind::Neq => r"\neq",
                PredKind::Lt => "<",
                PredKind::Leq => r"\leq",
                PredKind::Gt => r">",
                PredKind::Geq => r"\geq",
            }
        )
    }
}

impl TeXFormat for QuantifierKind {
    fn tex_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            QuantifierKind::Universal => write!(f, "\\forall"),
            QuantifierKind::Existential => write!(f, "\\exists"),
        }
    }
}
impl TeXFormat for Variable {
    fn tex_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}: {}", TeXPrinter(&self.id), TeXPrinter(&self.ty))
    }
}

impl TeXFormat for Constraint {
    fn tex_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self.kind() {
            ConstraintExpr::True => write!(f, r"\true"),
            ConstraintExpr::False => write!(f, r"\false"),
            ConstraintExpr::Pred(p, l) if l.len() == 2 => write!(
                f,
                "({} {} {})",
                TeXPrinter(&l[0]),
                TeXPrinter(p),
                TeXPrinter(&l[1])
            ),
            ConstraintExpr::Pred(p, l) => {
                write!(f, "({p})(")?;
                for x in l.iter() {
                    write!(f, "{},", TeXPrinter(x))?;
                }
                Ok(())
            }
            ConstraintExpr::Conj(x, y) => {
                write!(f, "({} \\land {})", TeXPrinter(x), TeXPrinter(y))
            }
            ConstraintExpr::Disj(x, y) => {
                write!(f, "({} \\lor {})", TeXPrinter(x), TeXPrinter(y))
            }
            ConstraintExpr::Quantifier(q, x, c) => {
                write!(
                    f,
                    "({} {}. {})",
                    TeXPrinter(q),
                    TeXPrinter(x),
                    TeXPrinter(c)
                )
            }
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub enum PrecedenceKind {
    Sequential, // for ml
    If,         // for ml
    Disj,
    Conj,
    Not,
    Pred, // PredKind operators
    Add,  // +, -
    Mul,  // *, /, %
    Abs,
    App,
    Atom,
}

pub trait Precedence {
    fn precedence(&self) -> PrecedenceKind;
}

impl Precedence for OpKind {
    fn precedence(&self) -> PrecedenceKind {
        match self {
            OpKind::Add => PrecedenceKind::Add,
            OpKind::Sub => PrecedenceKind::Add,
            OpKind::Mul => PrecedenceKind::Mul,
            OpKind::Div => PrecedenceKind::Mul,
            OpKind::Mod => PrecedenceKind::Mul,
        }
    }
}

impl Precedence for Op {
    fn precedence(&self) -> PrecedenceKind {
        match self.kind() {
            OpExpr::Op(opkind, _, _) => opkind.precedence(),
            OpExpr::Var(_) | OpExpr::Const(_) => PrecedenceKind::Atom,
            OpExpr::ITE(_, _, _) => PrecedenceKind::If,
            OpExpr::Ptr(_, o) => o.precedence(),
        }
    }
}

impl Precedence for Constraint {
    fn precedence(&self) -> PrecedenceKind {
        match self.kind() {
            ConstraintExpr::True | ConstraintExpr::False => PrecedenceKind::Atom,
            ConstraintExpr::Pred(_, _) => PrecedenceKind::Pred,
            ConstraintExpr::Conj(_, _) => PrecedenceKind::Conj,
            ConstraintExpr::Disj(_, _) => PrecedenceKind::Disj,
            ConstraintExpr::Quantifier(_, _, _) => PrecedenceKind::Abs,
        }
    }
}

////// expand ite
/// x = if y > 0 then 1 else 0 ===> (y > 0 /\ x = 1) \/ (y <= 0 /\ x = 0)
pub fn expand_ite_op(op: &Op) -> Option<(Constraint, Op, Op)> {
    match op.kind() {
        crate::formula::OpExpr::ITE(c, x, y) => Some((c.clone(), x.clone(), y.clone())),
        OpExpr::Op(o, o1, o2) => match expand_ite_op(o1) {
            Some((c, x, y)) => Some((
                c,
                Op::mk_bin_op(*o, x, o2.clone()),
                Op::mk_bin_op(*o, y, o2.clone()),
            )),
            None => {
                let (c, x, y) = expand_ite_op(o2)?;
                Some((
                    c,
                    Op::mk_bin_op(*o, o1.clone(), x),
                    Op::mk_bin_op(*o, o1.clone(), y),
                ))
            }
        },
        OpExpr::Var(_) | OpExpr::Const(_) => None,
        OpExpr::Ptr(_, _) => panic!("program error"),
    }
}

pub fn expand_ite_constr_once(c: &Constraint) -> Constraint {
    match c.kind() {
        ConstraintExpr::True | ConstraintExpr::False => c.clone(),
        ConstraintExpr::Pred(p, l) => {
            for (i, o) in l.iter().enumerate() {
                if let Some((c, x, y)) = expand_ite_op(o) {
                    let mut l1 = l.clone();
                    l1[i] = x;
                    let c1 = Constraint::mk_conj(c.clone(), Constraint::mk_pred(*p, l1));

                    let mut l2 = l.clone();
                    l2[i] = y;
                    let c2 = Constraint::mk_conj(c.negate().unwrap(), Constraint::mk_pred(*p, l2));
                    return Constraint::mk_disj(c1, c2);
                }
            }
            c.clone()
        }
        ConstraintExpr::Conj(c1, c2) => {
            let c1 = expand_ite_constr_once(c1);
            let c2 = expand_ite_constr_once(c2);
            Constraint::mk_conj(c1, c2)
        }
        ConstraintExpr::Disj(c1, c2) => {
            let c1 = expand_ite_constr_once(c1);
            let c2 = expand_ite_constr_once(c2);
            Constraint::mk_disj(c1, c2)
        }
        ConstraintExpr::Quantifier(q, v, c) => {
            let c = expand_ite_constr_once(c);
            Constraint::mk_quantifier(*q, v.clone(), c)
        }
    }
}

pub fn expand_ite_constr(mut c: Constraint) -> Constraint {
    loop {
        let c2 = expand_ite_constr_once(&c);
        if c == c2 {
            break c;
        } else {
            println!("{} ==> {}", c, c2);
            c = c2;
        }
    }
}
