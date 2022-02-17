use crate::formula::ty::Type;
use crate::formula::{Bot, Constraint, Fv, Ident, Op, Top, Variable};
use crate::util::P;
use std::fmt;

#[derive(Debug)]
pub enum ConstKind {
    Int(i64),
}

pub type Const = P<ConstKind>;

impl fmt::Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ConstKind::*;
        match self.kind() {
            Int(i) => write!(f, "{}", i),
        }
    }
}

impl Const {
    pub fn mk_int(v: i64) -> Const {
        Const::new(ConstKind::Int(v))
    }
    pub fn is_int(&self) -> bool {
        use ConstKind::*;
        match self.kind() {
            Int(_) => true,
        }
    }
    pub fn int(&self) -> i64 {
        use ConstKind::*;
        match self.kind() {
            Int(x) => *x,
        }
    }
}

#[derive(Debug)]
pub enum GoalKind<C> {
    Constr(C),
    Op(Op),
    Var(Ident),
    Abs(Variable, Goal<C>),
    App(Goal<C>, Goal<C>),
    Conj(Goal<C>, Goal<C>),
    Disj(Goal<C>, Goal<C>),
    Univ(Variable, Goal<C>),
}

pub type Goal<C> = P<GoalKind<C>>;

impl<C: fmt::Display> fmt::Display for Goal<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use GoalKind::*;
        match self.kind() {
            Constr(c) => write!(f, "{}", c),
            Op(o) => write!(f, "{}", o),
            Var(x) => write!(f, "{}", x),
            App(x, y) => write!(f, "{} {}", x, y),
            Conj(x, y) => write!(f, "({} & {})", x, y),
            Disj(x, y) => write!(f, "({} | {})", x, y),
            Univ(x, y) => write!(f, "∀{}.{}", x, y),
            Abs(x, y) => write!(f, "\\{}.{}", x, y),
        }
    }
}
impl<C: Top> Top for Goal<C> {
    fn mk_true() -> Self {
        Goal::mk_constr(C::mk_true())
    }

    fn is_true(&self) -> bool {
        match self.kind() {
            GoalKind::Constr(c) if c.is_true() => true,
            _ => false,
        }
    }
}
impl<C: Bot> Bot for Goal<C> {
    fn mk_false() -> Self {
        Goal::mk_constr(C::mk_false())
    }

    fn is_false(&self) -> bool {
        match self.kind() {
            GoalKind::Constr(c) if c.is_false() => true,
            _ => false,
        }
    }
}
impl From<Constraint> for Goal<Constraint> {
    fn from(c: Constraint) -> Self {
        Goal::mk_constr(c)
    }
}

impl<C> Goal<C> {
    pub fn mk_constr(x: C) -> Goal<C> {
        Goal::new(GoalKind::Constr(x))
    }
    pub fn mk_app(lhs: Goal<C>, rhs: Goal<C>) -> Goal<C> {
        Goal::new(GoalKind::App(lhs, rhs))
    }
    pub fn mk_var(ident: Ident) -> Goal<C> {
        Goal::new(GoalKind::Var(ident))
    }
    pub fn mk_univ(x: Variable, g: Goal<C>) -> Goal<C> {
        Goal::new(GoalKind::Univ(x, g))
    }
    pub fn mk_abs(x: Variable, g: Goal<C>) -> Goal<C> {
        Goal::new(GoalKind::Abs(x, g))
    }
    pub fn mk_op(op: Op) -> Goal<C> {
        Goal::new(GoalKind::Op(op))
    }
}
impl<C: Top> Goal<C> {
    pub fn mk_conj(lhs: Goal<C>, rhs: Goal<C>) -> Goal<C> {
        if lhs.is_true() {
            rhs
        } else if rhs.is_true() {
            lhs
        } else {
            Goal::new(GoalKind::Conj(lhs, rhs))
        }
    }
    pub fn mk_disj(lhs: Goal<C>, rhs: Goal<C>) -> Goal<C> {
        if lhs.is_true() {
            lhs
        } else if rhs.is_true() {
            rhs
        } else {
            Goal::new(GoalKind::Disj(lhs, rhs))
        }
    }
}
impl<C: Bot + Top> Goal<C> {
    pub fn mk_ho_disj(fmls: impl IntoIterator<Item = Goal<C>>, mut sty: Type) -> Goal<C> {
        let mut vs = Vec::new();
        loop {
            sty = match sty.kind() {
                super::TypeKind::Proposition => break,
                super::TypeKind::Arrow(t, s) => {
                    vs.push(Variable::mk(Ident::fresh(), t.clone()));
                    s.clone()
                }
                super::TypeKind::Integer => panic!("program error"),
            };
        }
        let mut x = Goal::mk_false();
        for f in fmls {
            let mut fml = f;
            for v in vs.iter() {
                fml = Goal::mk_app(fml, Goal::mk_var(v.id));
            }
            x = Goal::mk_disj(x, fml);
        }
        for v in vs.iter().rev() {
            x = Goal::mk_abs(v.clone(), x);
        }
        x
    }
}

#[derive(Debug)]
pub struct Clause<C> {
    pub body: Goal<C>,
    pub head: Variable,
    // pub fixpoint: Fixpoint
}

impl<C: Fv<Id = Ident>> Fv for Goal<C> {
    type Id = Ident;

    fn fv_with_vec(&self, fvs: &mut std::collections::HashSet<Self::Id>) {
        match self.kind() {
            GoalKind::Var(x) => {
                fvs.insert(*x);
            }
            GoalKind::App(x, y) => {
                x.fv_with_vec(fvs);
                y.fv_with_vec(fvs);
            }
            GoalKind::Constr(c) => c.fv_with_vec(fvs),
            GoalKind::Op(o) => o.fv_with_vec(fvs),
            GoalKind::Conj(x, y) | GoalKind::Disj(x, y) => {
                x.fv_with_vec(fvs);
                y.fv_with_vec(fvs);
            }
            GoalKind::Univ(x, c) | GoalKind::Abs(x, c) => {
                c.fv_with_vec(fvs);
                fvs.remove(&x.id);
            }
        }
    }
}

impl<C: Fv<Id = Ident>> Fv for Clause<C> {
    type Id = Ident;

    fn fv_with_vec(&self, fvs: &mut std::collections::HashSet<Self::Id>) {
        self.body.fv_with_vec(fvs);
    }
}

impl<C: fmt::Display> fmt::Display for Clause<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ", self.head)?;
        write!(f, "= {}", self.body)
    }
}

#[derive(Debug)]
pub struct Problem<C> {
    pub clauses: Vec<Clause<C>>,
    pub top: Goal<C>,
}

impl<C: fmt::Display> fmt::Display for Problem<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "toplevel: {}", &self.top)?;
        for c in self.clauses.iter() {
            writeln!(f, "- {}", c)?;
        }
        fmt::Result::Ok(())
    }
}

impl<C> Clause<C> {
    pub fn new(body: Goal<C>, head: Variable) -> Clause<C> {
        Clause { body, head }
    }
    pub fn new_top_clause(body: Goal<C>) -> Clause<C> {
        let head = Variable::fresh_prop();
        Clause { body, head }
    }
}
