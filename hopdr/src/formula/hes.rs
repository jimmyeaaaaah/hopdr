use crate::formula::ty::Type;
use crate::formula::{Bot, Constraint, Fv, Ident, Logic, Op, Rename, Top, Variable};
use crate::pdr::rtype::Refinement;
use crate::util::P;
use std::collections::HashSet;
use std::fmt;

use super::{fofml, Subst};

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
            Constr(c) => write!(f, "({})", c),
            Op(o) => write!(f, "({})", o),
            Var(x) => write!(f, "{}", x),
            App(x, y) => write!(f, "[{} {}]", x, y),
            Conj(x, y) => write!(f, "({} & {})", x, y),
            Disj(x, y) => write!(f, "({} | {})", x, y),
            Univ(x, y) => write!(f, "(∀{}.{})", x, y),
            Abs(x, y) => write!(f, "(\\{}.{})", x, y),
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
impl<C> From<C> for Goal<C> {
    fn from(c: C) -> Self {
        Goal::mk_constr(c)
    }
}

impl From<Goal<Constraint>> for Constraint {
    // even though g has type *, and it can be beta-reduced to a constraint,
    // we cannot convert g to the constraint.
    // This is a naive way of translating Goal to Constraint.
    fn from(g: Goal<Constraint>) -> Self {
        match g.kind() {
            GoalKind::Constr(c) => c.clone(),
            GoalKind::Conj(g1, g2) => {
                let c1 = g1.clone().into();
                let c2 = g2.clone().into();
                Constraint::mk_conj(c1, c2)
            }
            GoalKind::Disj(g1, g2) => {
                let c1 = g1.clone().into();
                let c2 = g2.clone().into();
                Constraint::mk_disj(c1, c2)
            }
            GoalKind::Univ(x, g) => {
                let c = g.clone().into();
                Constraint::mk_quantifier_int(super::QuantifierKind::Universal, x.id, c)
            }
            GoalKind::Op(_) | GoalKind::Var(_) | GoalKind::Abs(_, _) | GoalKind::App(_, _) => {
                panic!("program error: {} cannot be translated to Constraint", g)
            }
        }
    }
}
impl<C> From<Goal<C>> for Op {
    fn from(g: Goal<C>) -> Self {
        match g.kind() {
            GoalKind::Op(o) => o.clone(),
            GoalKind::Var(x) => Op::mk_var(*x),
            GoalKind::Constr(_)
            | GoalKind::Abs(_, _)
            | GoalKind::App(_, _)
            | GoalKind::Conj(_, _)
            | GoalKind::Disj(_, _)
            | GoalKind::Univ(_, _) => panic!("program error"),
        }
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
impl<C> Goal<C> {
    pub fn mk_conj(lhs: Goal<C>, rhs: Goal<C>) -> Goal<C> {
        Goal::new(GoalKind::Conj(lhs, rhs))
    }
    pub fn is_conj(&self) -> bool {
        match self.kind() {
            GoalKind::Conj(_, _) => true,
            _ => false,
        }
    }
    pub fn mk_disj(lhs: Goal<C>, rhs: Goal<C>) -> Goal<C> {
        Goal::new(GoalKind::Disj(lhs, rhs))
    }
    pub fn is_disj(&self) -> bool {
        match self.kind() {
            GoalKind::Disj(_, _) => true,
            _ => false,
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

impl<C: Fv<Id = Ident>> Fv for Goal<C> {
    type Id = Ident;

    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>) {
        match self.kind() {
            GoalKind::Var(x) => {
                fvs.insert(*x);
            }
            GoalKind::Univ(x, g) | GoalKind::Abs(x, g) => {
                g.fv_with_vec(fvs);
                fvs.remove(&x.id);
            }
            GoalKind::App(g1, g2) | GoalKind::Conj(g1, g2) | GoalKind::Disj(g1, g2) => {
                g1.fv_with_vec(fvs);
                g2.fv_with_vec(fvs);
            }
            GoalKind::Constr(c) => c.fv_with_vec(fvs),
            GoalKind::Op(op) => op.fv_with_vec(fvs),
        }
    }
}
impl<C: Rename> Rename for Goal<C> {
    fn rename(&self, x: &Ident, y: &Ident) -> Self {
        match self.kind() {
            GoalKind::Constr(c) => Goal::mk_constr(c.rename(x, y)),
            GoalKind::Op(op) => Goal::mk_op(op.rename(x, y)),
            GoalKind::Var(id) => Goal::mk_var(if id == x { *y } else { *id }),
            GoalKind::Abs(id, g) => {
                let g = if &id.id != x {
                    g.rename(x, y)
                } else {
                    g.clone()
                };
                Goal::mk_abs(id.clone(), g)
            }
            GoalKind::Univ(id, g) => {
                let g = if &id.id != x {
                    g.rename(x, y)
                } else {
                    g.clone()
                };
                Goal::mk_univ(id.clone(), g)
            }
            GoalKind::App(g1, g2) => Goal::mk_app(g1.rename(x, y), g2.rename(x, y)),
            GoalKind::Conj(g1, g2) => Goal::mk_conj(g1.rename(x, y), g2.rename(x, y)),
            GoalKind::Disj(g1, g2) => Goal::mk_disj(g1.rename(x, y), g2.rename(x, y)),
        }
    }
}

impl<C: Subst<Item = Op, Id = Ident> + Rename + Fv<Id = Ident> + fmt::Display> Subst for Goal<C> {
    type Item = Goal<C>;
    type Id = Variable;
    // we assume formula has already been alpha-renamed
    // TODO: where? We will not assume alpha-renamed
    fn subst(&self, x: &Variable, v: &Goal<C>) -> Self {
        fn subst_inner<C: Subst<Item = Op, Id = Ident> + Rename + fmt::Display>(
            target: &Goal<C>,
            x: &Variable,
            v: &Goal<C>,
            fv: &HashSet<Ident>,
        ) -> Goal<C> {
            // tmp debug
            //debug!("subst_inner: [{}/{}]{}", v, x, target);
            match target.kind() {
                GoalKind::Var(y) => {
                    if x.id == *y {
                        v.clone()
                    } else {
                        target.clone()
                    }
                }
                GoalKind::Constr(c) if x.ty.is_int() => {
                    // when x has type int, v can be reduced to Op
                    let op = v.clone().into();
                    let c = c.subst(&x.id, &op);
                    Goal::mk_constr(c)
                }
                GoalKind::Op(o) if x.ty.is_int() => {
                    let op = v.clone().into();
                    let o = o.subst(&x.id, &op);
                    Goal::mk_op(o)
                }
                GoalKind::Constr(_) | GoalKind::Op(_) => target.clone(),
                GoalKind::App(g1, g2) => {
                    let g1 = subst_inner(g1, x, v, fv);
                    let g2 = subst_inner(g2, x, v, fv);
                    Goal::mk_app(g1, g2)
                }
                GoalKind::Conj(g1, g2) => {
                    let g1 = subst_inner(g1, x, v, fv);
                    let g2 = subst_inner(g2, x, v, fv);
                    Goal::mk_conj(g1, g2)
                }
                GoalKind::Disj(g1, g2) => {
                    let g1 = subst_inner(g1, x, v, fv);
                    let g2 = subst_inner(g2, x, v, fv);
                    Goal::mk_disj(g1, g2)
                }
                GoalKind::Abs(y, g) => {
                    if y.id == x.id {
                        target.clone()
                    } else if fv.contains(&y.id) {
                        let y2_ident = Ident::fresh();
                        let y2 = Variable::mk(y2_ident, y.ty.clone());
                        let g = g.rename(&y.id, &y2_ident);
                        Goal::mk_abs(y2, subst_inner(&g, x, v, fv))
                    } else {
                        Goal::mk_abs(y.clone(), subst_inner(g, x, v, fv))
                    }
                }
                GoalKind::Univ(y, g) => {
                    if y.id == x.id {
                        target.clone()
                    } else if fv.contains(&y.id) {
                        let y2_ident = Ident::fresh();
                        let y2 = Variable::mk(y2_ident, y.ty.clone());
                        let g = g.rename(&y.id, &y2_ident);
                        Goal::mk_univ(y2, subst_inner(&g, x, v, fv))
                    } else {
                        Goal::mk_univ(y.clone(), subst_inner(g, x, v, fv))
                    }
                }
            }
        }
        let fv = v.clone().fv();
        // debug
        crate::title!("fvs:");
        for f in fv.iter() {
            debug!("- {}", f)
        }
        crate::title!("subst");
        debug!("subst: [{}/{}]", v, x);
        debug!("{}", self);
        let r = subst_inner(self, x, v, &fv);
        debug!("{}", r);
        debug!("substed");
        r
    }
}

impl<C: Rename + Fv<Id = Ident>> Goal<C> {
    pub fn alpha_renaming(&self) -> Goal<C> {
        pub fn go<C: Rename>(goal: &Goal<C>, vars: &mut HashSet<Ident>) -> Goal<C> {
            // aux function for checking the uniqueness of v.id;
            // if v.id has already appeared previously (meaning v.id in vars),
            // first it generates a fresh identifier and rename v.id with the new one.
            let aux = |v: &Variable, g: &Goal<C>, vars: &HashSet<Ident>| {
                if vars.contains(&v.id) {
                    let id = Ident::fresh();
                    let g = g.rename(&v.id, &id);
                    (Variable::mk(id, v.ty.clone()), g)
                } else {
                    (v.clone(), g.clone())
                }
            };
            match goal.kind() {
                GoalKind::Constr(_) | GoalKind::Op(_) | GoalKind::Var(_) => goal.clone(),
                GoalKind::Abs(v, g) => {
                    let (v, g) = aux(v, g, vars);
                    vars.insert(v.id);
                    let g = go(&g, vars);
                    Goal::mk_abs(v, g)
                }
                GoalKind::Univ(v, g) => {
                    let (v, g) = aux(v, g, vars);
                    vars.insert(v.id);
                    let g = go(&g, vars);
                    Goal::mk_univ(v, g)
                }
                GoalKind::App(g1, g2) => {
                    let g1 = go(g1, vars);
                    let g2 = go(g2, vars);
                    Goal::mk_app(g1, g2)
                }
                GoalKind::Conj(g1, g2) => {
                    let g1 = go(g1, vars);
                    let g2 = go(g2, vars);
                    Goal::mk_conj(g1, g2)
                }
                GoalKind::Disj(g1, g2) => {
                    let g1 = go(g1, vars);
                    let g2 = go(g2, vars);
                    Goal::mk_disj(g1, g2)
                }
            }
        }
        let mut fvs = self.fv();
        go(self, &mut fvs)
    }
}
// TODO: fix not to use Refinement
impl<C: Refinement> Goal<C> {
    fn reduce_inner(&self) -> Goal<C> {
        match self.kind() {
            GoalKind::App(g, arg) => {
                // g must be have form \x. phi
                let g = g.reduce_inner();
                let arg = arg.reduce_inner();
                match g.kind() {
                    GoalKind::Abs(x, g) => {
                        let g2 = g.subst(x, &arg);
                        // debug
                        // println!("app: [{}/{}]{} ---> {}", arg, x.id, g, g2);
                        g2
                    }
                    _ => Goal::mk_app(g, arg),
                }
            }
            GoalKind::Conj(g1, g2) => {
                let g1 = g1.reduce_inner();
                let g2 = g2.reduce_inner();
                Goal::mk_conj(g1, g2)
            }
            GoalKind::Disj(g1, g2) => {
                let g1 = g1.reduce_inner();
                let g2 = g2.reduce_inner();
                Goal::mk_disj(g1, g2)
            }
            GoalKind::Univ(x, g) => {
                let g = g.reduce_inner();
                Goal::mk_univ(x.clone(), g)
            }
            GoalKind::Abs(x, g) => {
                let g = g.reduce_inner();
                Goal::mk_abs(x.clone(), g)
            }
            GoalKind::Constr(_) | GoalKind::Var(_) | GoalKind::Op(_) => self.clone(),
        }
    }
    // since there is no recursion and g is strongly typed, this procedure
    // always terminates
    pub fn reduce_goal(&self) -> Goal<C> {
        // first reduces the formula to a formula of type *
        // then traslates it to a fofml::Atom constraint.
        // debug!("to be reduced: {}", &self);
        crate::title!("reduce_goal");
        debug!("reduce {}", self);
        let mut g_old = self.clone();
        loop {
            let g = g_old.reduce_inner();
            if g == g_old {
                // debug
                // debug!("reduced: {}", &g);
                return g;
            }
            debug!("⇝ {}", g);
            g_old = g;
        }
    }
    // until it reaches the beta normal form
    pub fn reduce(&self) -> C {
        self.reduce_goal().into()
    }

    fn prenex_normal_form_raw(
        self: &Goal<C>,
        env: &mut HashSet<Ident>,
    ) -> (Vec<Variable>, Goal<C>) {
        match self.kind() {
            GoalKind::Op(_)
            | GoalKind::Var(_)
            | GoalKind::Abs(_, _)
            | GoalKind::App(_, _)
            | GoalKind::Constr(_) => (Vec::new(), self.clone()),
            GoalKind::Conj(a1, a2) => {
                let (mut v1, a1) = a1.prenex_normal_form_raw(env);
                let (mut v2, a2) = a2.prenex_normal_form_raw(env);
                v1.append(&mut v2);
                (v1, Goal::mk_conj(a1, a2))
            }
            GoalKind::Disj(a1, a2) => {
                let (mut v1, a1) = a1.prenex_normal_form_raw(env);
                let (mut v2, a2) = a2.prenex_normal_form_raw(env);
                v1.append(&mut v2);
                (v1, Goal::mk_disj(a1, a2))
            }
            GoalKind::Univ(x, a) => {
                let (x, a) = if env.contains(&x.id) {
                    // if env already contains the ident to be bound,
                    // we rename it to a fresh one.
                    let x2_ident = Ident::fresh();
                    let x2 = Variable::mk(x2_ident, x.ty.clone());
                    let a = a.rename(&x.id, &x2.id);
                    (x2, a)
                } else {
                    (x.clone(), a.clone())
                };
                env.insert(x.id);
                let (mut v, a) = a.prenex_normal_form_raw(env);
                debug_assert!(v.iter().find(|y| { x.id == y.id }).is_none());
                env.remove(&x.id);
                v.push(x);
                (v, a)
            }
        }
    }
    fn quantify(&self, vs: &[Variable]) -> Goal<C> {
        let fv = self.fv();
        let mut result = self.clone();
        for v in vs.iter().rev() {
            if fv.contains(&v.id) {
                result = Goal::mk_univ(v.clone(), result);
            }
        }
        result
    }

    fn to_cnf_inner(&self) -> Vec<Goal<C>> {
        fn cross_or<C: Refinement>(v1: &[Goal<C>], v2: &[Goal<C>]) -> Vec<Goal<C>> {
            let mut v = Vec::new();
            for x in v1 {
                for y in v2 {
                    v.push(Goal::mk_disj(x.clone(), y.clone()));
                }
            }
            v
        }
        match self.kind() {
            GoalKind::Conj(x, y) => {
                let mut v1 = x.to_cnf_inner();
                let mut v2 = y.to_cnf_inner();
                v1.append(&mut v2);
                v1
            }
            GoalKind::Disj(x, y) => {
                let v1 = x.to_cnf_inner();
                let v2 = y.to_cnf_inner();
                cross_or(&v1, &v2)
            }
            GoalKind::Constr(_)
            | GoalKind::Op(_)
            | GoalKind::Var(_)
            | GoalKind::Abs(_, _)
            | GoalKind::App(_, _)
            | GoalKind::Univ(_, _) => vec![self.clone()],
        }
    }
    pub fn to_cnf(&self) -> Vec<Goal<C>> {
        let (vs, pnf) = self.prenex_normal_form_raw(&mut HashSet::new());
        let cnf = pnf.to_cnf_inner();
        cnf.into_iter().map(|g| g.quantify(&vs)).collect()
    }
}

impl<C> Goal<C> {
    pub fn order(&self) -> usize {
        match self.kind() {
            // if order(Var(_)) > 0, then \x. ... has bigger order than that.
            GoalKind::Constr(_) | GoalKind::Op(_) | GoalKind::Var(_) => 0,
            GoalKind::Abs(x, y) => std::cmp::max(x.order() + 1, y.order()),
            GoalKind::App(x, y) | GoalKind::Conj(x, y) | GoalKind::Disj(x, y) => {
                std::cmp::max(x.order(), y.order())
            }
            GoalKind::Univ(_, y) => y.order(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Clause<C> {
    pub body: Goal<C>,
    pub head: Variable,
    // pub fixpoint: Fixpoint
}

impl From<Clause<Constraint>> for Clause<fofml::Atom> {
    fn from(c: Clause<Constraint>) -> Self {
        Clause {
            body: c.body.into(),
            head: c.head,
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

impl<C> Clause<C> {
    pub fn new(body: Goal<C>, head: Variable) -> Clause<C> {
        Clause { body, head }
    }
    pub fn new_top_clause(body: Goal<C>) -> Clause<C> {
        let head = Variable::fresh_prop();
        Clause { body, head }
    }
    pub fn order(&self) -> usize {
        self.body.order()
    }
}

#[derive(Debug, Clone)]
pub struct Problem<C> {
    pub clauses: Vec<Clause<C>>,
    pub top: Goal<C>,
}

impl From<Problem<Constraint>> for Problem<fofml::Atom> {
    fn from(p: Problem<Constraint>) -> Self {
        let clauses = p.clauses.into_iter().map(|x| x.into()).collect();
        let top = p.top.into();
        Problem { clauses, top }
    }
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

impl<C: Rename> Problem<C> {
    // [ψ₁/F₁, ψ₂/F₂ … ]ψ
    pub fn eval(&self, target: &Goal<C>) -> Goal<C> {
        match target.kind() {
            GoalKind::Var(y) => match self.get_clause(y) {
                Some(c) => c.body.clone(),
                None => target.clone(),
            },
            GoalKind::Constr(_) | GoalKind::Op(_) => target.clone(),
            GoalKind::App(g1, g2) => {
                let g1 = self.eval(g1);
                let g2 = self.eval(g2);
                Goal::mk_app(g1, g2)
            }
            GoalKind::Conj(g1, g2) => {
                let g1 = self.eval(g1);
                let g2 = self.eval(g2);
                Goal::mk_conj(g1, g2)
            }
            GoalKind::Disj(g1, g2) => {
                let g1 = self.eval(g1);
                let g2 = self.eval(g2);
                Goal::mk_disj(g1, g2)
            }
            GoalKind::Abs(y, g) => match self.get_clause(&y.id) {
                Some(_) => {
                    let y2_ident = Ident::fresh();
                    let y2 = Variable::mk(y2_ident, y.ty.clone());
                    let g = g.rename(&y.id, &y2_ident);
                    Goal::mk_abs(y2, self.eval(&g))
                }
                None => Goal::mk_abs(y.clone(), self.eval(g)),
            },
            GoalKind::Univ(y, g) => {
                if self.get_clause(&y.id).is_some() {
                    let y2_ident = Ident::fresh();
                    let y2 = Variable::mk(y2_ident, y.ty.clone());
                    let g = g.rename(&y.id, &y2_ident);
                    Goal::mk_univ(y2, self.eval(&g))
                } else {
                    Goal::mk_univ(y.clone(), self.eval(g))
                }
            }
        }
    }
}

impl<C> Problem<C> {
    pub fn order(&self) -> usize {
        let mut ord = 0;
        for c in self.clauses.iter() {
            ord = std::cmp::max(ord, c.order())
        }
        ord
    }

    pub fn get_clause<'a>(&'a self, id: &Ident) -> Option<&'a Clause<C>> {
        for c in self.clauses.iter() {
            if c.head.id == *id {
                return Some(c);
            }
        }
        None
    }
}
