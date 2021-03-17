use std::{
    collections::{HashMap, HashSet},
    ffi::FromBytesWithNulError,
    rc::Rc,
    unimplemented,
    fmt,
};

use crate::formula::hes::{Atom, AtomKind, Clause, ConstKind, Goal, GoalKind};
use crate::formula::pcsp;
use crate::formula::{
    Conjunctive, Constraint, Ident, IntegerEnvironment, Op, Subst, Top, Type as SType,
    TypeKind as STypeKind, P,
};
use crate::solver::smt;

#[derive(Debug)]
pub enum TauKind<C> {
    Proposition(C),
    IArrow(Ident, Tau<C>),
    Arrow(Tau<C>, Tau<C>),
}

pub type TyKind = TauKind<Constraint>;
pub type Tau<C> = P<TauKind<C>>;
pub type Ty = Tau<Constraint>;

impl <C: fmt::Display> fmt::Display for Tau<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TauKind::Proposition(c) => write!(f, "bool[{}]", c),
            TauKind::IArrow(i, t) => write!(f, "({}: int -> {})", i, t),
            TauKind::Arrow(t1, t2) => write!(f, "({} -> {})", t1, t2)
        }
    }
}

impl Ty {
    fn clone_with_template(&self, env: IntegerEnvironment) -> Tau<pcsp::Atom> {
        match self.kind() {
            TauKind::Proposition(_) => {
                let args = env.variables();
                let a = pcsp::Atom::fresh_pred(args);
                Tau::mk_prop_ty(a)
            }
            TauKind::IArrow(x, t) => {
                let env = env.add(*x);
                let t = t.clone_with_template(env);
                Tau::mk_iarrow(*x, t)
            }
            TauKind::Arrow(t1, t2) => {
                let t1 = t1.clone_with_template(env.clone());
                let t2 = t2.clone_with_template(env);
                Tau::mk_arrow(t1, t2)
            }
        }
    }
}

impl From<Tau<Constraint>> for Tau<pcsp::Atom> {
    fn from(from: Tau<Constraint>) -> Tau<pcsp::Atom> {
        match from.kind() {
            TauKind::Proposition(c) => Tau::mk_prop_ty(c.clone().into()),
            TauKind::IArrow(x, e) => Tau::mk_iarrow(x.clone(), e.clone().into()),
            TauKind::Arrow(e, e2) => {
                let e = e.clone().into();
                let e2 = e2.clone().into();
                Tau::mk_arrow(e, e2)
            }
        }
    }
}

impl<C: Subst> Subst for Tau<C> {
    // \tau[v/x]
    fn subst(&self, x: &Ident, v: &Op) -> Tau<C> {
        match self.kind() {
            TauKind::Proposition(c) => Tau::mk_prop_ty(c.subst(x, v)),
            TauKind::IArrow(id, _body) if id == x => self.clone(),
            TauKind::IArrow(id, body) => Tau::mk_iarrow(*id, body.subst(x, v)),
            TauKind::Arrow(l, r) => Tau::mk_arrow(l.subst(x, v), r.subst(x, v)),
        }
    }
}

impl<C: Subst> Tau<C> {
    pub fn mk_prop_ty(c: C) -> Tau<C> {
        Tau::new(TauKind::Proposition(c))
    }

    pub fn mk_iarrow(id: Ident, t: Tau<C>) -> Tau<C> {
        Tau::new(TauKind::IArrow(id, t))
    }

    pub fn mk_arrow(t: Tau<C>, s: Tau<C>) -> Tau<C> {
        Tau::new(TauKind::Arrow(t, s))
    }

    fn app(&self, v: &Op) -> Tau<C> {
        match self.kind() {
            TauKind::IArrow(x, t) => t.subst(x, v),
            _ => panic!("program error: tried to app integer to non-integer arrow type"),
        }
    }

    fn arrow_unwrap(&self) -> (Tau<C>, Tau<C>) {
        match self.kind() {
            TauKind::Arrow(x, y) => (x.clone(), y.clone()),
            _ => panic!("unwrap fail"),
        }
    }

    fn rty<'a>(&'a self) -> &'a C {
        match self.kind() {
            TauKind::Proposition(c) => c,
            // rty(iarrow(x, v)) should be \exists x. rty(v)
            // but here, implicitly all free variables are captured by
            // some universal quantifier when pcsp constraints are passed
            // to a background solver.
            TauKind::IArrow(_, t) => t.rty(),
            TauKind::Arrow(_, t) => t.rty(),
        }
    }
}

fn infer_greatest_type(environment: &Environment, arrow_type: Ty, arg_t: Ty) {
    let mut v = Vec::new();
    let ret_t = match &*arrow_type {
        TauKind::Arrow(_, y) => y.clone_with_template(environment.imap.clone()),
        _ => panic!("program error"),
    };
    //let ret_t= generate_template(environment, ret_st);
    let lhs: Tau<pcsp::Atom> = arrow_type.into();
    let rhs: Tau<pcsp::Atom> = Tau::mk_arrow(arg_t.into(), ret_t);
    generate_constraint(&lhs, &rhs, &mut v);
}

fn generate_constraint_inner(
    rty: pcsp::Atom,
    lhs: &Tau<pcsp::Atom>,
    rhs: &Tau<pcsp::Atom>,
    constraints: &mut Vec<pcsp::PCSP>,
) {
    match (lhs.kind(), rhs.kind()) {
        (TauKind::Proposition(c1), TauKind::Proposition(c2)) => {
            let c2 = pcsp::Atom::mk_conj(rty, c2.clone());
            let c1 = c1.clone();
            let cnstr = pcsp::PCSP::new(c2, c1);
            constraints.push(cnstr);
        }
        (TauKind::IArrow(x1, t1), TauKind::IArrow(x2, t2)) => {
            // let t2 = t2[x1/x2]
            let t2 = t2.subst(x1, &Op::mk_var(*x2));
            generate_constraint_inner(rty, t1, &t2, constraints);
        }
        (TauKind::Arrow(t1, s1), TauKind::Arrow(t2, s2)) => {
            generate_constraint_inner(rty.clone(), s1, s2, constraints);
            let rt = s2.rty().clone();
            generate_constraint_inner(pcsp::Atom::mk_conj(rt, rty), t2, t1, constraints);
        }
        (_, _) => panic!("program error: tried to compare {:?} <= {:?}", lhs, rhs),
    }
}

fn generate_constraint(
    lhs: &Tau<pcsp::Atom>,
    rhs: &Tau<pcsp::Atom>,
    constraints: &mut Vec<pcsp::PCSP>,
) {
    generate_constraint_inner(pcsp::Atom::mk_true(), lhs, rhs, constraints)
}

impl TyKind {
    fn new_top(st: &SType) -> TyKind {
        use STypeKind::*;
        match st.kind() {
            Proposition => TauKind::Proposition(Constraint::mk_true()),
            Arrow(x, y) if **x == Integer => {
                TauKind::IArrow(Ident::fresh(), Tau::new(TauKind::new_top(y)))
            }
            Arrow(x, y) => {
                TauKind::Arrow(Tau::new(TauKind::new_bot(x)), Tau::new(TauKind::new_top(y)))
            }
            Integer => panic!("integer occurs at the result position"),
        }
    }

    fn new_bot(st: &SType) -> TyKind {
        use STypeKind::*;
        match st.kind() {
            Proposition => TauKind::Proposition(Constraint::mk_false()),
            Arrow(x, y) if **x == Integer => {
                TauKind::IArrow(Ident::fresh(), Tau::new(TauKind::new_top(y)))
            }
            Arrow(x, y) => {
                TauKind::Arrow(Tau::new(TauKind::new_top(x)), Tau::new(TauKind::new_top(y)))
            }
            Integer => panic!("integer occurs at the result position"),
        }
    }
}

pub struct Environment {
    // Assumption: all variables are alpha-renamed.
    map: HashMap<Ident, Vec<Ty>>,
    imap: IntegerEnvironment,
}

impl Environment {
    pub fn merge(&mut self, _env: &Environment) {
        unimplemented!()
    }

    pub fn new() -> Environment {
        Environment {
            map: HashMap::new(),
            imap: IntegerEnvironment::new(),
        }
    }

    fn add_(&mut self, v: Ident, t: Ty) {
        match self.map.get_mut(&v) {
            Some(s) => {
                s.push(t);
            }
            None => {
                self.map.insert(v, vec![t]);
            }
        }
    }

    pub fn iadd(&mut self, v: Ident) {
        self.imap = self.imap.clone().add(v);
    }

    pub fn tadd(&mut self, v: Ident, t: Ty) {
        self.add_(v, t);
    }

    pub fn add_top(&mut self, v: Ident, st: &SType) {
        self.tadd(v, Ty::new(TauKind::new_top(st)));
    }

    pub fn texists(&self, v: &Ident) -> bool {
        self.map.get(v).is_some()
    }

    pub fn iexists(&self, v: &Ident) -> bool {
        self.imap.exists(v)
    }

    pub fn tget<'a>(&'a self, v: &Ident) -> Option<&'a Vec<Ty>> {
        println!("tget: {}", v);
        self.map.get(v)
    }
}

pub enum Error {
    TypeError,
}

fn int_expr(atom: &Atom, env: &Environment) -> Option<Op> {
    use AtomKind::*;
    use ConstKind::*;
    match atom.kind() {
        Const(c) => match c.kind() {
            Int(x) => Some(Op::mk_const(*x)),
            _ => None,
        },
        Var(v) if env.iexists(v) => Some(Op::mk_var(v.clone())),
        _ => None,
    }
}

fn type_check_atom(atom: &Atom, env: &Environment) -> Vec<Tau<Constraint>> {
    use AtomKind::*;
    match atom.kind() {
        App(x, arg) => {
            let ie = int_expr(arg, env);
            let ts = type_check_atom(x, env);
            match ie {
                Some(op) => ts.into_iter().map(|t| t.app(&op)).collect(),
                None => {
                    let ss = type_check_atom(arg, env);
                    let result_ts = Vec::new();
                    for t in ts.iter() {
                        for s in ss.iter() {
                            let _result_t = infer_greatest_type(env, t.clone(), s.clone());
                            unimplemented!()
                        }
                    }
                    result_ts
                }
            }
        }
        Var(v) => env.tget(v).unwrap().clone(),
        Const(_c) => panic!("program error"),
    }
}

fn type_check_goal(goal: &Goal, tenv: &Environment) -> Constraint {
    use GoalKind::*;
    let f = type_check_goal;
    match goal.kind() {
        Atom(atom) => {
            let ts = type_check_atom(atom, tenv);
            let mut ret_constr = Constraint::mk_false();
            for t in ts.iter() {
                match t.kind() {
                    TauKind::Proposition(c) => {
                        ret_constr = Constraint::mk_disj(ret_constr, c.clone())
                    }
                    _ => panic!("program error. The result type of atom must be prop."),
                }
            }
            ret_constr
        }
        Constr(c) => c.clone(),
        Conj(x, y) => Constraint::mk_conj(f(x, tenv), f(y, tenv)),
        Disj(x, y) => Constraint::mk_disj(f(x, tenv), f(y, tenv)),
        Univ(v, x) => Constraint::mk_univ(v.clone(), f(x, tenv)),
    }
}

pub fn type_check_clause(clause: &Clause, rty: Ty, env: &mut Environment) -> bool {
    let mut t = rty;
    for arg in clause.args.iter() {
        match t.kind() {
            TauKind::Proposition(_) => {panic!("program error")}
            TauKind::IArrow(x, s) => {
                t = s.rename_variable(x, arg);
                env.iadd(arg.clone());
            }
            TauKind::Arrow(x, y) => {
                env.tadd(arg.clone(), x.clone());
                t = y.clone();
            }
        }
    }
    let c = match t.kind() {
        TauKind::Proposition(c) => c,
        _ => panic!("program error"),
    };
    let c2 = type_check_goal(&clause.body, env);

    let c = Constraint::mk_arrow(c2, c.clone()).unwrap();
    match smt::smt_solve(&c) {
        smt::SMTResult::Sat => true,
        _ => false,
    }
}
