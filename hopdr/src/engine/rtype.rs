use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Display},
    unimplemented,
};

use crate::formula::{chc, pcsp};
use crate::formula::{
    chc::pcsps2chcs,
    hes::{Atom, AtomKind, Clause, Goal, GoalKind},
};
use crate::formula::{
    Bot, Conjunctive, Constraint, Fv, Ident, IntegerEnvironment, Op, QuantifierKind, Rename, Subst,
    Top, Type as SType, TypeKind as STypeKind,
};
use crate::solver::smt;
use crate::util::PhantomPtr as P;

#[derive(Debug)]
pub enum TauKind<P, C> {
    Proposition(C),
    IArrow(Ident, Tau<P, C>),
    Arrow(Tau<P, C>, Tau<P, C>),
}

#[derive(Debug)]
pub struct Positive {}

pub type Tau<Pos, C> = P<TauKind<Pos, C>, Pos>;
pub type TyKind<P, C> = TauKind<P, C>;
pub type Ty = Tau<Positive, Constraint>;

#[derive(Debug)]
pub enum Error {
    TypeError,
    SMTTimeout,
    SMTUnknown,
}

impl From<chc::ResolutionError> for Error {
    fn from(_: chc::ResolutionError) -> Error {
        Error::TypeError
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Error::TypeError => "type error",
            Error::SMTTimeout => "SMT Timeout",
            Error::SMTUnknown => "SMT Unknown",
        };
        write!(f, "{}", s)
    }
}

impl<P, C: fmt::Display> fmt::Display for Tau<P, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TauKind::Proposition(c) => write!(f, "bool[{}]", c),
            TauKind::IArrow(i, t) => write!(f, "({}: int -> {})", i, t),
            TauKind::Arrow(t1, t2) => write!(f, "({} -> {})", t1, t2),
        }
    }
}

impl<P, C> Tau<P, C> {
    pub fn clone_with_template<Positivity>(
        &self,
        env: IntegerEnvironment,
        new_idents: &mut HashMap<Ident, pcsp::Predicate>,
    ) -> Tau<Positivity, pcsp::Atom> {
        match self.kind() {
            TauKind::Proposition(_) => {
                let args = env.variables();
                let p = pcsp::Predicate::fresh_pred(args);
                let id = p.id;
                let args = p.args.clone();
                new_idents.insert(p.id, p);
                let a = pcsp::Atom::mk_pred(id, args);
                Tau::mk_prop_ty(a)
            }
            TauKind::IArrow(x, t) => {
                let env = env.add(*x);
                let t = t.clone_with_template(env, new_idents);
                Tau::mk_iarrow(*x, t)
            }
            TauKind::Arrow(t1, t2) => {
                let t1 = t1.clone_with_template(env.clone(), new_idents);
                let t2 = t2.clone_with_template(env, new_idents);
                Tau::mk_arrow(t1, t2)
            }
        }
    }
    pub fn is_prop(&self) -> bool {
        match self.kind() {
            TauKind::Proposition(_) => true,
            _ => false,
        }
    }
}

impl<Positivity> From<&Tau<Positivity, Constraint>> for Tau<Positivity, pcsp::Atom> {
    fn from(from: &Tau<Positivity, Constraint>) -> Tau<Positivity, pcsp::Atom> {
        match from.kind() {
            TauKind::Proposition(c) => Tau::mk_prop_ty(c.clone().into()),
            TauKind::IArrow(x, e) => Tau::mk_iarrow(*x, e.into()),
            TauKind::Arrow(e, e2) => {
                let e = e.into();
                let e2 = e2.into();
                Tau::mk_arrow(e, e2)
            }
        }
    }
}

impl<Positivity> From<Tau<Positivity, Constraint>> for Tau<Positivity, pcsp::Atom> {
    fn from(from: Tau<Positivity, Constraint>) -> Tau<Positivity, pcsp::Atom> {
        (&from).into()
    }
}

impl<P, C: Subst> Subst for Tau<P, C> {
    // \tau[v/x]
    fn subst(&self, x: &Ident, v: &Op) -> Tau<P, C> {
        match self.kind() {
            TauKind::Proposition(c) => Tau::mk_prop_ty(c.subst(x, v)),
            TauKind::IArrow(id, _body) if id == x => self.clone(),
            TauKind::IArrow(id, body) => Tau::mk_iarrow(*id, body.subst(x, v)),
            TauKind::Arrow(l, r) => Tau::mk_arrow(l.subst(x, v), r.subst(x, v)),
        }
    }
}

impl<P, C: Subst + Rename> Rename for Tau<P, C> {
    fn rename(&self, x: &Ident, y: &Ident) -> Tau<P, C> {
        match self.kind() {
            TauKind::Proposition(c) => Tau::mk_prop_ty(c.rename(x, y)),
            TauKind::IArrow(id, _body) if id == x => self.clone(),
            TauKind::IArrow(id, body) => Tau::mk_iarrow(*id, body.rename(x, y)),
            TauKind::Arrow(l, r) => Tau::mk_arrow(l.rename(x, y), r.rename(x, y)),
        }
    }
}

impl<P> Tau<P, pcsp::Atom> {
    pub fn assign(&self, model: &HashMap<Ident, (Vec<Ident>, Constraint)>) -> Tau<P, Constraint> {
        match self.kind() {
            TauKind::Proposition(p) => Tau::mk_prop_ty(p.assign(model)),
            TauKind::IArrow(v, x) => Tau::mk_iarrow(*v, x.assign(model)),
            TauKind::Arrow(x, y) => Tau::mk_arrow(x.assign(model), y.assign(model)),
        }
    }
}

impl<P, C: Subst> Tau<P, C> {
    pub fn mk_prop_ty(c: C) -> Tau<P, C> {
        Tau::new(TauKind::Proposition(c))
    }

    pub fn mk_iarrow(id: Ident, t: Tau<P, C>) -> Tau<P, C> {
        Tau::new(TauKind::IArrow(id, t))
    }

    pub fn mk_arrow(t: Tau<P, C>, s: Tau<P, C>) -> Tau<P, C> {
        Tau::new(TauKind::Arrow(t, s))
    }

    pub fn app(&self, v: &Op) -> Tau<P, C> {
        match self.kind() {
            TauKind::IArrow(x, t) => t.subst(x, v),
            _ => panic!("program error: tried to app integer to non-integer arrow type"),
        }
    }

    pub fn arrow_unwrap(&self) -> (Tau<P, C>, Tau<P, C>) {
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

fn rename_constraints_by_types<P>(
    chc: chc::CHC<pcsp::Atom>,
    t1: &Tau<P, pcsp::Atom>,
    t2: &Tau<P, pcsp::Atom>,
) -> chc::CHC<pcsp::Atom> {
    match (t1.kind(), t2.kind()) {
        (TauKind::Proposition(_), TauKind::Proposition(_)) => chc,
        (TauKind::IArrow(x, tx), TauKind::IArrow(y, ty)) => {
            rename_constraints_by_types(chc.rename(y, x), tx, &ty.rename(y, x))
        }
        (TauKind::Arrow(s1, t1), TauKind::Arrow(s2, t2)) => {
            let chc = rename_constraints_by_types(chc, s1, s2);

            rename_constraints_by_types(chc, t1, t2)
        }
        _ => panic!("program error"),
    }
}

fn rename_integer_variable<P>(
    t1: &Tau<P, pcsp::Atom>,
    t2: &Tau<P, pcsp::Atom>,
) -> Tau<P, pcsp::Atom> {
    match (t1.kind(), t2.kind()) {
        (TauKind::Proposition(_), TauKind::Proposition(_)) => t2.clone(),
        (TauKind::IArrow(x, tx), TauKind::IArrow(y, ty)) => {
            let t = rename_integer_variable(tx, &ty.rename(y, x));
            Tau::mk_iarrow(*x, t)
        }
        (TauKind::Arrow(s1, t1), TauKind::Arrow(s2, t2)) => {
            let s2 = rename_integer_variable(s1, s2);
            let t2 = rename_integer_variable(t1, t2);
            Tau::mk_arrow(s2, t2)
        }
        _ => panic!("program error"),
    }
}

fn infer_subtype<P: fmt::Debug, C>(
    environment: &Environment<Tau<P, C>>,
    arrow_type: Tau<P, pcsp::Atom>,
    arg_t: Tau<P, pcsp::Atom>,
    lhs_c: &[chc::CHC<pcsp::Atom>],
    rhs_c: &[chc::CHC<pcsp::Atom>],
) -> Result<(Tau<P, pcsp::Atom>, Vec<chc::CHC<pcsp::Atom>>), Error> {
    // debug!("infer_greatest_type: {} <: {} -> ?", arrow_type, arg_t);
    let mut new_idents = HashMap::new();
    let (rhs_c_renamed, arg_t, ret_t) = match &*arrow_type {
        TauKind::Arrow(arg_t2, y) => {
            // rename rhs_c
            let mut rhs_c_renamed = Vec::new();
            let arg_t_renamed = rename_integer_variable(arg_t2, &arg_t);
            for chc in rhs_c {
                rhs_c_renamed.push(rename_constraints_by_types(chc.clone(), arg_t2, &arg_t))
            }
            (
                rhs_c_renamed,
                arg_t_renamed,
                y.clone_with_template(environment.imap.clone(), &mut new_idents),
            )
        }
        _ => panic!("program error"),
    };
    //let ret_t= generate_template(environment, ret_st);
    let lhs: Tau<P, pcsp::Atom> = arrow_type;
    let rhs: Tau<P, pcsp::Atom> = Tau::mk_arrow(arg_t, ret_t.clone());
    let mut constraints = Vec::new();
    generate_constraint(&lhs, &rhs, &mut constraints);

    //let (t, c) = infer_greatest_type_inner(ret_t, Constraint::mk_true(), true);
    // check environment; c |- arg_t < arg_t2

    let chc_constraints = match pcsps2chcs(&constraints) {
        Some(x) => x,
        None => return Err(Error::TypeError),
    };
    let c = chc::simplify(&chc_constraints, lhs_c, &rhs_c_renamed, &new_idents)?;

    Ok((ret_t, c))
}

fn generate_constraint_inner<
    P: fmt::Debug,
    A: Conjunctive + Clone + Rename + Subst + fmt::Debug + Display,
>(
    rty: A,
    lhs: &Tau<P, A>,
    rhs: &Tau<P, A>,
    constraints: &mut Vec<pcsp::PCSP<A>>,
) {
    match (lhs.kind(), rhs.kind()) {
        (TauKind::Proposition(c1), TauKind::Proposition(c2)) => {
            let c2 = A::mk_conj(rty, c2.clone());
            let c1 = c1.clone();
            let cnstr = pcsp::PCSP::new(c2, c1);
            constraints.push(cnstr);
        }
        (TauKind::IArrow(x1, t1), TauKind::IArrow(x2, t2)) => {
            // let t2 = t2[x1/x2]
            let t2 = t2.rename(x2, x1);
            generate_constraint_inner(rty, t1, &t2, constraints);
        }
        (TauKind::Arrow(t1, s1), TauKind::Arrow(t2, s2)) => {
            generate_constraint_inner(rty.clone(), s1, s2, constraints);
            let rt = s2.rty().clone();
            generate_constraint_inner(A::mk_conj(rt, rty), t2, t1, constraints);
        }
        (_, _) => panic!("program error: tried to compare {:?} <= {:?}", lhs, rhs),
    }
}

fn generate_constraint<
    P: fmt::Debug,
    A: Conjunctive + Clone + Rename + Subst + Top + fmt::Debug + Display,
>(
    lhs: &Tau<P, A>,
    rhs: &Tau<P, A>,
    constraints: &mut Vec<pcsp::PCSP<A>>,
) {
    // debug!("generate_constraint: {} <: {}", lhs, rhs);
    generate_constraint_inner(A::mk_true(), lhs, rhs, constraints)
}

pub trait TTop {
    fn mk_top(st: &SType) -> Self;
}

pub trait TBot {
    fn mk_bot(st: &SType) -> Self;
}

impl<P, C: Top + Bot> TTop for Tau<P, C> {
    fn mk_top(st: &SType) -> Self {
        Tau::new(TyKind::new_top(st))
    }
}

impl<P, C: Top + Bot> TBot for Tau<P, C> {
    fn mk_bot(st: &SType) -> Self {
        Tau::new(TyKind::new_bot(st))
    }
}

impl<P, C: Top + Bot> TyKind<P, C> {
    fn new_top(st: &SType) -> TyKind<P, C> {
        use STypeKind::*;
        match st.kind() {
            Proposition => TauKind::Proposition(C::mk_true()),
            Arrow(x, y) if **x == Integer => {
                TauKind::IArrow(Ident::fresh(), Tau::new(TauKind::new_top(y)))
            }
            Arrow(x, y) => {
                TauKind::Arrow(Tau::new(TauKind::new_bot(x)), Tau::new(TauKind::new_top(y)))
            }
            Integer => panic!("integer occurs at the result position"),
        }
    }
    fn new_bot(st: &SType) -> TyKind<P, C> {
        use STypeKind::*;
        match st.kind() {
            Proposition => TauKind::Proposition(C::mk_false()),
            Arrow(x, y) if **x == Integer => {
                TauKind::IArrow(Ident::fresh(), Tau::new(TauKind::new_bot(y)))
            }
            Arrow(x, y) => {
                TauKind::Arrow(Tau::new(TauKind::new_top(x)), Tau::new(TauKind::new_bot(y)))
            }
            Integer => panic!("integer occurs at the result position"),
        }
    }
}

impl<P> Fv for Tau<P, pcsp::Atom> {
    type Id = Ident;
    fn fv_with_vec(&self, fvs: &mut HashSet<Self::Id>) {
        match self.kind() {
            TauKind::Proposition(c) => c.fv_with_vec(fvs),
            TauKind::IArrow(_, t) => t.fv_with_vec(fvs),
            TauKind::Arrow(t1, t2) => {
                t1.fv_with_vec(fvs);
                t2.fv_with_vec(fvs)
            }
        }
    }
}

pub struct TypeEnvironment<Type> {
    pub map: HashMap<Ident, Vec<Type>>,
}

pub type PosEnvironment = TypeEnvironment<Ty>;

impl<T: Clone> Clone for TypeEnvironment<T> {
    fn clone(&self) -> Self {
        Self {
            map: self.map.clone(),
        }
    }
}

impl<T: Display> Display for TypeEnvironment<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (idx, ts) in self.map.iter() {
            write!(f, "{} : ", idx)?;
            let mut fst = true;
            for t in ts {
                if fst {
                    fst = false;
                } else {
                    write!(f, ", ")?;
                }
                write!(f, "{}", t)?;
            }
            writeln!(f)?;
        }
        writeln!(f)
    }
}

impl<P, C: Top + Bot> TypeEnvironment<Tau<P, C>> {
    pub fn new() -> TypeEnvironment<Tau<P, C>> {
        TypeEnvironment {
            map: HashMap::new(),
        }
    }
    fn add_(&mut self, v: Ident, t: Tau<P, C>) {
        match self.map.get_mut(&v) {
            Some(s) => {
                s.push(t);
            }
            None => {
                self.map.insert(v, vec![t]);
            }
        }
    }
    pub fn add(&mut self, v: Ident, t: Tau<P, C>) {
        self.add_(v, t);
    }
    pub fn exists(&self, v: &Ident) -> bool {
        self.map.get(v).is_some()
    }
    pub fn add_top(&mut self, v: Ident, st: &SType) {
        self.add(v, Tau::mk_top(st));
    }

    pub fn add_bot(&mut self, v: Ident, st: &SType) {
        self.add(v, Tau::mk_bot(st));
    }

    pub fn get<'a>(&'a self, v: &Ident) -> Option<&'a Vec<Tau<P, C>>> {
        let r = self.map.get(v);
        match r {
            Some(v) => {
                for _x in v.iter() {
                    //debug!("tget cont: {}", x);
                }
            }
            None => {
                debug!("not found");
            }
        }
        r
    }
}
impl<P> TypeEnvironment<Tau<P, Constraint>> {
    pub fn clone_with_template<P2>(
        &self,
        new_idents: &mut HashMap<Ident, pcsp::Predicate>,
    ) -> TypeEnvironment<Tau<P2, pcsp::Atom>> {
        let mut env = TypeEnvironment::new();
        for (i, ts) in self.map.iter() {
            for t in ts {
                let st = t.clone_with_template(IntegerEnvironment::new(), new_idents);
                env.add(*i, st);
            }
        }
        env
    }
}

pub struct Environment<Ty> {
    // Assumption: all variables are alpha-renamed.
    pub map: TypeEnvironment<Ty>,
    pub imap: IntegerEnvironment,
}
impl<P> From<&TypeEnvironment<Tau<P, Constraint>>> for TypeEnvironment<Tau<P, pcsp::Atom>> {
    fn from(e: &TypeEnvironment<Tau<P, Constraint>>) -> Self {
        let mut env: TypeEnvironment<Tau<P, pcsp::Atom>> = TypeEnvironment::new();
        for (x, ys) in e.map.iter() {
            for y in ys {
                let t = y.into();
                env.add(*x, t);
            }
        }
        env
    }
}

impl<P, C: Top + Bot + Subst + Rename> Environment<Tau<P, C>> {
    pub fn merge(&mut self, _env: &Environment<Tau<P, C>>) {
        unimplemented!()
    }

    pub fn new() -> Environment<Tau<P, C>> {
        Environment {
            map: TypeEnvironment::new(),
            imap: IntegerEnvironment::new(),
        }
    }

    pub fn from_type_environment(map: TypeEnvironment<Tau<P, C>>) -> Environment<Tau<P, C>> {
        Environment {
            map,
            imap: IntegerEnvironment::new(),
        }
    }

    pub fn iadd(&mut self, v: Ident) {
        self.imap = self.imap.clone().add(v);
    }

    pub fn tadd(&mut self, v: Ident, t: Tau<P, C>) {
        self.map.add(v, t)
    }

    pub fn texists(&self, v: &Ident) -> bool {
        self.map.exists(v)
    }

    pub fn iexists(&self, v: &Ident) -> bool {
        self.imap.exists(v)
    }

    pub fn tget<'a>(&'a self, v: &Ident) -> Option<&'a Vec<Tau<P, C>>> {
        self.map.get(v)
    }

    pub fn add_arg_types(&mut self, args: &[Ident], ty: Tau<P, C>) -> Tau<P, C> {
        let mut tmp_t = ty;
        for arg in args {
            match tmp_t.kind() {
                TauKind::Proposition(_) => panic!("program error"),
                TauKind::IArrow(x, s) => {
                    tmp_t = s.rename_variable(x, arg);
                    self.iadd(*arg);
                }
                TauKind::Arrow(x, y) => {
                    self.tadd(*arg, x.clone());
                    tmp_t = y.clone();
                }
            }
        }
        tmp_t
    }
}

fn int_expr<'a, P, C: Top + Bot + Subst + Rename>(
    atom: &Atom,
    env: &Environment<Tau<P, C>>,
) -> Option<Ident> {
    use AtomKind::*;
    match atom.kind() {
        //Const(c) => match c.kind() {
        //    Int(x) => Some(Op::mk_const(*x)),
        //    _ => None,
        //},
        Var(v) if env.iexists(v) => Some(*v),
        _ => None,
    }
}

pub fn type_check_atom<'a, P: fmt::Debug, C: Top + Bot + Rename + Subst>(
    atom: &Atom,
    env: &Environment<Tau<P, C>>,
) -> Result<Vec<(Tau<P, pcsp::Atom>, Vec<chc::CHC<pcsp::Atom>>)>, Error>
where
    Tau<P, C>: Into<Tau<P, pcsp::Atom>>,
{
    use AtomKind::*;
    debug!("type_check_atom: {}", atom);
    let r = match atom.kind() {
        App(x, arg) => {
            let ie = int_expr(arg, env);
            let ts = type_check_atom(x, env)?;
            match ie {
                Some(y) => ts
                    .into_iter()
                    .map(|(t, cs)| match t.kind() {
                        TauKind::IArrow(x, t) => (
                            t.rename(x, &y),
                            cs.into_iter().map(|c| c.rename(x, &y)).collect(),
                        ),
                        TauKind::Proposition(_) | TauKind::Arrow(_, _) => panic!("program error"),
                    })
                    .collect(),
                None => {
                    let ss = type_check_atom(arg, env)?;
                    let mut result_ts = Vec::new();
                    for (t, cs1) in ts.iter() {
                        for (s, cs2) in ss.iter() {
                            let result_t = infer_subtype(env, t.clone(), s.clone(), cs1, cs2)?;
                            result_ts.push(result_t);
                        }
                    }
                    result_ts
                }
            }
        }
        Var(v) => env
            .tget(v)
            .unwrap()
            .clone()
            .into_iter()
            .map(|x| (x.into(), Vec::new()))
            .collect(),
    };
    debug!("type_check_atom cont: {}", atom);
    for (v, _) in r.iter() {
        debug!("type_check_atom cont ty: {}", v);
    }
    Ok(r)
}

pub fn type_check_goal<'a>(
    goal: &Goal,
    tenv: &mut Environment<Tau<Positive, pcsp::Atom>>,
) -> Result<pcsp::Atom, Error> {
    //debug!("type_check_goal start: {}", goal);
    use GoalKind::*;
    let f = type_check_goal;
    let r = match goal.kind() {
        Atom(atom) => {
            let ts = type_check_atom(atom, tenv)?;
            // for (t, constraints) in ts.iter() {
            //     debug!("- type: {}", t);
            //     for c in constraints.iter() {
            //         debug!("-- constraint: {}", c)
            //     }
            // }

            // TODO: here calculate greatest type
            let mut ret_constr = pcsp::Atom::mk_false();
            for (t, constraints) in ts {
                let mut targets = HashSet::new();
                t.fv_with_vec(&mut targets);
                match t.kind() {
                    TauKind::Proposition(_) => {
                        let c = chc::resolve_target(constraints, &targets).unwrap();
                        ret_constr = pcsp::Atom::mk_disj(ret_constr, c.clone());
                    }
                    _ => panic!("program error. The result type of atom must be prop."),
                }
            }
            ret_constr
        }
        Constr(c) => c.clone().into(),
        Conj(x, y) => pcsp::Atom::mk_conj(f(x, tenv)?, f(y, tenv)?),
        Disj(x, y) => pcsp::Atom::mk_disj(f(x, tenv)?, f(y, tenv)?),
        Univ(v, x) => {
            if v.ty.is_int() {
                tenv.iadd(v.id);
                pcsp::Atom::mk_quantifier(QuantifierKind::Universal, v.id, f(x, tenv)?)
            } else {
                unimplemented!()
            }
        }
    };
    debug!("type_check_goal: {} has type {} ", goal, r);
    Ok(r)
}

fn check_smt(c: &Constraint, vars: &HashSet<Ident>) -> Result<(), Error> {
    let mut solver = smt::default_solver();
    match solver.solve(c, vars) {
        smt::SMTResult::Sat => Ok(()),
        smt::SMTResult::Unsat => Err(Error::TypeError),
        smt::SMTResult::Unknown => Err(Error::SMTUnknown),
        smt::SMTResult::Timeout => Err(Error::SMTTimeout),
    }
}

pub fn type_check_top(
    toplevel: &Goal,
    env: TypeEnvironment<Tau<Positive, pcsp::Atom>>,
) -> Result<(), Error> {
    let mut env = Environment::from_type_environment(env);
    let cnstr = type_check_goal(toplevel, &mut env)?
        .to_constraint()
        .unwrap();
    check_smt(&cnstr, &env.imap.iter().collect())
}

pub fn type_check_clause(
    clause: &Clause,
    rty: Ty,
    env: TypeEnvironment<Tau<Positive, pcsp::Atom>>,
) -> Result<(), Error> {
    debug!("type_check_clause: {}: {}", clause, rty);
    let mut env = Environment::from_type_environment(env);
    let t = env.add_arg_types(&clause.args, rty.into());
    let c = match t.kind() {
        TauKind::Proposition(c) => c.to_constraint().unwrap(),
        _ => panic!("program error"),
    };
    let c2 = type_check_goal(&clause.body, &mut env)?
        .to_constraint()
        .unwrap();
    println!("typecheck_clause constraint: {}", c);
    let c2 = pcsp::PCSP::new(c, c2);
    let c = c2.to_constraint().unwrap().remove_quantifier();

    debug!("{:?}", env.imap.iter().collect::<Vec<_>>());
    check_smt(&c, &env.imap.iter().collect())
}
