use std::{collections::{HashMap, HashSet}, ffi::FromBytesWithNulError, fmt::{self, Display}, rc::Rc, unimplemented};

use crate::formula::{chc::pcsps2chcs, hes::{Atom, AtomKind, Clause, ConstKind, Goal, GoalKind}};
use crate::formula::{pcsp, chc};
use crate::formula::{
    Conjunctive, Constraint, Ident, IntegerEnvironment, Op, Subst, Top, Type as SType,
    TypeKind as STypeKind, P,
    QuantifierKind,
    Fv
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

#[derive(Debug)]
pub enum Error {
    TypeError,
    SMTTimeout,
    SMTUnknown
}

impl From<chc::ResolutionError> for Error {
    fn from(_: chc::ResolutionError) -> Error {
        Error::TypeError
    }
}

impl fmt::Display for Error  {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Error::TypeError => "type error",
            Error::SMTTimeout => "SMT Timeout",
            Error::SMTUnknown => "SMT Unknown"
        };
        write!(f, "{}", s)
    }
}

impl <C: fmt::Display> fmt::Display for Tau<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TauKind::Proposition(c) => write!(f, "bool[{}]", c),
            TauKind::IArrow(i, t) => write!(f, "({}: int -> {})", i, t),
            TauKind::Arrow(t1, t2) => write!(f, "({} -> {})", t1, t2)
        }
    }
}

impl <C>Tau<C> {
    fn clone_with_template(&self, env: IntegerEnvironment, new_idents: &mut HashSet<Ident>) -> Tau<pcsp::Atom> {
        match self.kind() {
            TauKind::Proposition(_) => {
                let args = env.variables();
                let a = pcsp::Atom::fresh_pred(args, new_idents);
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

fn infer_subtype(environment: &Environment, arrow_type: Tau<pcsp::Atom>, arg_t: Tau<pcsp::Atom>, lhs_c: &[chc::CHC<pcsp::Atom>], rhs_c: &[chc::CHC<pcsp::Atom>]) -> Result<(Tau<pcsp::Atom>, Vec<chc::CHC<pcsp::Atom>>), Error> {
    debug!("infer_greatest_type: {} <: {} -> ?", arrow_type.clone(), arg_t.clone());
    let mut new_idents = HashSet::new();
    let ret_t = match &*arrow_type {
        TauKind::Arrow(_, y) => y.clone_with_template(environment.imap.clone(), &mut new_idents),
        _ => panic!("program error"),
    };
    //let ret_t= generate_template(environment, ret_st);
    let lhs: Tau<pcsp::Atom> = arrow_type.into();
    let rhs: Tau<pcsp::Atom> = Tau::mk_arrow(arg_t.into(), ret_t.clone());
    debug!("len lhs: {}", lhs_c.len());
    debug!("len rhs: {}", rhs_c.len());
    let mut constraints = Vec::new();
    generate_constraint(&lhs, &rhs, &mut constraints);
    debug!("len2: {}", constraints.len());

    //let (t, c) = infer_greatest_type_inner(ret_t, Constraint::mk_true(), true);
    // check environment; c |- arg_t < arg_t2 

    let chc_constraints = match pcsps2chcs(&constraints) {
        Some(x) => x,
        None => return Err(Error::TypeError),
    };
    let c = chc::simplify(&chc_constraints, lhs_c, rhs_c, &new_idents)?;

    Ok((ret_t, c))
}

fn generate_constraint_inner<A: Conjunctive + Clone + Subst + fmt::Debug>(
    rty: A,
    lhs: &Tau<A>,
    rhs: &Tau<A>,
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
            let t2 = t2.subst(x1, &Op::mk_var(*x2));
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

fn generate_constraint<A: Conjunctive + Clone + Subst + Top + fmt::Debug>(
    lhs: &Tau<A>,
    rhs: &Tau<A>,
    constraints: &mut Vec<pcsp::PCSP<A>>,
) {
    generate_constraint_inner(A::mk_true(), lhs, rhs, constraints)
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

impl Fv for Tau<pcsp::Atom> {
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
        debug!("tget: {}", v);
        let r = self.map.get(v);
        match r {
            Some(v) => {
                for x in v.iter() {
                    debug!("tget cont: {}", x);
                }
            },
            None => {
                debug!("not found");
            }
        }
        r
    }
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

fn type_check_atom(atom: &Atom, env: &Environment) -> Result<Vec<(Tau<pcsp::Atom>, Vec<chc::CHC<pcsp::Atom>>)>, Error> {
    //debug!("type_check_atom: {}", atom);
    use AtomKind::*;
    let r = 
    match atom.kind() {
        App(x, arg) => {
            let ie = int_expr(arg, env);
            let ts = type_check_atom(x, env)?;
            match ie {
                Some(op) => ts.into_iter().map(|(t, c)| (t.app(&op), c)).collect(),
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
        Var(v) => env.tget(v).unwrap().clone().into_iter().map(|x|(x.into(),Vec::new())).collect(),
        Const(_c) => panic!("program error"),
    };
    //debug!("type_check_atom cont: {}", atom);
    for (v,_) in r.iter() {
        debug!("type_check_atom cont ty: {}", v);
    }
    Ok(r)
}


fn type_check_goal(goal: &Goal, tenv: &mut Environment) -> Result<Constraint, Error> {
    debug!("type_check_goal start: {}", goal);
    use GoalKind::*;
    let f = type_check_goal;
    let r = 
    match goal.kind() {
        Atom(atom) => {
            let (ts) = type_check_atom(atom, tenv)?;
            for (t, constraints) in ts.iter() {
                debug!("- type: {}", t);
                for c in constraints.iter() {
                    debug!("-- constraint: {}", c)
                }
            }

            let mut fvs = HashSet::new();
            for (t, _) in ts.iter() {
                t.fv_with_vec(&mut fvs);
            }
            if fvs.len() > 1 {
                return Err(Error::TypeError)
            }
            if fvs.len() == 0 {
                debug!("fixme");
                // tmp
                return Ok(Constraint::mk_true())
            }
            let target = *fvs.iter().next().unwrap();
            debug!("ha?");

            unimplemented!();
            //let mut chc_constraints = match pcsps2chcs(&constraints) {
            //    Some(x) => x,
            //    None => return Err(Error::TypeError),
            //};
            //debug!("resolution");

            //let c = chc::solve_by_resolution(target, chc_constraints)?;
            let ts: Vec<Ty> = unimplemented!();
            // TODO: here calculate greatest type
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
        Conj(x, y) => Constraint::mk_conj(f(x, tenv)?, f(y, tenv)?),
        Disj(x, y) => Constraint::mk_disj(f(x, tenv)?, f(y, tenv)?),
        Univ(v, x) => {
            if v.ty.is_int() {
                tenv.iadd(v.id);
                Constraint::mk_quantifier(QuantifierKind::Universal, v.clone(), f(x, tenv)?)
            } else {
                unimplemented!()
            }
        },
    };
    debug!("type_check_goal: {} has type {} ", goal, r);
    Ok(r)
}

pub fn type_check_clause(clause: &Clause, rty: Ty, env: &mut Environment) -> Result<(), Error> {
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
    let mut constraints = Vec::new();
    let c2 = type_check_goal(&clause.body, env)?;

    constraints.push(pcsp::PCSP::new(c.clone(), c2.clone()));
    let mut c = Constraint::mk_false();

    for c2 in constraints {
        let c2 = c2.to_constraint().unwrap().remove_quantifier();
        debug!("constraint: {}", &c2);
        c = Constraint::mk_disj(c, c2);
    }

    match smt::smt_solve(&c) {
        smt::SMTResult::Sat => Ok(()),
        smt::SMTResult::Unsat => Err(Error::TypeError),
        smt::SMTResult::Unknown => Err(Error::SMTUnknown),
        smt::SMTResult::Timeout => Err(Error::SMTTimeout)
    }
}
