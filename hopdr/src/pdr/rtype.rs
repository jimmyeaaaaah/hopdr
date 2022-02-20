use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Display},
};

use super::fml::{Env, Formula};
use crate::formula::{chc, Variable};
use crate::formula::{
    Bot, Conjunctive, Constraint, Ident, Top, Type as SType, TypeKind as STypeKind,
};
use crate::{formula::hes::Goal, solver::smt};

use crate::util::P;

#[derive(Debug)]
pub enum TauKind<C> {
    Proposition(C),
    IArrow(Ident, Tau<C>),
    Arrow(Vec<Tau<C>>, Tau<C>),
}

pub type Tau<C> = P<TauKind<C>>;
pub type TyKind<C> = TauKind<C>;
pub type Ty = Tau<Constraint>;

pub struct Positive {}

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
impl<C: fmt::Display> fmt::Display for Tau<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TauKind::Proposition(c) => write!(f, "bool[{}]", c),
            TauKind::IArrow(i, t) => write!(f, "({}: int -> {})", i, t),
            TauKind::Arrow(t1, t2) => {
                write!(f, "(")?;
                if t1.len() == 0 {
                    write!(f, "T")?;
                } else {
                    if t1.len() > 1 {
                        write!(f, "(")?;
                    }
                    write!(f, "{}", &t1[0])?;
                    for t in t1[1..].iter() {
                        write!(f, " /\\ {}", t)?;
                    }
                    if t1.len() > 1 {
                        write!(f, ")")?;
                    }
                }
                write!(f, "-> {})", t2)
            }
        }
    }
}

pub trait TTop {
    fn mk_top(st: &SType) -> Self;
}

pub trait TBot {
    fn mk_bot(st: &SType) -> Self;
}

impl<C: Top + Bot> TTop for Tau<C> {
    fn mk_top(st: &SType) -> Self {
        Tau::new(TyKind::new_top(st))
    }
}

impl<C: Top + Bot> TBot for Tau<C> {
    fn mk_bot(st: &SType) -> Self {
        Tau::new(TyKind::new_bot(st))
    }
}
impl<C: Top + Bot> TyKind<C> {
    fn new_top(st: &SType) -> TyKind<C> {
        use STypeKind::*;
        match st.kind() {
            Proposition => TauKind::Proposition(C::mk_true()),
            Arrow(x, y) if **x == Integer => {
                TauKind::IArrow(Ident::fresh(), Tau::new(TauKind::new_top(y)))
            }
            Arrow(x, y) => TauKind::Arrow(
                vec![Tau::new(TauKind::new_bot(x))],
                Tau::new(TauKind::new_top(y)),
            ),
            Integer => panic!("integer occurs at the result position"),
        }
    }
    fn new_bot(st: &SType) -> TyKind<C> {
        use STypeKind::*;
        match st.kind() {
            Proposition => TauKind::Proposition(C::mk_false()),
            Arrow(x, y) if **x == Integer => {
                TauKind::IArrow(Ident::fresh(), Tau::new(TauKind::new_bot(y)))
            }
            Arrow(x, y) => TauKind::Arrow(
                vec![Tau::new(TauKind::new_top(x))],
                Tau::new(TauKind::new_bot(y)),
            ),
            Integer => panic!("integer occurs at the result position"),
        }
    }
}

impl<C> Tau<C> {
    pub fn to_sty(&self) -> SType {
        match self.kind() {
            TauKind::Proposition(_) => SType::mk_type_prop(),
            TauKind::IArrow(_, t) => SType::mk_type_arrow(SType::mk_type_int(), t.to_sty()),
            TauKind::Arrow(t1, t2) => SType::mk_type_arrow(t1[0].to_sty(), t2.to_sty()),
        }
    }
    pub fn mk_prop_ty(c: C) -> Tau<C> {
        Tau::new(TauKind::Proposition(c))
    }

    pub fn mk_iarrow(id: Ident, t: Tau<C>) -> Tau<C> {
        Tau::new(TauKind::IArrow(id, t))
    }

    pub fn mk_arrow(t: Vec<Tau<C>>, s: Tau<C>) -> Tau<C> {
        Tau::new(TauKind::Arrow(t, s))
    }

    pub fn mk_arrow_single(t: Tau<C>, s: Tau<C>) -> Tau<C> {
        Tau::new(TauKind::Arrow(vec![t], s))
    }
}

// Type environment
pub struct TypeEnvironment<Type> {
    pub map: HashMap<Ident, Vec<Type>>,
}
pub type TyEnv = TypeEnvironment<Ty>;

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
impl<C: Top + Bot> TypeEnvironment<Tau<C>> {
    pub fn new() -> TypeEnvironment<Tau<C>> {
        TypeEnvironment {
            map: HashMap::new(),
        }
    }
    fn add_(&mut self, v: Ident, t: Tau<C>) {
        match self.map.get_mut(&v) {
            Some(s) => {
                s.push(t);
            }
            None => {
                self.map.insert(v, vec![t]);
            }
        }
    }
    pub fn add(&mut self, v: Ident, t: Tau<C>) {
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

    pub fn get<'a>(&'a self, v: &Ident) -> Option<&'a Vec<Tau<C>>> {
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

// ⌊τ⌋_c
pub fn to_fml(c: Formula, t: Ty) -> Formula {
    match t.kind() {
        TauKind::Proposition(c2) => Formula::mk_conj(c, c2.clone().into()),
        TauKind::IArrow(x, y) => {
            Formula::mk_abs(Variable::mk(*x, SType::mk_type_int()), to_fml(c, y.clone()))
        }
        TauKind::Arrow(ts, y) => {
            let ident = Ident::fresh();
            let g = Goal::mk_var(ident);
            let mut cs = c;
            for t in ts.iter() {
                cs = Formula::mk_conj(types(g.clone(), t.clone()), cs);
            }
            let fml = to_fml(cs, y.clone());
            Goal::mk_abs(Variable::mk(ident, ts[0].to_sty()), fml)
        }
    }
}

// ⌊τ⌋_tt
pub fn least_fml(t: Ty) -> Formula {
    let f = to_fml(Formula::mk_true(), t.clone());
    println!("least_fml: {} ---> {}", t, f);
    f
}

// ψ↑τ
fn types(fml: Formula, t: Ty) -> Formula {
    match t.kind() {
        TauKind::Proposition(c) => {
            let c = c.clone().negate().unwrap().into();
            Formula::mk_disj(c, fml)
        }
        TauKind::IArrow(x, t) => {
            let v = Variable::mk(*x, SType::mk_type_int());
            let p = Formula::mk_app(fml, Formula::mk_var(*x));
            let fml = types(p, t.clone());
            Formula::mk_univ(v, fml)
        }
        TauKind::Arrow(x, y) => {
            let arg = Formula::mk_ho_disj(x.iter().map(|t| least_fml(t.clone())), x[0].to_sty());
            let fml = Formula::mk_app(fml, arg);
            types(fml, y.clone())
        }
    }
}

pub fn type_check(env: &Env, g: &Formula, t: &Ty) -> bool {
    types_check(env, g, vec![t.clone()])
}

// allow inter section types
pub fn types_check(env: &Env, g: &Formula, ts: impl IntoIterator<Item = Ty>) -> bool {
    let f = env.eval(g.clone());
    let cnstr = ts
        .into_iter()
        .map(|t| {
            println!("type_check: {} : {}", g, t);
            let cnstr = types(f.clone(), t.clone()).reduce();
            let cnstr: Constraint = cnstr.into();
            cnstr
        })
        .fold(Constraint::mk_true(), |x, y| Constraint::mk_conj(x, y));
    match smt::default_solver().solve(&cnstr, &HashSet::new()) {
        smt::SMTResult::Sat => true,
        smt::SMTResult::Unsat => false,
        smt::SMTResult::Timeout | smt::SMTResult::Unknown => panic!("smt check fail.."),
    }
}

// pub fn type_check(env: TyEnv, fml: Formula, t: Ty) -> Result<(), Error> {
//
//     unimplemented!()
// }
