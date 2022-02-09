use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Display},
    unimplemented,
};

use crate::formula::{chc, fofml, pcsp, Variable};
use crate::formula::{
    chc::pcsps2chcs,
    hes::{Clause, Goal, GoalKind},
};
use crate::formula::{
    Bot, Conjunctive, Constraint, Fv, Ident, IntegerEnvironment, Op, QuantifierKind, Rename, Subst,
    Top, Type as SType, TypeKind as STypeKind,
};
use crate::pdr::fml::Formula;
use crate::solver::smt;
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
            TauKind::Arrow(t1, t2) => write!(f, "({} -> {})", "arg", t2),
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
fn to_fml(c: Constraint, t: Ty) -> Constraint {
    unimplemented!()
}

// ψ↑τ
fn types(fml: Formula, t: Ty) -> Constraint {
    unimplemented!()
}
