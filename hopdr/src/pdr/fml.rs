use std::collections::{HashMap, HashSet};
use std::fmt::Display;

use crate::formula::fofml;
use crate::formula::hes::Problem;
use crate::formula::hes::{Goal, GoalKind};
use crate::formula::{Constraint, Fv, Ident, Logic, Op, Rename, Subst, Type as SType, Variable};
use crate::pdr::rtype::{
    least_fml, types_check, tys_check, Refinement, Tau, TyEnv, TypeEnvironment,
};
use crate::solver;
use crate::solver::smt;

impl From<Goal<Constraint>> for Goal<fofml::Atom> {
    fn from(g: Goal<Constraint>) -> Self {
        match g.kind() {
            GoalKind::Constr(c) => Goal::mk_constr(c.clone().into()),
            GoalKind::Op(o) => Goal::mk_op(o.clone()),
            GoalKind::Var(v) => Goal::mk_var(*v),
            GoalKind::Abs(x, y) => Goal::mk_abs(x.clone(), y.clone().into()),
            GoalKind::App(x, y) => Goal::mk_app(x.clone().into(), y.clone().into()),
            GoalKind::Conj(x, y) => Goal::mk_conj(x.clone().into(), y.clone().into()),
            GoalKind::Disj(x, y) => Goal::mk_disj(x.clone().into(), y.clone().into()),
            GoalKind::Univ(x, y) => Goal::mk_univ(x.clone(), y.clone().into()),
        }
    }
}

impl From<Goal<fofml::Atom>> for fofml::Atom {
    // Assumption: the frm formula has type *
    fn from(frm: Goal<fofml::Atom>) -> Self {
        match frm.kind() {
            GoalKind::Constr(c) => c.clone(),
            GoalKind::Conj(g1, g2) => {
                let c1 = g1.clone().into();
                let c2 = g2.clone().into();
                fofml::Atom::mk_conj(c1, c2)
            }
            GoalKind::Disj(g1, g2) => {
                let c1 = g1.clone().into();
                let c2 = g2.clone().into();
                fofml::Atom::mk_disj(c1, c2)
            }
            GoalKind::Univ(x, g) => fofml::Atom::mk_univq(x.id, g.clone().into()),
            // the following must not happen
            GoalKind::Abs(_, _) | GoalKind::App(_, _) | GoalKind::Var(_) | GoalKind::Op(_) => {
                panic!("impossible to transform: {}", frm)
            }
        }
    }
}
// check if it is completely the same form
// in other words, even if f1 and f2 are alpha-equivalent,
// they are the different formulas.
// impl<C: PartialEq> PartialEq for Goal<C> {
// fn eq(&self, other: &Self) -> bool {
// match (self.kind(), other.kind()) {
// (GoalKind::Constr(c1), GoalKind::Constr(c2)) => c1 == c2,
// (GoalKind::Op(o1), GoalKind::Op(o2)) => o1 == o2,
// (GoalKind::Var(x1), GoalKind::Var(x2)) => x1 == x2,
// (GoalKind::Abs(x1, g1), GoalKind::Abs(x2, g2)) => x1 == x2 && g1 == g2,
// (GoalKind::App(g11, g12), GoalKind::App(g21, g22)) => g11 == g21 && g12 == g22,
// (GoalKind::Conj(g11, g12), GoalKind::Conj(g21, g22)) => g11 == g21 && g12 == g22,
// (GoalKind::Disj(g11, g12), GoalKind::Disj(g21, g22)) => g11 == g21 && g12 == g22,
// (GoalKind::Univ(x1, g1), GoalKind::Univ(x2, g2)) => x1 == x2 && g1 == g2,
// (_, _) => false,
// }
// }
// }

// Formula Environment Σ
pub struct Env<C> {
    map: HashMap<Ident, Goal<C>>,
    tmap: HashMap<Ident, SType>,
}

impl<C: Display> Display for Env<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (k, fml) in self.map.iter() {
            writeln!(f, "{}: {}\n", k, fml)?;
        }
        Ok(())
    }
}

impl<C: Refinement> Env<C> {
    // ⌊Γ⌋
    pub fn from_type_environment(tenv: &TypeEnvironment<Tau<C>>) -> Env<C> {
        let mut map = HashMap::new();
        let mut tmap = HashMap::new();
        for (key, ts) in tenv.map.iter() {
            let fmls = ts.iter().map(|t| least_fml(t.clone()));
            map.insert(*key, Goal::mk_ho_disj(fmls, ts[0].to_sty()));
            tmap.insert(*key, ts[0].to_sty());
        }
        Env { map, tmap }
    }

    fn go(&self, g: Goal<C>, ints: &mut HashSet<Ident>) -> Goal<C> {
        match g.kind() {
            GoalKind::Var(x) => match self.map.get(x) {
                Some(f) => {
                    debug!("checking var: {}", x);
                    let g = f.clone();
                    let mut fvs = g.fv();
                    for key in self.map.keys() {
                        fvs.remove(key);
                    }
                    debug!("fvs: {:?}", fvs);
                    debug!("ints: {:?}", ints);
                    // instantiate fvs by ints
                    let mut gs = vec![g];
                    for fv in fvs
                        .into_iter()
                        .map(|fv| Variable::mk(fv, SType::mk_type_int()))
                    {
                        let mut new_gs = Vec::new();
                        for int in ints.iter() {
                            for g in gs.iter() {
                                if new_gs.len() > 100000 {
                                    panic!("explosion")
                                }
                                new_gs.push(g.subst(&fv, &Goal::mk_op(Op::mk_var(int.clone()))));
                            }
                        }
                        gs = new_gs;
                    }
                    assert!(gs.len() > 0);
                    Goal::mk_ho_disj(gs, self.tmap.get(x).unwrap().clone())
                }
                None => Goal::mk_var(*x),
            },
            GoalKind::Abs(x, y) if x.ty.is_int() => {
                let b = ints.insert(x.id);
                let g = Goal::mk_abs(x.clone(), self.go(y.clone(), ints));
                if b {
                    ints.remove(&x.id);
                }
                g
            }
            GoalKind::Abs(x, y) => Goal::mk_abs(x.clone(), self.go(y.clone(), ints)),
            GoalKind::App(x, y) => Goal::mk_app(self.go(x.clone(), ints), self.go(y.clone(), ints)),
            GoalKind::Conj(x, y) => {
                Goal::mk_conj(self.go(x.clone(), ints), self.go(y.clone(), ints))
            }
            GoalKind::Disj(x, y) => {
                Goal::mk_disj(self.go(x.clone(), ints), self.go(y.clone(), ints))
            }
            GoalKind::Univ(x, y) if x.ty.is_int() => {
                let b = ints.insert(x.id);
                let g = Goal::mk_univ(x.clone(), self.go(y.clone(), ints));
                if b {
                    ints.remove(&x.id);
                }
                g
            }
            GoalKind::Univ(x, y) => Goal::mk_univ(x.clone(), self.go(y.clone(), ints)),
            GoalKind::Constr(_) | GoalKind::Op(_) => g.clone(),
        }
    }
    pub fn eval(&self, g: Goal<C>) -> Goal<C> {
        debug!("eval: {}", g);
        self.go(g, &mut HashSet::new())
    }
}
//fn correct_int_expr(&self, ints)
impl Env<fofml::Atom> {
    pub fn from_tyenv(tenv: &TyEnv) -> Env<fofml::Atom> {
        let mut map = HashMap::new();
        let mut tmap = HashMap::new();
        for (key, ts) in tenv.map.iter() {
            let fmls = ts.iter().map(|t| least_fml(t.clone().into()));
            map.insert(*key, Goal::mk_ho_disj(fmls, ts[0].to_sty()));
            tmap.insert(*key, ts[0].to_sty());
        }
        Env { map, tmap }
    }
}

impl<C: Refinement> Problem<C> {
    // ℱ(Σ)
    pub fn transform(&self, env: &Env<C>) -> Env<C> {
        let mut map = HashMap::new();
        for c in self.clauses.iter() {
            map.insert(c.head.id, env.eval(c.body.clone()));
        }
        Env {
            map,
            tmap: env.tmap.clone(),
        }
    }
}

pub fn env_models_constraint<C: Refinement>(env: &Env<C>, g: &Goal<C>) -> C {
    // debuggo
    debug!("env_models env: {}", env);
    let f = env.eval(g.clone());
    debug!("env_models g: {}", f);
    f.reduce()
}

// Γ ⊧ g ⇔ ⊧ θ where Γ(g) ⤳ θ
pub fn env_models(env: &Env<Constraint>, g: &Goal<Constraint>) -> bool {
    crate::title!("env_models");
    debug!("{}", g);
    let cnstr = env_models_constraint(env, g);
    match smt::default_solver().solve(&cnstr, &HashSet::new()) {
        solver::SolverResult::Sat => true,
        solver::SolverResult::Unsat => false,
        solver::SolverResult::Timeout | solver::SolverResult::Unknown => panic!("smt check fail.."),
    }
}

pub fn env_types<C: Refinement>(env: &Env<C>, tenv: &TypeEnvironment<Tau<C>>) -> C {
    let mut result_constraint = C::mk_true();
    crate::title!("env_types");
    for (x, g) in env.map.iter() {
        let ts = tenv.get(x).unwrap();
        let c = types_check(g, ts.iter().map(|x| x.clone()));
        debug!("pred name: {}", x);
        debug!("{}", g);
        debug!("generates");
        debug!("{}", c);
        result_constraint = C::mk_conj(result_constraint, c);
    }
    result_constraint
}

pub fn check_inductive(env: &TyEnv, problem: &Problem<Constraint>) -> bool {
    let tmpenv = Env::from_type_environment(env);
    debug!("tmpenv");
    debug!("{}", tmpenv);
    let fenv = problem.transform(&tmpenv);
    debug!("fenv");
    debug!("{}", fenv);

    // transform fenv
    // currently just checking ⌊Γ⌋ ↑ Γ
    for (id, g) in fenv.map.into_iter() {
        let tys = env.get(&id).unwrap().iter().map(|x| x.clone());
        if !tys_check(&g, tys) {
            return false;
        }
    }
    true
}
