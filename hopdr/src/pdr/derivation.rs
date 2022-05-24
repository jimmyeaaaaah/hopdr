use super::rtype::{Tau, TyEnv, TypeEnvironment};
use crate::formula;
use crate::formula::hes::{Goal, GoalBase, Problem as ProblemBase};
use crate::formula::{
    chc, fofml, pcsp, Bot, Constraint, Ident, Logic, Op, Rename, Subst, Top, Type as Sty, Variable,
};
use crate::solver;

use rpds::Stack;

use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;

type Atom = fofml::Atom;
type Candidate = Goal<Atom>;
type Ty = Tau<Atom>;
type Env = TypeEnvironment<Ty>;
type Problem = ProblemBase<Atom>;
type CHC = chc::CHC<chc::Atom, Constraint>;
type PCSP = pcsp::PCSP<fofml::Atom>;

type ITy = Stack<Ty>;

impl Into<ITy> for Ty {
    fn into(self) -> ITy {
        let mut s = Stack::new();
        s.push_mut(self);
        s
    }
}

impl Sty {
    fn generate_template(&self, env: &mut HashSet<Ident>) -> Ty {
        match self.kind() {
            formula::TypeKind::Proposition => {
                let args: Vec<Op> = env.iter().map(|x| x.clone().into()).collect();
                let p = fofml::Atom::mk_fresh_pred(args);
                Ty::mk_prop_ty(p)
            }
            formula::TypeKind::Arrow(s, t) if s.is_int() => {
                let arg = Ident::fresh();
                env.insert(arg);
                let t = self.generate_template(env);
                let exists = env.remove(&arg);
                debug_assert!(exists);
                Ty::mk_iarrow(arg, t)
            }
            formula::TypeKind::Arrow(t1, t2) => {
                let v = vec![t1.generate_template(env)];
                let t = t2.generate_template(env);
                Ty::mk_arrow(v, t)
            }
            formula::TypeKind::Integer => panic!("program error"),
        }
    }
}

fn vec2ity(v: &[Ty]) -> ITy {
    let mut s = ITy::new();
    for t in v {
        s.push(t.clone());
    }
    s
}

fn get_lambda_variable(g: &Candidate) -> Ident {
    match g.kind() {
        formula::hes::GoalKind::Abs(v, _) => v.id,
        _ => panic!("g must be a lambda abstraction but got {}", g),
    }
}

/// track_idents maps predicate in Problem to the idents of lambda abstractions used for substitution
///
/// example:
///  F x f = φ₁
///  ψ = F ... /\ F ...
/// then:
///  ψ = (λx1. λf. [x1/x]φ₁) ... /\ (λx2. λf. [x2/x]φ₁) ...
/// and track_idents
///  - F = [x1, x2]
fn subst_predicate(
    candidate: &Candidate,
    problem: &Problem,
    track_idents: &mut HashMap<Ident, Vec<Ident>>,
) -> Candidate {
    match candidate.kind() {
        formula::hes::GoalKind::Constr(_) | formula::hes::GoalKind::Op(_) => candidate.clone(),
        formula::hes::GoalKind::Var(x) => match problem.get_clause(x) {
            Some(clause) => {
                let body = &clause.body;
                match body.kind() {
                    formula::hes::GoalKind::Abs(v, g) => {
                        let id = v.id;
                        let new_id = Ident::fresh();
                        let g = g.rename(&id, &new_id);
                        Goal::mk_abs(Variable::mk(new_id, v.ty.clone()), g)
                    }
                    _ => panic!("body must be a lambda abstraction but got {}", body),
                }
            }
            None => candidate.clone(),
        },
        formula::hes::GoalKind::Abs(v, g) => {
            let g = subst_predicate(g, problem, track_idents);
            Candidate::mk_abs(v.clone(), g)
        }
        formula::hes::GoalKind::App(x, y) => {
            let x = subst_predicate(x, problem, track_idents);
            let y = subst_predicate(y, problem, track_idents);
            Candidate::mk_app(x, y)
        }
        formula::hes::GoalKind::Conj(x, y) => {
            let x = subst_predicate(x, problem, track_idents);
            let y = subst_predicate(y, problem, track_idents);
            Candidate::mk_app(x, y)
        }
        formula::hes::GoalKind::Disj(x, y) => {
            let x = subst_predicate(x, problem, track_idents);
            let y = subst_predicate(y, problem, track_idents);
            Candidate::mk_app(x, y)
        }
        formula::hes::GoalKind::Univ(v, g) => {
            let g = subst_predicate(g, problem, track_idents);
            Candidate::mk_univ(v.clone(), g)
        }
    }
}

// perhaps we will attach auxiliary information so we prepare another struct for reduction sequence
struct Reduction {
    candidate: G,
    level: usize,
}

impl Reduction {
    fn new(candidate: G, level: usize) -> Reduction {
        Reduction { candidate, level }
    }
}

#[derive(Clone)]
struct Level {
    level: Stack<usize>,
}
impl Level {
    fn new() -> Level {
        Level {
            level: Stack::new(),
        }
    }
    fn add_level(&mut self, level: usize) {
        self.level = self.level.push(level)
    }
}

/// internal representation of candidate terms.
///
/// Level is used for tracking when this candidate is used
/// as the argument of beta-reduction.
type G = GoalBase<Atom, Level>;

impl From<Candidate> for G {
    fn from(c: Candidate) -> Self {
        let l = Level::new();
        match c.kind() {
            formula::hes::GoalKind::Constr(c) => G::mk_constr_t(c.clone(), l),
            formula::hes::GoalKind::Op(op) => G::mk_op_t(op.clone(), l),
            formula::hes::GoalKind::Var(id) => G::mk_var_t(*id, l),
            formula::hes::GoalKind::Abs(v, g) => G::mk_abs_t(v.clone(), g.clone().into(), l),
            formula::hes::GoalKind::App(x, y) => G::mk_app_t(x.clone().into(), y.clone().into(), l),
            formula::hes::GoalKind::Conj(x, y) => {
                G::mk_conj_t(x.clone().into(), y.clone().into(), l)
            }
            formula::hes::GoalKind::Disj(x, y) => {
                G::mk_disj_t(x.clone().into(), y.clone().into(), l)
            }
            formula::hes::GoalKind::Univ(x, g) => G::mk_univ_t(x.clone(), g.clone().into(), l),
        }
    }
}

fn generate_reduction_sequence(goal: &G) -> (Vec<Reduction>, G) {
    // Some(Candidate): substituted an app
    // None: not yet
    use formula::hes::GoalKind;

    fn go(goal: &G, level: &mut usize) -> Option<G> {
        fn go_(goal: &G, level: usize) -> Option<G> {
            match goal.kind() {
                GoalKind::App(g, arg) => {
                    // g must be have form \x. phi
                    go_(g, level)
                        .map(|g| G::mk_app_t(g, arg.clone(), goal.aux.clone()))
                        .or_else(|| {
                            go_(arg, level)
                                .map(|arg| G::mk_app_t(g.clone(), arg, goal.aux.clone()))
                                .or_else(|| {
                                    let mut g = g.clone();
                                    g.aux.add_level(level);
                                    match g.kind() {
                                        GoalKind::Abs(x, g) => {
                                            let g2 = g.subst(x, &arg);
                                            // debug
                                            // println!("app: [{}/{}]{} ---> {}", arg, x.id, g, g2);
                                            Some(g2)
                                        }
                                        _ => None,
                                    }
                                })
                        })
                }
                GoalKind::Conj(g1, g2) => go_(g1, level)
                    .map(|g1| G::mk_conj_t(g1, g2.clone(), goal.aux.clone()))
                    .or_else(|| {
                        go_(g2, level).map(|g2| G::mk_conj_t(g1.clone(), g2, goal.aux.clone()))
                    }),
                GoalKind::Disj(g1, g2) => go_(g1, level)
                    .map(|g1| G::mk_disj_t(g1, g2.clone(), goal.aux.clone()))
                    .or_else(|| {
                        go_(g2, level).map(|g2| G::mk_disj_t(g1.clone(), g2, goal.aux.clone()))
                    }),
                GoalKind::Univ(x, g) => {
                    go_(g, level).map(|g| G::mk_univ_t(x.clone(), g, goal.aux.clone()))
                }
                GoalKind::Abs(x, g) => {
                    go_(g, level).map(|g| G::mk_abs_t(x.clone(), g, goal.aux.clone()))
                }
                GoalKind::Constr(_) | GoalKind::Var(_) | GoalKind::Op(_) => None,
            }
        }
        *level += 1;
        go_(goal, *level)
    }
    let mut level = 0usize;
    let mut seq = vec![Reduction::new(goal.clone(), level)];
    let mut reduced = goal.clone();

    debug!("{}", reduced);
    while let Some(g) = go(&reduced, &mut level) {
        reduced = g.clone();
        debug!("-> {}", reduced);
        seq.push(Reduction::new(g, level));
    }
    (seq, reduced)
}

struct Context {
    normal_form: G,
    track_idents: HashMap<Ident, Vec<Ident>>,
    reduction_sequence: Vec<Reduction>,
    abstraction_types: HashMap<Ident, Ty>,
    clauses: Vec<PCSP>,
}

impl Context {
    fn new(
        normal_form: G,
        track_idents: HashMap<Ident, Vec<Ident>>,
        reduction_sequence: Vec<Reduction>,
    ) -> Context {
        Context {
            normal_form,
            track_idents,
            reduction_sequence,
            abstraction_types: HashMap::new(),
            clauses: Vec::new(),
        }
    }
    /// infer types by subject expansion along with reduction sequence
    fn infer_type(&mut self) {
        unimplemented!()
    }
}

fn reduce_until_normal_form(candidate: &Candidate, problem: &Problem) -> Context {
    let mut track_idents = HashMap::new();
    let goal = subst_predicate(candidate, problem, &mut track_idents);
    // track idents must not be renamed since we have already assigned new idents.
    let goal = goal.alpha_renaming().into();
    let (reduction_sequence, normal_form) = generate_reduction_sequence(&goal);
    Context::new(normal_form, track_idents, reduction_sequence)
}

#[derive(Clone, Debug)]
struct TypeCandidate {
    t: Ty,
    constraints: Stack<PCSP>,
}

impl From<Ty> for TypeCandidate {
    fn from(t: Ty) -> Self {
        TypeCandidate {
            t,
            constraints: Stack::new(),
        }
    }
}

impl TypeCandidate {
    fn new(t: Ty, constraints: Stack<PCSP>) -> TypeCandidate {
        TypeCandidate { t, constraints }
    }
}

/// Since type environment can contain multiple candidate types,
/// we make sure that which one is suitable by considering them parallely.
#[derive(Clone, Debug)]
struct PossibleType {
    types: Stack<TypeCandidate>,
}
impl<'a, T: IntoIterator<Item = &'a Ty>> From<T> for PossibleType {
    fn from(ts: T) -> Self {
        let mut types = Stack::new();
        for t in ts.into_iter() {
            let t: Ty = t.clone().into();
            let t = t.into();
            types.push_mut(t);
        }
        PossibleType { types }
    }
}

impl PossibleType {
    fn new(types: Stack<TypeCandidate>) -> PossibleType {
        PossibleType { types }
    }
}

impl From<Ty> for PossibleType {
    fn from(t: Ty) -> Self {
        let t = t.into();
        let mut types = Stack::new();
        types.push_mut(t);
        PossibleType { types }
    }
}

/// Γ ⊢ ψ : •〈⊤〉
///
/// tenv: Γ
/// candidate: ψ
/// ctx.abstraction_types: is used for handling types appeared in derivations
/// assumption: candidate has a beta-normal form of type *.
fn type_check_top(ctx: &mut Context, tenv: &Env, candidate: &G) -> bool {
    // we assume conjunction normal form and has the form (θ => a₁ a₂ ⋯) ∧ ⋯
    fn go(ctx: &mut Context, tenv: &Env, ienv: &HashSet<Ident>, c: &G) -> PossibleType {
        match c.kind() {
            formula::hes::GoalKind::Constr(c) => Ty::mk_prop_ty(c.clone().into()).into(),
            formula::hes::GoalKind::Var(x) => match tenv.get(x) {
                Some(t) => t.iter().into(),
                None => {
                    panic!("{} is not found in env", x)
                }
            },
            formula::hes::GoalKind::App(g1, g2) => {
                let pt1 = go(ctx, tenv, ienv, g1);
                let pt2 = go(ctx, tenv, ienv, g2);
                let mut types = Stack::new();
                for t1 in pt1.types.iter() {
                    for t2 in pt2.types.iter() {
                        // generates t1 <= t2 -> t' and constraints on the subsumption
                        unimplemented!()
                    }
                }
                PossibleType::new(types)
            }
            formula::hes::GoalKind::Conj(_, _)
            | formula::hes::GoalKind::Disj(_, _)
            | formula::hes::GoalKind::Univ(_, _) => panic!("go only accepts atom formulas"),
            formula::hes::GoalKind::Abs(v, g) => panic!("c is not a beta-normal form"),
            formula::hes::GoalKind::Op(_) => panic!("fatal error"),
        }
    }
    // 1. collects integers of universal quantifiers
    // 2. calculates cnf
    // 3. formats element of cnf to be (θ => ψ)
    // 4. pt = go(ψ) for each ψ
    // 5. check if for some tc in pt, tc.t <= *<θ> and tc.constraints hold, and returns the result
    unimplemented!()
}

pub fn generate_constraint(
    candidate: &Candidate,
    problem: &Problem,
    tenv: &Env,
) -> Option<TypeEnvironment<Tau<Constraint>>> {
    let mut ctx = reduce_until_normal_form(candidate, problem);
    let candidate = ctx.normal_form.clone();
    if !type_check_top(&mut ctx, tenv, &candidate) {
        return None;
    }
    ctx.infer_type();

    // TODO: cnf/dnf
    // solve constraints
    let clauses = ctx.clauses.into_iter().map(|c| {
        let head = match c.head.kind() {
            fofml::AtomKind::Predicate(p, l) => {
                chc::CHCHead::Predicate(chc::Atom::new(*p, l.clone()))
            }
            _ if c.head.is_false() => chc::CHCHead::Constraint(Constraint::mk_false()),
            _ => panic!("program error"),
        };
        (c.body.into(), head)
    });
    let clauses = chc::generate_chcs(clauses);
    crate::title!("generated CHC");
    for c in clauses.iter() {
        debug!("{}", c);
    }

    let m = match solver::chc::default_solver().solve(&clauses) {
        solver::chc::CHCResult::Sat(m) => m,
        solver::chc::CHCResult::Unsat => panic!("PDR fails to solve the given constraint"),
        solver::chc::CHCResult::Unknown => {
            panic!("PDR fails to infer a refinement type due to the background CHC solver's error")
        }

        solver::chc::CHCResult::Timeout => panic!(
            "PDR fails to infer a refinement type due to timeout of the background CHC solver"
        ),
    };

    crate::title!("model from CHC solver");
    // TODO: Display model
    debug!("{}", m);
    let model = solver::interpolation::solve(&clauses);
    debug!("interpolated:");
    debug!("{}", m);

    let model = model.model;
    let mut result_env = TypeEnvironment::new();
    for (k, ts) in tenv.map.iter() {
        for t in ts {
            result_env.add(*k, t.assign(&model));
        }
    }
    Some(result_env)
}
