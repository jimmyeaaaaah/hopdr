use super::rtype::{Tau, TypeEnvironment};
use crate::formula::hes::{Goal, GoalBase, Problem as ProblemBase};
use crate::formula::{self, Fv};
use crate::formula::{
    chc, fofml, pcsp, Bot, Constraint, Ident, Logic, Negation, Op, Rename, Subst, Top, Variable,
};
use crate::solver;

use rpds::{HashTrieMap, Stack};

use std::collections::{HashMap, HashSet};

type Atom = Constraint;
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

// impl Sty {
//     fn generate_template(&self, env: &mut HashSet<Ident>) -> Ty {
//         match self.kind() {
//             formula::TypeKind::Proposition => {
//                 let args: Vec<Op> = env.iter().map(|x| x.clone().into()).collect();
//                 let p = fofml::Atom::mk_fresh_pred(args);
//                 Ty::mk_prop_ty(p)
//             }
//             formula::TypeKind::Arrow(s, t) if s.is_int() => {
//                 let arg = Ident::fresh();
//                 env.insert(arg);
//                 let t = self.generate_template(env);
//                 let exists = env.remove(&arg);
//                 debug_assert!(exists);
//                 Ty::mk_iarrow(arg, t)
//             }
//             formula::TypeKind::Arrow(t1, t2) => {
//                 let v = vec![t1.generate_template(env)];
//                 let t = t2.generate_template(env);
//                 Ty::mk_arrow(v, t)
//             }
//             formula::TypeKind::Integer => panic!("program error"),
//         }
//     }
// }

fn vec2ity(v: &[Ty]) -> ITy {
    let s = ITy::new();
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
    level_arg: Stack<usize>,
    level_ret: Stack<usize>,
}
impl Level {
    fn new() -> Level {
        Level {
            level_arg: Stack::new(),
            level_ret: Stack::new(),
        }
    }
    fn add_arg_level(&mut self, level: usize) {
        self.level_arg = self.level_arg.push(level)
    }
    fn add_ret_level(&mut self, level: usize) {
        self.level_ret = self.level_ret.push(level)
    }
}

impl Default for Level {
    fn default() -> Self {
        Level::new()
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
                                    let mut arg = arg.clone();
                                    // track the type of argument
                                    arg.aux.add_arg_level(level);
                                    match g.kind() {
                                        GoalKind::Abs(x, g) => {
                                            let mut ret = g.subst(x, &arg);
                                            // track the result type
                                            ret.aux.add_ret_level(level);
                                            Some(ret)
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
    fn infer_type(&mut self, map: HashMap<usize, Vec<Ty>>) {
        for reduction in self.reduction_sequence.iter().rev() {
            let ty = map.get(&reduction.level).unwrap();
        }
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
struct CandidateType {
    ty: Ty,
    // level -> type map appeared in the derivation of ty so far.
    derivation: HashTrieMap<usize, Stack<Ty>>,
}

impl CandidateType {
    fn new(ty: Ty, derivation: HashTrieMap<usize, Stack<Ty>>) -> CandidateType {
        CandidateType { ty, derivation }
    }
    fn memorize(&mut self, level: usize) {
        let st = match self.derivation.get(&level) {
            Some(st) => st.clone(),
            None => Stack::new(),
        };
        self.derivation = self.derivation.insert(level, st.push(self.ty.clone()))
    }
}

impl From<Ty> for CandidateType {
    fn from(ty: Ty) -> Self {
        CandidateType {
            ty,
            derivation: HashTrieMap::new(),
        }
    }
}

/// Since type environment can contain multiple candidate types,
/// we make sure that which one is suitable by considering them parallely.
#[derive(Debug)]
struct PossibleType {
    types: Vec<CandidateType>,
}
impl<'a, T: IntoIterator<Item = &'a Ty>> From<T> for PossibleType {
    fn from(ts: T) -> Self {
        let mut types = Vec::new();
        for t in ts.into_iter() {
            let t: CandidateType = t.clone().into();
            types.push(t);
        }
        PossibleType::new(types)
    }
}

impl PossibleType {
    fn new(types: Vec<CandidateType>) -> PossibleType {
        PossibleType { types }
    }

    // check if ts' ⊂ self exists where ts' <: ts holds.
    fn check_subtype(&self, ts: &[Ty], constraint: &Constraint) -> bool {
        use crate::pdr::rtype::TauKind;
        fn go(constraint: Constraint, t: &Ty, s: &Ty) -> Constraint {
            match (t.kind(), s.kind()) {
                (TauKind::Proposition(c1), TauKind::Proposition(c2)) => Constraint::mk_implies(
                    Constraint::mk_conj(constraint.clone(), c2.clone()),
                    c1.clone(),
                ),
                (TauKind::IArrow(x1, t1), TauKind::IArrow(x2, t2)) => {
                    let t2 = t2.rename(x2, x1);
                    go(constraint, t1, &t2)
                }
                (TauKind::Arrow(ts1, _t1), TauKind::Arrow(ts2, _t2)) => {
                    let mut result_constraint = Constraint::mk_true();
                    // ⋀ᵢ tᵢ ≺ ⋀ⱼt'ⱼ ⇔∀ tᵢ. ∃ t'ⱼ. tᵢ ≺ t'ⱼ
                    for tx in ts1 {
                        let mut tmpc = Constraint::mk_false();
                        for ty in ts2 {
                            let c = Constraint::mk_conj(constraint.clone(), ty.constraint_rty());
                            tmpc = Constraint::mk_disj(tmpc, go(c, tx, ty));
                        }
                        result_constraint = Constraint::mk_conj(result_constraint, tmpc);
                    }
                    result_constraint
                }
                (_, _) => panic!("fatal"),
            }
        }
        // is there possible derivation for each t in ts
        for t in ts {
            for s in self.types.iter() {
                let c = go(constraint.clone(), &s.ty, t);
                // check by smt solver
                if solver::smt::default_solver()
                    .solve_with_universal_quantifiers(&c)
                    .is_sat()
                {
                    return true;
                }
            }
        }
        false
    }
}

impl From<Ty> for PossibleType {
    fn from(t: Ty) -> Self {
        let t = t.into();
        let mut types = Vec::new();
        types.push(t);
        PossibleType::new(types)
    }
}

fn rename_integer_variable(t1: &Ty, t2: &Ty) -> Ty {
    use crate::pdr::rtype::TauKind;
    match (t1.kind(), t2.kind()) {
        (TauKind::Proposition(_), TauKind::Proposition(_)) => t2.clone(),
        (TauKind::IArrow(x, tx), TauKind::IArrow(y, ty)) => {
            let t = rename_integer_variable(tx, &ty.rename(y, x));
            Tau::mk_iarrow(*x, t)
        }
        (TauKind::Arrow(s1, t1), TauKind::Arrow(s2, t2)) => {
            let mut args = Vec::new();
            for (s1, s2) in s1.iter().zip(s2.iter()) {
                let s2 = rename_integer_variable(s1, s2);
                args.push(s2);
            }
            let t2 = rename_integer_variable(t1, t2);
            Tau::mk_arrow(args, t2)
        }
        _ => panic!("program error"),
    }
}

fn check_int_expr(ienv: &HashSet<Ident>, g: &G) -> Option<Op> {
    match g.kind() {
        formula::hes::GoalKind::Op(o) => Some(o.clone()),
        formula::hes::GoalKind::Var(x) if ienv.contains(x) => Some(Op::mk_var(*x)),
        formula::hes::GoalKind::Var(_)
        | formula::hes::GoalKind::Constr(_)
        | formula::hes::GoalKind::Abs(_, _)
        | formula::hes::GoalKind::App(_, _)
        | formula::hes::GoalKind::Conj(_, _)
        | formula::hes::GoalKind::Disj(_, _)
        | formula::hes::GoalKind::Univ(_, _) => None,
    }
}
// takes g and formats it and returns (Θ, g') where Θ => g'
fn format_cnf_clause(g: G) -> (Constraint, G) {
    match g.kind() {
        formula::hes::GoalKind::Constr(_)
        | formula::hes::GoalKind::Var(_)
        | formula::hes::GoalKind::Abs(_, _)
        | formula::hes::GoalKind::App(_, _) => (Constraint::mk_true(), g.clone()),
        formula::hes::GoalKind::Disj(g1, g2) => {
            let c: Option<Atom> = g1.clone().into();
            match c {
                Some(c) => (c.negate().unwrap(), g2.clone()),
                None => {
                    let c: Option<Atom> = g2.clone().into();
                    match c {
                        Some(c) => (c.negate().unwrap(), g1.clone()),
                        None => panic!("fatal: candidate is non-linear."),
                    }
                }
            }
        }
        formula::hes::GoalKind::Conj(_, _)
        | formula::hes::GoalKind::Univ(_, _)
        | formula::hes::GoalKind::Op(_) => panic!("fatal"),
    }
}

/// Γ ⊢ ψ : •<T>
///
/// tenv: Γ
/// candidate: ψ
/// ctx.abstraction_types: is used for handling types appeared in derivations
/// assumption: candidate has a beta-normal form of type *.
fn type_check_top(
    ctx: &mut Context,
    tenv: &Env,
    candidate: &G,
) -> Option<HashTrieMap<usize, Stack<Ty>>> {
    use crate::pdr::rtype::TauKind;
    // we assume conjunction normal form and has the form (θ => a₁ a₂ ⋯) ∧ ⋯
    // constraint: Θ
    // Γ; Θ ⊢ c : t
    // function go constructs possible derivation trees by induction on the structure of c(ψ)
    //
    fn go(
        ctx: &mut Context,
        constraint: &Constraint,
        t: &Ty,
        tenv: &Env,
        ienv: &HashSet<Ident>,
        c: &G,
    ) -> PossibleType {
        fn go_inner(
            ctx: &mut Context,
            t: &Ty,
            tenv: &Env,
            ienv: &HashSet<Ident>,
            c: &G,
        ) -> PossibleType {
            match c.kind() {
                formula::hes::GoalKind::Constr(c) => Ty::mk_prop_ty(c.clone().into()).into(),
                formula::hes::GoalKind::Var(x) => match tenv.get(x) {
                    Some(t) => t.iter().into(),
                    None => {
                        panic!("{} is not found in env", x)
                    }
                },
                formula::hes::GoalKind::App(g1, g2) => {
                    let pt1 = go(ctx, t, tenv, ienv, g1);
                    match check_int_expr(ienv, g2) {
                        // Case: the type of argument is int
                        Some(op) => {
                            let types = pt1
                                .types
                                .into_iter()
                                .map(|t| match t.ty.kind() {
                                    TauKind::IArrow(x, t2) => {
                                        CandidateType::new(t2.subst(x, &op), t.derivation.clone())
                                    }
                                    _ => panic!("fatal"),
                                })
                                .collect();
                            return PossibleType::new(types);
                        }
                        // Otherwise, we continue.
                        None => (),
                    };
                    // we calculate the
                    let pt2 = go(ctx, t, tenv, ienv, g2);
                    let mut types = Vec::new();
                    for t1 in pt1.types.iter() {
                        // check if t1 <= t2 -> t' holds
                        let (ts, ret_ty) = match t1.ty.kind() {
                            TauKind::Arrow(ts, ret_ty) => (ts, ret_ty),
                            _ => panic!("fatal"),
                        };
                        // check if there is a possible type derivation; if so, mark ret_ty as PossibleType; otherwise, do nothing.
                        if pt2.check_subtype(ts, unimplemented!()) {
                            types.push(CandidateType::new(ret_ty.clone(), t1.derivation.clone()));
                        }
                    }
                    PossibleType::new(types)
                }
                formula::hes::GoalKind::Conj(_, _)
                | formula::hes::GoalKind::Disj(_, _)
                | formula::hes::GoalKind::Univ(_, _) => panic!("go only accepts atom formulas"),
                formula::hes::GoalKind::Abs(_v, _g) => panic!("c is not a beta-normal form"),
                formula::hes::GoalKind::Op(_) => panic!("fatal error"),
            }
        }
        let mut pt = go_inner(ctx, t, tenv, ienv, c);
        for level in c.aux.level_arg.iter() {
            for ct in pt.types.iter_mut() {
                ct.memorize(*level);
            }
        }
        pt
    }
    // これが嘘だなあ
    // prenex normal formすら取れるかわからん
    // F (λx.∀y.x >= y) ∧ F (∀x.∀y.x <= y)
    // のような例が普通にあるので
    // 必要なのは、**各bool型の式について** prenex normal formであり、(Θ => ψ) /\ ...の形の論理式に変換すること
    // これは既存関数ではできないので、新しくそういう関数を作るべき
    // 加えて、変換したときに、reductionのときに作っていたlevelの情報を保存するように変換できるはず

    // 1. collects integers of universal quantifiers
    // prenex normal formだけ考える
    let (vars, candidate) = candidate.prenex_normal_form_raw(&mut HashSet::new());
    let ienv = vars
        .iter()
        .map(|v| {
            debug_assert!(v.ty.is_int());
            v.id
        })
        .collect();

    let pt = go(
        ctx,
        &Constraint::mk_true(),
        &Ty::mk_prop_ty(Constraint::mk_true()),
        tenv,
        &ienv,
        &candidate,
    );
    pt.types.pop().map(|t| t.derivation)
}

pub fn generate_constraint(
    candidate: &Candidate,
    problem: &Problem,
    tenv: &Env,
) -> Option<TypeEnvironment<Tau<Constraint>>> {
    let mut ctx = reduce_until_normal_form(candidate, problem);
    let candidate = ctx.normal_form.clone();
    let map = type_check_top(&mut ctx, tenv, &candidate)?;
    ctx.infer_type(map);

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
    let _model = solver::interpolation::solve(&clauses);
    debug!("interpolated:");
    debug!("{}", m);

    //let model = model.model;
    //let mut result_env = TypeEnvironment::new();
    //for (k, ts) in tenv.map.iter() {
    //    for t in ts {
    //        result_env.add(*k, t.assign(&model));
    //    }
    //}
    //Some(result_env)
    unimplemented!()
}
