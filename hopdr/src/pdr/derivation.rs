use super::rtype::{Tau, TauKind, TypeEnvironment};
use crate::formula::hes::{Goal, GoalBase, Problem as ProblemBase};
use crate::formula::{self, FirstOrderLogic};
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
type Level = usize;
// perhaps we will attach auxiliary information so we prepare another struct for reduction sequence
struct Reduction {
    // this is the id of this reduction.
    // this value is memorized in the memory of each expression
    // for each reduction. That is, when we have reduction
    //    expr1 expr2 -> expr3
    // this id is memorized in expr2's memory (as the argument) and expr3's memory (as the return value)
    level: Level,
    // this is `expr1` in the above example.
    // at the inference phase, we utilize G's memory to assign the inferred types to G.
    predicate: G,
}

impl Reduction {
    fn new(predicate: G, level: usize) -> Reduction {
        Reduction { predicate, level }
    }
}

#[derive(Clone)]
struct TypeMemory {
    level_arg: Stack<usize>,
    level_ret: Stack<usize>,
}
impl TypeMemory {
    fn new() -> TypeMemory {
        TypeMemory {
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

impl Default for TypeMemory {
    fn default() -> Self {
        TypeMemory::new()
    }
}

/// internal representation of candidate terms.
///
/// Level is used for tracking when this candidate is used
/// as the argument of beta-reduction.
type G = GoalBase<Atom, TypeMemory>;

impl From<Candidate> for G {
    fn from(c: Candidate) -> Self {
        let l = TypeMemory::new();
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

    fn go(goal: &G, level: &mut usize) -> Option<(G, G)> {
        // left of the return value: the reduced term
        // right of the return value: the abstraction in the redux.
        fn go_(goal: &G, level: usize) -> Option<(G, G)> {
            match goal.kind() {
                GoalKind::App(predicate, arg) => {
                    // g must be have form \x. phi
                    go_(predicate, level)
                        .map(|(g, pred)| (G::mk_app_t(g, arg.clone(), goal.aux.clone()), pred))
                        .or_else(|| {
                            go_(arg, level)
                                .map(|(arg, pred)| {
                                    (G::mk_app_t(predicate.clone(), arg, goal.aux.clone()), pred)
                                })
                                .or_else(|| {
                                    let mut arg = arg.clone();
                                    // track the type of argument
                                    arg.aux.add_arg_level(level);
                                    match predicate.kind() {
                                        GoalKind::Abs(x, g) => {
                                            let mut ret = g.subst(x, &arg);
                                            // track the result type
                                            ret.aux.add_ret_level(level);
                                            Some((ret, predicate.clone()))
                                        }
                                        _ => None,
                                    }
                                })
                        })
                }
                GoalKind::Conj(g1, g2) => go_(g1, level)
                    .map(|(g1, p)| (G::mk_conj_t(g1, g2.clone(), goal.aux.clone()), p))
                    .or_else(|| {
                        go_(g2, level)
                            .map(|(g2, p)| (G::mk_conj_t(g1.clone(), g2, goal.aux.clone()), p))
                    }),
                GoalKind::Disj(g1, g2) => go_(g1, level)
                    .map(|(g1, p)| (G::mk_disj_t(g1, g2.clone(), goal.aux.clone()), p))
                    .or_else(|| {
                        go_(g2, level)
                            .map(|(g2, p)| (G::mk_disj_t(g1.clone(), g2, goal.aux.clone()), p))
                    }),
                GoalKind::Univ(x, g) => {
                    go_(g, level).map(|(g, p)| (G::mk_univ_t(x.clone(), g, goal.aux.clone()), p))
                }
                GoalKind::Abs(x, g) => {
                    go_(g, level).map(|(g, p)| (G::mk_abs_t(x.clone(), g, goal.aux.clone()), p))
                }
                GoalKind::Constr(_) | GoalKind::Var(_) | GoalKind::Op(_) => None,
            }
        }
        *level += 1;
        go_(goal, *level)
    }
    let mut level = 0usize;
    let mut seq = Vec::new();
    let mut reduced = goal.clone();

    debug!("{}", reduced);
    while let Some((g, p)) = go(&reduced, &mut level) {
        reduced = g.clone();
        debug!("-> {}", reduced);
        seq.push(Reduction::new(p, level));
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
    fn infer_type(&mut self, map: Derivation) {
        unimplemented!()
    }
}

fn infer_type(normal_form: G, derivation: Derivation, reduction_sequence: Vec<Reduction>) {
    let mut current = normal_form;
    //let mut constraints = Vec::new();
    for reduction in reduction_sequence.iter().rev() {
        let level = reduction.level;
        // 1. get the corresponding types
        let arg_ty = derivation.get_arg(&level);
        let ret_ty = derivation.get_ret(&level);
        // 2. generate template type from arg_ty -> ret_ty
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
struct DerivationMap(HashTrieMap<usize, Stack<Ty>>);
impl DerivationMap {
    fn new() -> DerivationMap {
        DerivationMap(HashTrieMap::new())
    }
    fn merge_derivation_map(&mut self, mut y: DerivationMap) {
        for (k, vs) in y.0.iter() {
            let stack = match self.0.get(k) {
                Some(s) => {
                    let mut s = s.clone();
                    for v in vs {
                        s.push_mut(v.clone())
                    }
                    s
                }
                None => vs.clone(),
            };
            self.0.insert_mut(*k, stack);
        }
    }
    fn insert(&mut self, level: usize, ty: Ty) {
        let st = match self.0.get(&level) {
            Some(st) => st.clone(),
            None => Stack::new(),
        };
        self.0 = self.0.insert(level, st.push(ty.clone()))
    }
    fn get(&self, level: &usize) -> Stack<Ty> {
        self.0.get(level).cloned().unwrap_or(Stack::new())
    }
}
#[derive(Clone, Debug)]
struct Derivation {
    arg: DerivationMap,
    ret: DerivationMap,
}

impl Derivation {
    fn new() -> Derivation {
        let arg = DerivationMap::new();
        let ret = DerivationMap::new();
        Derivation { arg, ret }
    }
    fn insert_arg(&mut self, level: usize, ty: Ty) {
        self.arg.insert(level, ty);
    }
    fn insert_ret(&mut self, level: usize, ty: Ty) {
        self.ret.insert(level, ty);
    }
    fn get_arg(&self, level: &usize) -> Stack<Ty> {
        self.arg.get(level)
    }
    fn get_ret(&self, level: &usize) -> Stack<Ty> {
        self.ret.get(level)
    }
    fn merge(&mut self, derivation: &Derivation) {
        self.arg.merge_derivation_map(derivation.arg.clone());
        self.ret.merge_derivation_map(derivation.ret.clone());
    }
}
#[derive(Clone, Debug)]
struct CandidateType {
    ty: Ty,
    // level -> type map appeared in the derivation of ty so far.
    derivation: Derivation,
}

// inner purpose
enum Method {
    Conj,
    Disj,
}
impl CandidateType {
    fn new(ty: Ty, derivation: Derivation) -> CandidateType {
        CandidateType { ty, derivation }
    }
    fn memorize_arg(&mut self, level: usize) {
        self.derivation.insert_arg(level, self.ty.clone())
    }
    fn memorize_ret(&mut self, level: usize) {
        self.derivation.insert_ret(level, self.ty.clone())
    }
    fn merge_derivation(&mut self, derivation: &Derivation) {
        self.derivation.merge(derivation);
    }
    fn merge_inner(&mut self, c: &CandidateType, method: Method) {
        self.ty = match (self.ty.kind(), c.ty.kind()) {
            (TauKind::Proposition(c1), TauKind::Proposition(c2)) => match method {
                Method::Conj => Ty::mk_prop_ty(Atom::mk_conj(c1.clone(), c2.clone())),
                Method::Disj => Ty::mk_prop_ty(Atom::mk_disj(c1.clone(), c2.clone())),
            },
            (_, _) => panic!("fatal"),
        };
        self.merge_derivation(&c.derivation)
    }
    // only for bool type
    fn conjoin(c1: &CandidateType, c2: &CandidateType) -> CandidateType {
        let mut c1 = c1.clone();
        c1.merge_inner(c2, Method::Conj);
        c1
    }
    fn disjoin(c1: &CandidateType, c2: &CandidateType) -> CandidateType {
        let mut c1 = c1.clone();
        c1.merge_inner(c2, Method::Disj);
        c1
    }
    fn quantify(&mut self, x: Ident) {
        let t = match self.ty.kind() {
            TauKind::Proposition(c) => Ty::mk_prop_ty(Atom::mk_quantifier_int(
                crate::formula::QuantifierKind::Universal,
                x,
                c.clone(),
            )),
            TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => panic!("fatal"),
        };
        self.ty = t;
    }
}

impl From<Ty> for CandidateType {
    fn from(ty: Ty) -> Self {
        CandidateType {
            ty,
            derivation: Derivation::new(),
        }
    }
}

/// Since type environment can contain multiple candidate types,
/// we make sure that which one is suitable by considering them parallely.
#[derive(Debug)]
struct PossibleType {
    types: Vec<CandidateType>,
}
impl<'a, T: IntoIterator<Item = Ty>> From<T> for PossibleType {
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

    fn empty() -> PossibleType {
        PossibleType::new(Vec::new())
    }

    fn push(&mut self, ty: CandidateType) {
        self.types.push(ty);
    }

    fn conjoin(pt1: PossibleType, pt2: PossibleType) -> PossibleType {
        let mut ts = Vec::new();
        for pt1 in pt1.types.iter() {
            for pt2 in pt2.types.iter() {
                let pt1 = CandidateType::conjoin(pt1, pt2);
                ts.push(pt1);
            }
        }
        PossibleType::new(ts)
    }
    fn disjoin(pt1: PossibleType, pt2: PossibleType) -> PossibleType {
        let mut ts = Vec::new();
        for pt1 in pt1.types.iter() {
            for pt2 in pt2.types.iter() {
                let pt1 = CandidateType::disjoin(pt1, pt2);
                ts.push(pt1);
            }
        }
        PossibleType::new(ts)
    }
    fn quantify(&mut self, x: &Ident) {
        for pt1 in self.types.iter_mut() {
            pt1.quantify(*x);
        }
    }

    // check if ts' ⊂ self exists where ts' <: ts holds.
    fn check_subtype(&self, ts: &[Ty], constraint: &Constraint) -> bool {
        // is there possible derivation for each t in ts
        for t in ts {
            for s in self.types.iter() {
                let c = Ty::check_subtype(constraint, &s.ty, t);
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
fn type_check_top(_ctx: &mut Context, tenv: &mut Env, candidate: &G) -> Option<Derivation> {
    // tenv+ienv; constraint |- App(arg, ret): t
    fn handle_app(
        constraint: &Constraint,
        t: &Ty,
        tenv: &mut Env,
        ienv: &mut HashSet<Ident>,
        app_expr: &G,
    ) -> PossibleType {
        fn handle_inner(
            constraint: &Constraint,
            t: &Ty,
            tenv: &mut Env,
            ienv: &mut HashSet<Ident>,
            pred: &G,
        ) -> PossibleType {
            match pred.kind() {
                formula::hes::GoalKind::Var(x) => match tenv.get(x) {
                    Some(ts) => ts.iter().map(|t| t.add_context(constraint)).into(),
                    None => PossibleType::empty(),
                },
                formula::hes::GoalKind::App(predg, argg) => {
                    let pred_pt = handle_inner(constraint, t, tenv, ienv, predg);
                    // Case: the argument is integer
                    match check_int_expr(ienv, argg) {
                        // Case: the type of argument is int
                        Some(op) => {
                            let types = pred_pt
                                .types
                                .into_iter()
                                .map(|t| match t.ty.kind() {
                                    TauKind::IArrow(x, t2) => {
                                        CandidateType::new(t2.subst(x, &op), t.derivation.clone())
                                    }
                                    _ => panic!("fatal"),
                                })
                                .collect();
                            return PossibleType::new(types); // eary return
                        }
                        // Otherwise, we continue.
                        None => (),
                    };

                    // Case: the argument is not integer
                    let mut result_cts = Vec::new();
                    // we calculate the argument's type. we have to enumerate all the possible type of pt1.
                    'pt_iter: for ty in pred_pt.types {
                        let (arg_t, result_t) = match ty.ty.kind() {
                            TauKind::Arrow(arg, result) => (arg, result),
                            TauKind::Proposition(_) | TauKind::IArrow(_, _) => panic!("fatal"),
                        };
                        let arg_constraint =
                            Constraint::mk_conj(result_t.constraint_rty(), constraint.clone());
                        let mut result_ct: CandidateType = result_t.clone().into();
                        // check if there exists a derivation for all types in the intersection type.
                        for t in arg_t {
                            // check if arg_constraint |- argg: arg_t
                            match go(&arg_constraint, t, tenv, ienv, argg) {
                                Some(ct) => {
                                    result_ct.merge_derivation(&ct.derivation);
                                }
                                // if there exists a type in the intersection type that cannot be derived,
                                // we filter out this possible type.
                                None => continue 'pt_iter,
                            }
                        }
                        // Now that all the argument for `pred_pt` can be derived, we have candidatetype `result_t`
                        // with the derivations of `ct`s
                        result_cts.push(result_ct);
                    }
                    PossibleType::new(result_cts)
                }
                formula::hes::GoalKind::Constr(_)
                | formula::hes::GoalKind::Op(_)
                | formula::hes::GoalKind::Abs(_, _)
                | formula::hes::GoalKind::Conj(_, _)
                | formula::hes::GoalKind::Disj(_, _)
                | formula::hes::GoalKind::Univ(_, _) => panic!("fatal"),
            }
        }
        let mut pt = handle_inner(constraint, t, tenv, ienv, app_expr);
        for level in app_expr.aux.level_arg.iter() {
            for ct in pt.types.iter_mut() {
                ct.memorize_arg(*level);
            }
        }
        for level in app_expr.aux.level_ret.iter() {
            for ct in pt.types.iter_mut() {
                ct.memorize_ret(*level);
            }
        }
        pt
    }
    // we assume conjunction normal form and has the form (θ => a₁ a₂ ⋯) ∧ ⋯
    // constraint: Θ
    // Γ; Θ ⊢ c : t
    // function go constructs possible derivation trees by induction on the structure of c(ψ)
    //
    fn go(
        constraint: &Constraint,
        t: &Ty,
        tenv: &mut Env,
        ienv: &mut HashSet<Ident>,
        c: &G,
    ) -> Option<CandidateType> {
        fn go_inner(
            constraint: &Constraint,
            t: &Ty,
            tenv: &mut Env,
            ienv: &mut HashSet<Ident>,
            c: &G,
        ) -> Option<CandidateType> {
            match c.kind() {
                formula::hes::GoalKind::Constr(c) => {
                    if solver::smt::default_solver()
                        .solve_with_universal_quantifiers(&Atom::mk_implies(
                            constraint.clone(),
                            c.clone(),
                        ))
                        .is_sat()
                    {
                        Some(Ty::mk_prop_ty(c.clone().into()).into())
                    } else {
                        None
                    }
                }
                formula::hes::GoalKind::Var(x) => match tenv.get(x) {
                    Some(ts) => {
                        for s in ts {
                            // check if constraint |- s <: t
                            let c = Ty::check_subtype(constraint, s, t);
                            if solver::smt::default_solver()
                                .solve_with_universal_quantifiers(&c)
                                .is_sat()
                            {
                                return Some(t.clone().into());
                            }
                        }
                        None
                    }
                    None => {
                        panic!("{} is not found in env", x)
                    }
                },
                formula::hes::GoalKind::Conj(g1, g2) => {
                    let t1 = go(constraint, t, tenv, ienv, g1)?;
                    let t2 = go(constraint, t, tenv, ienv, g2)?;
                    Some(CandidateType::conjoin(&t1, &t2))
                }
                formula::hes::GoalKind::Disj(g1, g2) => {
                    let c1: Option<Atom> = g1.clone().into();
                    let (c, g, g_) = match c1 {
                        Some(c) => (c, g2, g1),
                        None => (g2.clone().into(), g1, g2),
                    };
                    let c_neg = c.negate().unwrap();
                    let t1 = go(&Atom::mk_conj(c_neg, constraint.clone()), t, tenv, ienv, g)?;
                    // type check of constraints (to track the type derivation, checking g2 is necessary)
                    let t2 = go(constraint, t, tenv, ienv, g_)?;
                    Some(CandidateType::disjoin(&t1, &t2))
                }
                formula::hes::GoalKind::Univ(x, g) => {
                    // to avoid the collision, we rename the variable.
                    assert!(!ienv.insert(x.id));
                    let mut pt = go(constraint, t, tenv, ienv, &g)?;
                    // quantify all the constraint.
                    pt.quantify(x.id);
                    ienv.remove(&x.id);
                    Some(pt)
                }
                formula::hes::GoalKind::App(_, _) => {
                    handle_app(constraint, t, tenv, ienv, c).types.pop()
                }
                formula::hes::GoalKind::Abs(v, g) => {
                    // 1. check t and calculate the argument's type.
                    // 2.
                    match t.kind() {
                        TauKind::IArrow(id, t) if v.ty.is_int() => {
                            let t = t.rename(id, &v.id);
                            assert!(!ienv.insert(v.id));
                            let ct = go(constraint, &t, tenv, ienv, g)?;
                            ienv.remove(&v.id);
                            let ty = Ty::mk_iarrow(v.id, ct.ty);
                            Some(CandidateType::new(ty, ct.derivation))
                        }
                        TauKind::Arrow(ts, t) if !v.ty.is_int() => {
                            for t in ts {
                                tenv.add(v.id, t.clone());
                            }
                            let ct = go(constraint, t, tenv, ienv, g)?;
                            let ret_ty = ct.ty;
                            let ty = Ty::mk_arrow(ts.clone(), ret_ty);
                            Some(CandidateType::new(ty, ct.derivation))
                        }
                        _ => panic!("fatal"),
                    }
                }
                // op is always handled by App(x, op)
                formula::hes::GoalKind::Op(_) => panic!("fatal error"),
            }
        }
        go_inner(constraint, t, tenv, ienv, c).map(|mut ct| {
            // memorize the type assignment to each expr
            for level in c.aux.level_arg.iter() {
                ct.memorize_arg(*level);
            }
            for level in c.aux.level_ret.iter() {
                ct.memorize_ret(*level);
            }
            ct
        })
    }

    let mut ienv = HashSet::new();
    go(
        &Constraint::mk_true(),
        &Ty::mk_prop_ty(Constraint::mk_true()),
        tenv,
        &mut ienv,
        &candidate,
    )
    .map(|t| t.derivation)
}

pub fn generate_constraint(
    candidate: &Candidate,
    problem: &Problem,
    tenv: &mut Env,
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
