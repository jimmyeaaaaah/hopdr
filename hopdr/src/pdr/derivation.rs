use super::rtype::{Refinement, TBot, Tau, TauKind, TypeEnvironment};
use crate::formula::hes::{Goal, GoalBase, Problem as ProblemBase};
use crate::formula::{self, DerefPtr, FirstOrderLogic};
use crate::formula::{
    chc, fofml, pcsp, Constraint, Ident, Logic, Negation, Op, Rename, Subst, Top, Variable,
};
use crate::solver;
use crate::title;

use rpds::{HashTrieMap, Stack};

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::Formatter;

type Atom = fofml::Atom;
type Candidate = Goal<Constraint>;
type Ty = Tau<Atom>;
type Env = TypeEnvironment<Ty>;
type Problem = ProblemBase<Constraint>;
type CHC = chc::CHC<chc::Atom, Atom>;
type PCSP = pcsp::PCSP<fofml::Atom>;

/// track_idents maps predicate in Problem to the idents of lambda abstraction exprs
///
/// we can name each expr by using `aux.id`. for each expansion of a predicate, we memorize
/// this id.
/// example:
///  F x f = φ₁
///  ψ = F ... /\ F ...
/// then:
///  ψ = (λx1. λf. [x1/x]φ₁)ˣ ... /\ (λx2. λf. [x2/x]φ₁)ʸ ...
/// and track_idents
///  - F = [x, y]
fn subst_predicate(
    candidate: &G,
    problem: &Problem,
    track_idents: &mut HashMap<Ident, Vec<Ident>>,
) -> G {
    match candidate.kind() {
        formula::hes::GoalKind::Constr(_) | formula::hes::GoalKind::Op(_) => candidate.clone(),
        formula::hes::GoalKind::Var(x) => match problem.get_clause(x) {
            Some(clause) => {
                let body: G = clause.body.clone().into(); // assign a fresh id translating Candidate -> G
                track_idents
                    .entry(*x)
                    .or_insert_with(|| Vec::new())
                    .push(body.aux.id);
                match body.kind() {
                    formula::hes::GoalKind::Abs(v, g) => {
                        let id = v.id;
                        let new_id = Ident::fresh();
                        let g = g.rename(&id, &new_id);
                        G::mk_abs_t(Variable::mk(new_id, v.ty.clone()), g, body.aux.clone())
                    }
                    _ => panic!("body must be a lambda abstraction but got {}", body),
                }
            }
            None => candidate.clone(),
        },
        formula::hes::GoalKind::Abs(v, g) => {
            let g = subst_predicate(g, problem, track_idents);
            G::mk_abs_t(v.clone(), g, candidate.aux.clone())
        }
        formula::hes::GoalKind::App(x, y) => {
            let x = subst_predicate(x, problem, track_idents);
            let y = subst_predicate(y, problem, track_idents);
            G::mk_app_t(x, y, candidate.aux.clone())
        }
        formula::hes::GoalKind::Conj(x, y) => {
            let x = subst_predicate(x, problem, track_idents);
            let y = subst_predicate(y, problem, track_idents);
            G::mk_conj_t(x, y, candidate.aux.clone())
        }
        formula::hes::GoalKind::Disj(x, y) => {
            let x = subst_predicate(x, problem, track_idents);
            let y = subst_predicate(y, problem, track_idents);
            G::mk_disj_t(x, y, candidate.aux.clone())
        }
        formula::hes::GoalKind::Univ(v, g) => {
            let g = subst_predicate(g, problem, track_idents);
            G::mk_univ_t(v.clone(), g, candidate.aux.clone())
        }
    }
}
type Level = usize;
struct ReductionInfo {
    level: Level,
    arg: G,
    arg_var: Variable,
    old_id: Ident,
}
impl ReductionInfo {
    fn new(level: Level, arg: G, arg_var: Variable, old_id: Ident) -> ReductionInfo {
        ReductionInfo {
            level,
            arg,
            arg_var,
            old_id,
        }
    }
}

// perhaps we will attach auxiliary information so we prepare another struct for reduction sequence
struct Reduction {
    app_expr: G,
    // (λx. λy. ψ) arg1 arg2  -> ψ
    predicate: G, //λx. λy. ψ
    // args and arg_vras
    //
    // Level: this is the id of this reduction.
    // this value is memorized in the memory of each expression
    // for each reduction. That is, when we have reduction
    //    expr1 expr2 -> expr3
    // this id is memorized in expr2's memory (as the argument) and expr3's memory (as the return value)
    args: Stack<ReductionInfo>,
    // the result of beta reduction; predicate expr -> result
    result: G,
    // predicate's free variables of type int
    fvints: HashSet<Ident>,
    argints: HashSet<Ident>,
    // constraint of the redux where this reduction happens
    constraint: Constraint,
}

impl fmt::Display for Reduction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[Reduction ")?;
        for a in self.args.iter() {
            write!(f, "{}, ", a.level)?;
        }
        write!(f, "] fvints: {:?}", self.fvints)?;
        writeln!(f, " constraint: {}", self.constraint)?;
        writeln!(f, "{} ", self.predicate)?;
        for arg in self.args.iter() {
            writeln!(f, "- {} ", arg.arg)?;
        }
        write!(f, "\n ==> {}", self.result)
    }
}

impl Reduction {
    fn new(
        app_expr: G,
        predicate: G,
        result: G,
        fvints: HashSet<Ident>,
        argints: HashSet<Ident>,
        constraint: Constraint,
    ) -> Reduction {
        Reduction {
            app_expr,
            predicate,
            args: Stack::new(),
            result,
            fvints,
            argints,
            constraint,
        }
    }
    fn append_reduction(&mut self, reduction_info: ReductionInfo, result: G, app_expr: G) {
        if reduction_info.arg_var.ty.is_int() {
            self.fvints.insert(reduction_info.old_id);
            self.argints.insert(reduction_info.old_id);
        }
        self.result = result;
        self.app_expr = app_expr;
        self.args.push_mut(reduction_info);
    }
    fn level(&self) -> usize {
        self.args.peek().unwrap().level
    }
}

#[derive(Clone, Debug)]
struct TypeMemory {
    level_arg: Stack<usize>,
    id: Ident,
}
impl TypeMemory {
    fn new() -> TypeMemory {
        TypeMemory {
            level_arg: Stack::new(),
            id: Ident::fresh(),
        }
    }
    fn add_arg_level(&mut self, level: usize) {
        self.level_arg = self.level_arg.push(level)
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
type G = GoalBase<Constraint, TypeMemory>;

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

    fn go(goal: &G, level: &mut usize) -> Option<(G, Reduction)> {
        /// returns Some(_) if reduction happens in goal; otherwise None
        /// left of the return value: the reduced term
        /// right of the return value: the abstraction in the redux.
        fn go_(
            goal: &G,
            level: usize,
            fvints: &mut HashSet<Ident>,
            argints: &mut HashSet<Ident>,
            constraint: Constraint,
        ) -> Option<(G, Reduction)> {
            fn generate_reduction_info(
                level: usize,
                predicate: &G,
                arg: &G,
            ) -> Option<(G, ReductionInfo)> {
                match predicate.kind() {
                    GoalKind::Abs(x, g) => {
                        let mut arg = arg.clone();
                        // track the type of argument
                        arg.aux.add_arg_level(level);

                        let new_var = Variable::fresh(x.ty.clone());
                        let new_g = g.rename(&x.id, &new_var.id);
                        let old_id = x.id;
                        let mut ret = new_g.subst(&new_var, &arg);
                        // introduce a new fresh variable to identify this expr
                        ret.aux.id = Ident::fresh();
                        let reduction_info =
                            ReductionInfo::new(level, arg.clone(), new_var, old_id);
                        Some((ret.clone(), reduction_info))
                    }
                    _ => None,
                }
            }
            match goal.kind() {
                GoalKind::App(predicate, arg) => {
                    match generate_reduction_info(level, predicate, arg) {
                        // App(App(...(Abs(...) arg1) .. argn)
                        Some((ret, reduction_info)) => {
                            let mut reduction = Reduction::new(
                                goal.clone(),
                                predicate.clone(),
                                ret.clone(),
                                fvints.clone(),
                                argints.clone(),
                                constraint.clone(),
                            );
                            reduction.append_reduction(reduction_info, ret.clone(), goal.clone());
                            return Some((ret.clone(), reduction));
                        }
                        None => (),
                    };
                    match go_(predicate, level, fvints, argints, constraint.clone()) {
                        Some((ret, mut reduction)) => {
                            // case reduced above like App(App(Abs, arg)) -> App(Abs, arg)
                            return match generate_reduction_info(reduction.level() + 1, &ret, arg) {
                                Some((ret, reduction_info)) => {
                                    reduction.append_reduction(
                                        reduction_info,
                                        ret.clone(),
                                        goal.clone(),
                                    );
                                    Some((ret, reduction))
                                }
                                None => Some((G::mk_app_t(ret, arg.clone(), goal.aux.clone()), reduction)),
                            };
                        }
                        None => (),
                    };
                    go_(arg, level, fvints, argints, constraint.clone()).map(|(arg, pred)| {
                        (G::mk_app_t(predicate.clone(), arg, goal.aux.clone()), pred)
                    })
                }
                GoalKind::Conj(g1, g2) => go_(g1, level, fvints, argints, constraint.clone())
                    .map(|(g1, p)| (G::mk_conj_t(g1, g2.clone(), goal.aux.clone()), p))
                    .or_else(|| {
                        go_(g2, level, fvints, argints, constraint.clone())
                            .map(|(g2, p)| (G::mk_conj_t(g1.clone(), g2, goal.aux.clone()), p))
                    }),
                GoalKind::Disj(g1, g2) => {
                    let c1: Option<Constraint> = g1.clone().into();
                    match c1 {
                        Some(c1) => {
                            let constraint = Constraint::mk_conj(c1.negate().unwrap(), constraint);
                            go_(g2, level, fvints, argints, constraint).map(|(g2, p)| {
                                (G::mk_disj_t(g1.clone(), g2.clone(), goal.aux.clone()), p)
                            })
                        }
                        None => {
                            let c2: Option<Constraint> = g2.clone().into();
                            match c2 {
                                Some(c2) => {
                                    let constraint =
                                        Constraint::mk_conj(c2.negate().unwrap(), constraint);
                                    go_(g1, level, fvints, argints, constraint).map(|(g1, p)| {
                                        (G::mk_disj_t(g1.clone(), g2.clone(), goal.aux.clone()), p)
                                    })
                                }
                                None => {
                                    panic!("fatal")
                                }
                            }
                        }
                    }
                }
                GoalKind::Univ(x, g) => {
                    let mut saved = false;
                    if x.ty.is_int() && !fvints.insert(x.id) {
                        // x is type int and fvints already has x.id
                        saved = true;
                    }
                    let r = go_(g, level, fvints, argints, constraint)
                        .map(|(g, p)| (G::mk_univ_t(x.clone(), g, goal.aux.clone()), p));
                    if x.ty.is_int() && !saved {
                        fvints.remove(&x.id);
                    }
                    r
                }
                GoalKind::Abs(x, g) => {
                    let mut saved = false;
                    let mut saved_arg = false;
                    if x.ty.is_int() && !fvints.insert(x.id) {
                        // x is type int and fvints already has x.id
                        saved = true;
                    }
                    if x.ty.is_int() && !argints.insert(x.id) {
                        // x is type int and fvints already has x.id
                        saved_arg = true;
                    }

                    let r = go_(g, level, fvints, argints, constraint)
                        .map(|(g, p)| (G::mk_abs_t(x.clone(), g, goal.aux.clone()), p));
                    if x.ty.is_int() && !saved {
                        fvints.remove(&x.id);
                    }
                    if x.ty.is_int() && !saved_arg {
                        argints.remove(&x.id);
                    }
                    //debug!("abs={} ({})", r.is_some(), goal);
                    r
                }
                GoalKind::Constr(_) | GoalKind::Var(_) | GoalKind::Op(_) => None,
            }
        }
        go_(
            goal,
            *level,
            &mut HashSet::new(),
            &mut HashSet::new(),
            Constraint::mk_true(),
        )
        .map(|(ret, reduction)| {
            *level = reduction.level() + 1;
            (ret, reduction)
        })
    }
    let mut level = 0usize;
    let mut seq = Vec::new();
    let mut reduced = goal.clone();

    debug!("{}", reduced);
    while let Some((g, r)) = go(&reduced, &mut level) {
        reduced = g.clone();
        //debug!("-> {}", reduced);
        //debug!("-> {}", r);
        debug!("->  {}", reduced);

        seq.push(r);
    }
    (seq, reduced)
}

struct Context {
    normal_form: G,
    track_idents: HashMap<Ident, Vec<Ident>>,
    reduction_sequence: Vec<Reduction>,
    infer_polymorphic_type: bool,
}

impl Context {
    fn new(
        normal_form: G,
        track_idents: HashMap<Ident, Vec<Ident>>,
        reduction_sequence: Vec<Reduction>,
    ) -> Context {
        // default
        let infer_polymorphic_type = false;
        Context {
            normal_form,
            track_idents,
            reduction_sequence,
            infer_polymorphic_type,
        }
    }
    fn retrieve_from_track_idents(
        &self,
        model: &chc::Model,
        derivation: &Derivation,
    ) -> TypeEnvironment<Tau<Constraint>> {
        // TODO NEXT: we can retrieve it from context.track_idents
        let model = &model.model;
        let mut result_env = TypeEnvironment::new();
        for (pred_name, ids) in self.track_idents.iter() {
            for id in ids {
                let tys = derivation.expr.get_opt(id).unwrap();
                for ty in tys.iter() {
                    debug!("{}: {}", pred_name, ty);
                    debug!("{:?}", model);
                    let ty = ty.ty.clone();
                    result_env.add(*pred_name, ty.assign(&model));
                }
            }
        }
        result_env
    }
    /// Γ ⊢ ψ : •<T>
    ///
    /// tenv: Γ
    /// candidate: ψ
    /// ctx.abstraction_types: is used for handling types appeared in derivations
    /// assumption: candidate has a beta-normal form of type *.
    fn type_check_top(&mut self, tenv: &mut Env) -> Option<Derivation> {
        // tenv+ienv; constraint |- App(arg, ret): t
        fn handle_app(
            constraint: &Atom,
            tenv: &mut Env,
            ienv: &mut HashSet<Ident>,
            app_expr: &G,
        ) -> PossibleType {
            fn handle_inner(
                constraint: &Atom,
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
                        let pred_pt = handle_inner(constraint, tenv, ienv, predg);
                        // Case: the argument is integer
                        match argg.check_int_expr(ienv) {
                            // Case: the type of argument is int
                            Some(op) => {
                                let types = pred_pt
                                    .types
                                    .into_iter()
                                    .map(|t| match t.ty.kind() {
                                        TauKind::IArrow(x, t2) => CandidateType::new(
                                            t2.subst(x, &op),
                                            t.derivation.clone(),
                                        ),
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
                            let mut result_ct: CandidateType = result_t.clone().into();
                            // check if there exists a derivation for all types in the intersection type.
                            for t in arg_t {
                                let arg_constraint =
                                    Atom::mk_conj(t.rty_no_exists(), constraint.clone());
                                debug!("t: {}", t);
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
                    | formula::hes::GoalKind::Univ(_, _) => panic!("fatal: {}", pred),
                }
            }
            let mut pt = handle_inner(constraint, tenv, ienv, app_expr);
            for level in app_expr.aux.level_arg.iter() {
                for ct in pt.types.iter_mut() {
                    ct.memorize(*level);
                }
            }
            for ct in pt.types.iter_mut() {
                ct.set_types(app_expr, constraint.clone());
            }
            debug!("handle_app: {} |- {} : {} ", constraint, app_expr, pt);
            pt
        }
        // we assume conjunction normal form and has the form (θ => a₁ a₂ ⋯) ∧ ⋯
        // constraint: Θ
        // Γ; Θ ⊢ c : t
        // function go constructs possible derivation trees by induction on the structure of c(ψ)
        //
        fn go(
            constraint: &Atom,
            t: &Ty,
            tenv: &mut Env,
            ienv: &mut HashSet<Ident>,
            c: &G,
        ) -> Option<CandidateType> {
            fn go_inner(
                constraint: &Atom,
                t: &Ty,
                tenv: &mut Env,
                ienv: &mut HashSet<Ident>,
                c: &G,
            ) -> Option<CandidateType> {
                match c.kind() {
                    formula::hes::GoalKind::Constr(c) => {
                        let constraint = constraint.clone().into();
                        let type_constr = match t.kind() {
                            TauKind::Proposition(type_constr) => type_constr.clone().into(),
                            TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => panic!("fatal"),
                        };
                        if solver::smt::default_solver()
                            .solve_with_universal_quantifiers(&Constraint::mk_implies(
                                Constraint::mk_conj(constraint, type_constr),
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
                                let c = c.into();
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
                        let c1: Option<Constraint> = g1.clone().into();
                        let (c, g, g_) = match c1 {
                            Some(c) => (c, g2, g1),
                            None => (g2.clone().into(), g1, g2),
                        };
                        let c_neg = c.negate().unwrap();
                        let t1 = go(
                            &Atom::mk_conj(c_neg.into(), constraint.clone()),
                            t,
                            tenv,
                            ienv,
                            g,
                        )?;
                        // type check of constraints (to track the type derivation, checking g2 is necessary)
                        let t2 = go(
                            &Atom::mk_conj(c.into(), constraint.clone()),
                            t,
                            tenv,
                            ienv,
                            g_,
                        )?;
                        Some(CandidateType::disjoin(&t1, &t2))
                    }
                    formula::hes::GoalKind::Univ(x, g) => {
                        // to avoid the collision, we rename the variable.
                        assert!(ienv.insert(x.id));
                        let pt = go(constraint, t, tenv, ienv, &g);
                        ienv.remove(&x.id);
                        let mut pt = pt?;
                        // quantify all the constraint.
                        pt.quantify(x.id);
                        Some(pt)
                    }
                    formula::hes::GoalKind::App(_, _) => {
                        handle_app(constraint, tenv, ienv, c).types.pop()
                    }
                    formula::hes::GoalKind::Abs(v, g) => {
                        // 1. check t and calculate the argument's type.
                        // 2.
                        match t.kind() {
                            TauKind::IArrow(id, t) if v.ty.is_int() => {
                                let t = t.rename(id, &v.id);
                                assert!(ienv.insert(v.id));
                                let ct = go(constraint, &t, tenv, ienv, g);
                                ienv.remove(&v.id);
                                let ct = ct?;
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
                debug!(
                    "type_check_go({}): {} |- {} : {}",
                    c.aux.id, constraint, c, ct
                );
                // memorize the type assignment to each expr
                for level in c.aux.level_arg.iter() {
                    ct.memorize(*level);
                }
                ct.set_types(c, constraint.clone());
                ct
            })
        }
        title!("type_check_top");
        debug!("tenv: {}", tenv);
        debug!("{}", self.normal_form);
        let mut ienv = HashSet::new();
        go(
            &Atom::mk_true(),
            &Ty::mk_prop_ty(Atom::mk_true()),
            tenv,
            &mut ienv,
            &self.normal_form,
        )
        .map(|t| t.derivation)
    }
    fn infer_type(
        &mut self,
        mut derivation: Derivation,
    ) -> Option<TypeEnvironment<Tau<Constraint>>> {
        //let mut constraints = Vec::new();
        let mut clauses = Vec::new();
        for reduction in self.reduction_sequence.iter().rev() {
            title!("Reduction");
            debug!("{}", reduction);
            let ret_tys = derivation.get_expr_ty(&reduction.result.aux.id);
            if ret_tys.iter().len() == 0 {
                debug!(
                    "search for id={},expr={} ",
                    reduction.result.aux.id, reduction.result
                );
                title!("no ret_tys");
                panic!("fatal");
            }

            let mut arg_tys = Vec::new();
            for reduction in reduction.args.iter() {
                let arg_ty = if reduction.arg_var.ty.is_int() {
                    either::Left(reduction.arg_var.id)
                } else {
                    // 1. get the corresponding types
                    let arg_ty: Vec<Ty> = derivation
                        .get_arg(&reduction.level)
                        .iter()
                        .cloned()
                        .collect();
                    let arg_ty = if arg_ty.len() == 0 {
                        vec![Ty::mk_bot(&reduction.arg_var.ty)]
                    } else {
                        arg_ty
                    };
                    either::Right(arg_ty)
                };
                arg_tys.push(arg_ty);
            }

            for ret_ty in ret_tys.iter() {
                debug!("ret_ty: {}", ret_ty);
                let SavedTy {
                    ty: ret_ty,
                    constraint: ret_ty_constraint,
                } = ret_ty.clone();

                let tmp_ret_ty = ret_ty.clone_with_rty_template(
                    ret_ty_constraint.clone(),
                    &mut if self.infer_polymorphic_type {
                        reduction.fvints.clone()
                    } else {
                        reduction.argints.clone()
                    },
                );

                let mut tmp_ty = tmp_ret_ty.clone();
                let mut body_ty = ret_ty.clone();
                let mut app_expr_ty = tmp_ret_ty.clone();

                for (arg_ty, reduction) in arg_tys.iter().zip(reduction.args.iter()) {
                    match arg_ty {
                        either::Left(ident) => {
                            body_ty = body_ty.deref_ptr(ident).rename(&ident, &reduction.old_id);

                            tmp_ty = Tau::mk_iarrow(reduction.old_id, tmp_ty);

                            let op: Op = reduction.arg.clone().into();
                            app_expr_ty = app_expr_ty.subst(&reduction.old_id, &op);
                        }
                        either::Right(arg_ty) => {
                            tmp_ty = Ty::mk_arrow(arg_ty.clone(), tmp_ty);
                        }
                    };
                }
                // 3. generate constraint from subtyping t <: arg_ty -> ret_ty, and append them to constraints
                // constrain by `old <= new_tmpty <= top`
                //let mut argints = reduction.argints.clone();

                debug!("inferred type: {}", tmp_ty);
                debug!("body type: {}", body_ty);
                debug!("app_expr_type: {}", app_expr_ty);

                // TODO: I think this is ok
                //let constraint = Atom::mk_implies_opt(tmp_ty.rty_no_exists(), body_ty.rty()).unwrap();
                let constraint = Atom::mk_implies_opt(
                    Atom::mk_conj(tmp_ty.rty_no_exists(), ret_ty_constraint.clone()),
                    body_ty.rty_no_exists(),
                )
                .unwrap();

                let constraint2 =
                    Atom::mk_implies_opt(ret_ty_constraint.clone(), app_expr_ty.rty_no_exists())
                        .unwrap();
                let constraint = Atom::mk_conj(constraint, constraint2);
                // 2. create a template type from `ty` and free variables `fvints`
                match constraint.to_chcs_or_pcsps() {
                    either::Left(chcs) => {
                        debug!("constraints");
                        for c in chcs {
                            debug!("  - {}", c);
                            clauses.push(c);
                        }
                    }
                    either::Right(pcsps) => {
                        debug!("constriant: {}", constraint);
                        debug!("failed to translate the constraint to chcs");
                        for c in pcsps {
                            debug!("{}", c)
                        }
                        panic!("fatal")
                    }
                }
                // 4. for each `level` in reduction.candidate.aux, we add t to Derivation
                for level in reduction.predicate.aux.level_arg.iter() {
                    derivation.arg.insert(*level, tmp_ty.clone());
                }
                let tmp_saved_ty = SavedTy::mk(tmp_ty, ret_ty_constraint.clone());
                derivation
                    .expr
                    .set(reduction.predicate.aux.id, tmp_saved_ty);

                for level in reduction.app_expr.aux.level_arg.iter() {
                    derivation.arg.insert(*level, app_expr_ty.clone())
                }
                debug!(
                    "app_expr({}): {}",
                    reduction.app_expr.aux.id, reduction.app_expr
                );
                let app_expr_saved_ty = SavedTy::mk(app_expr_ty, ret_ty_constraint.clone());
                derivation
                    .expr
                    .set(reduction.app_expr.aux.id, app_expr_saved_ty);
            }
            debug!("");
        }
        clauses.iter().for_each(|c| debug!("- {}", c));
        // 4. solve the constraints by using the interpolation solver
        let m = match solver::chc::default_solver().solve(&clauses) {
            solver::chc::CHCResult::Sat(m) => m,
            solver::chc::CHCResult::Unsat => return None,
            solver::chc::CHCResult::Unknown => {
                panic!(
                    "PDR fails to infer a refinement type due to the background CHC solver's error"
                )
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
        debug!("{}", model);

        // collect needed predicate
        // 5. from the model, generate a type environment
        Some(self.retrieve_from_track_idents(&model, &derivation))
    }
}

fn reduce_until_normal_form(candidate: &Candidate, problem: &Problem) -> Context {
    let mut track_idents = HashMap::new();
    let candidate = candidate.clone().into(); // assign `aux` to candidate.
    let goal = subst_predicate(&candidate, problem, &mut track_idents);
    let goal = goal.alpha_renaming();
    title!("generate_reduction_sequence");
    let (reduction_sequence, normal_form) = generate_reduction_sequence(&goal);
    Context::new(normal_form, track_idents, reduction_sequence)
}

#[derive(Clone, Debug)]
struct SavedTy {
    ty: Ty,
    constraint: Atom,
}

impl fmt::Display for SavedTy {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}; {}", self.constraint, self.ty)
    }
}

impl SavedTy {
    fn kind<'a>(&'a self) -> &'a TauKind<Atom> {
        self.ty.kind()
    }
    fn mk(ty: Ty, constraint: Atom) -> SavedTy {
        SavedTy { ty, constraint }
    }
    fn deref_ptr(&self, ident: &Ident) -> SavedTy {
        let ty = self.ty.deref_ptr(ident);
        let constraint = self.constraint.deref_ptr(ident);
        SavedTy::mk(ty, constraint)
    }
}

impl Rename for SavedTy {
    fn rename(&self, x: &Ident, y: &Ident) -> Self {
        let ty = self.ty.rename(x, y);
        let constraint = self.constraint.rename(x, y);
        SavedTy::mk(ty, constraint)
    }
}

#[derive(Clone, Debug)]
struct DerivationMap<ID: Eq + std::hash::Hash + Copy, T>(HashTrieMap<ID, Stack<T>>);
impl<ID: Eq + std::hash::Hash + Copy, T: Clone> DerivationMap<ID, T> {
    fn new() -> DerivationMap<ID, T> {
        DerivationMap(HashTrieMap::new())
    }
    fn merge_derivation_map(&mut self, y: DerivationMap<ID, T>) {
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
    fn insert(&mut self, level: ID, ty: T) {
        let st = match self.0.get(&level) {
            Some(st) => st.clone(),
            None => Stack::new(),
        };
        self.0 = self.0.insert(level, st.push(ty.clone()))
    }
    fn set(&mut self, ident: ID, ty: T) {
        // overwrite the current assignment
        // the expr with `level` id can be copied.
        // however, for the purpose of tracking the type of the result expr
        // of beta-reduction, what we want to know is the latest type assignment.
        // By going back along with the reduction sequence, this can be achieved.
        self.0 = self.0.insert(ident, Stack::new().push(ty))
    }
    fn get(&self, level: &ID) -> Stack<T> {
        self.0.get(level).cloned().unwrap_or(Stack::new())
    }
    fn get_opt(&self, level: &ID) -> Option<Stack<T>> {
        self.0.get(level).cloned()
    }
}
#[derive(Clone, Debug)]
struct Derivation {
    arg: DerivationMap<usize, Ty>,
    expr: DerivationMap<Ident, SavedTy>,
}

impl Derivation {
    fn new() -> Derivation {
        let arg = DerivationMap::new();
        let expr = DerivationMap::new();
        Derivation { arg, expr }
    }
    fn memorize(&mut self, level: usize, ty: Ty) {
        self.arg.insert(level, ty);
    }
    // memorize expr : ty in a derivation
    fn memorize_type_judgement(&mut self, expr: &G, ty: SavedTy) {
        self.expr.set(expr.aux.id, ty);
    }
    fn get_arg(&self, level: &usize) -> Stack<Ty> {
        self.arg.get(level)
    }
    fn get_expr_ty(&self, level: &Ident) -> Stack<SavedTy> {
        self.expr.get(level)
    }
    fn merge(&mut self, derivation: &Derivation) {
        self.arg.merge_derivation_map(derivation.arg.clone());
        self.expr.merge_derivation_map(derivation.expr.clone());
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
    fn memorize(&mut self, level: usize) {
        self.derivation.memorize(level, self.ty.clone())
    }
    fn set_types(&mut self, expr: &G, constraint: Atom) {
        let ty = self.ty.clone();
        let saved_ty = SavedTy::mk(ty, constraint);
        self.derivation.memorize_type_judgement(expr, saved_ty);
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
            (_, _) => panic!("fatal: self.ty={} and c.ty={}", self.ty, c.ty),
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
        let ty = match self.ty.kind() {
            TauKind::Proposition(c) => Ty::mk_prop_ty(Atom::mk_quantifier_int(
                crate::formula::QuantifierKind::Universal,
                x,
                c.clone(),
            )),
            TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => panic!("fatal"),
        };
        self.ty = ty;
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

impl fmt::Display for CandidateType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.ty)
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
impl From<Ty> for PossibleType {
    fn from(t: Ty) -> Self {
        let t = t.into();
        let mut types = Vec::new();
        types.push(t);
        PossibleType::new(types)
    }
}
impl fmt::Display for PossibleType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.types.len() > 0 {
            write!(f, "{}", self.types[0])?;
            for t in self.types[1..].iter() {
                write!(f, " /\\ {}", t)?;
            }
        }
        Ok(())
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

// takes g and formats it and returns (Θ, g') where Θ => g'
fn format_cnf_clause(g: G) -> (Constraint, G) {
    match g.kind() {
        formula::hes::GoalKind::Constr(_)
        | formula::hes::GoalKind::Var(_)
        | formula::hes::GoalKind::Abs(_, _)
        | formula::hes::GoalKind::App(_, _) => (Constraint::mk_true(), g.clone()),
        formula::hes::GoalKind::Disj(g1, g2) => {
            let c: Option<Constraint> = g1.clone().into();
            match c {
                Some(c) => (c.negate().unwrap(), g2.clone()),
                None => {
                    let c: Option<Constraint> = g2.clone().into();
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

pub fn search_for_type(
    candidate: &Candidate,
    problem: &Problem,
    tenv: &mut Env,
) -> Option<TypeEnvironment<Tau<Constraint>>> {
    crate::title!("search_for_type");
    debug!("{}", candidate);
    // TODO: expand candidate once based on problem.
    let mut ctx = reduce_until_normal_form(candidate, problem);
    ctx.infer_polymorphic_type = true;
    debug!("{}", ctx.normal_form);
    //let candidate = ctx.normal_form.clone();
    let derivation = ctx.type_check_top(tenv)?;
    ctx.infer_type(derivation)
}
