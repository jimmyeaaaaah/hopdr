use super::optimizer;
use super::optimizer::{variable_info, InferenceResult, Optimizer};
use super::rtype::{PolymorphicType, Refinement, TBot, Tau, TauKind, TyEnv, TypeEnvironment};

use crate::formula::hes::{Goal, GoalBase, GoalKind, Problem as ProblemBase};
use crate::formula::{self, DerefPtr, FirstOrderLogic};
use crate::formula::{
    chc, fofml, Constraint, Fv, Ident, Logic, Negation, Op, Rename, Subst, Top, Variable,
};
use crate::solver;
use crate::title;
use crate::util::Pretty;

use rpds::{HashTrieMap, Stack};

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::Formatter;

type Atom = fofml::Atom;
type Candidate = Goal<Constraint>;
pub(crate) type Ty = Tau<Atom>;
type PTy = PolymorphicType<Tau<Atom>>;
type Env = TypeEnvironment<PTy>;
type Problem = ProblemBase<Constraint>;

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
    args: Vec<ReductionInfo>,
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
            args: Vec::new(),
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
        self.args.push(reduction_info);
    }
    fn level(&self) -> usize {
        self.args[self.args.len() - 1].level
    }
}

#[derive(Clone, Debug)]
struct TypeMemory {
    level_arg: Stack<usize>,
    id: Ident, // unique id for each sub expression of the formula
    old_ids: Stack<Ident>,
    tys: Option<Vec<Ty>>,
}
impl TypeMemory {
    fn new() -> TypeMemory {
        TypeMemory {
            level_arg: Stack::new(),
            id: Ident::fresh(),
            old_ids: Stack::new(),
            tys: None,
        }
    }
    fn add_arg_level(&mut self, level: usize) {
        self.level_arg = self.level_arg.push(level)
    }
    fn set_tys(&mut self, tys: Option<Vec<Ty>>) {
        self.tys = tys;
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

impl TypeMemory {
    fn update_id(&self) -> Self {
        let mut tm = self.clone();
        let old_id = tm.id;
        tm.id = Ident::fresh();
        tm.old_ids.push_mut(old_id);
        tm
    }
}

impl GoalBase<Constraint, TypeMemory> {
    fn update_ids(&self) -> Self {
        let mut expr = match self.kind() {
            GoalKind::Constr(_) | GoalKind::Op(_) | GoalKind::Var(_) => self.clone(),
            GoalKind::App(x, y) => {
                let x = x.update_ids();
                let y = y.update_ids();
                Self::mk_app(x, y)
            }
            GoalKind::Conj(x, y) => {
                let x = x.update_ids();
                let y = y.update_ids();
                Self::mk_conj(x, y)
            }
            GoalKind::Disj(x, y) => {
                let x = x.update_ids();
                let y = y.update_ids();
                Self::mk_disj(x, y)
            }
            GoalKind::Abs(v, x) => {
                let x = x.update_ids();
                Self::mk_abs(v.clone(), x)
            }
            GoalKind::Univ(v, x) => {
                let x = x.update_ids();
                Self::mk_univ(v.clone(), x)
            }
        };
        expr.aux = self.aux.update_id();
        expr
    }
}

fn generate_reduction_sequence(goal: &G, optimizer: &mut dyn Optimizer) -> (Vec<Reduction>, G) {
    /// returns
    /// 1. Some(Candidate): substituted an app
    /// 2. None: not yet
    fn go(optimizer: &mut dyn Optimizer, goal: &G, level: &mut usize) -> Option<(G, Reduction)> {
        /// returns Some(_) if reduction happens in goal; otherwise None
        /// left of the return value: the reduced term
        /// right of the return value: the abstraction in the redux.
        fn go_(
            optimizer: &mut dyn Optimizer,
            goal: &G,
            level: usize,
            fvints: &mut HashSet<Ident>,
            argints: &mut HashSet<Ident>,
            constraint: Constraint,
        ) -> Option<(G, Reduction)> {
            fn generate_reduction_info(
                optimizer: &mut dyn Optimizer,
                level: usize,
                predicate: &G,
                arg: &G,
                idents: &HashSet<Ident>, // idents passed to optimizer when generating a shared type template
            ) -> Option<(G, ReductionInfo)> {
                match predicate.kind() {
                    GoalKind::Abs(x, g) => {
                        let mut arg = arg.clone();
                        // track the type of argument
                        arg.aux.add_arg_level(level);

                        let new_var = Variable::fresh(x.ty.clone());
                        let new_g = g.rename(&x.id, &new_var.id);
                        let old_id = x.id;

                        // [feature shared_ty]
                        // introduce type sharing
                        match arg.aux.tys {
                            // if a shared type exists, we reuse it.
                            Some(_) => (),
                            None => {
                                let vi = variable_info(level, new_var.clone(), idents);
                                let tys = optimizer.gen_type(&vi);
                                arg.aux.set_tys(tys);
                            }
                        }

                        let ret = new_g.subst(&new_var, &arg).update_ids();

                        let reduction_info =
                            ReductionInfo::new(level, arg.clone(), new_var, old_id);
                        Some((ret.clone(), reduction_info))
                    }
                    _ => None,
                }
            }
            match goal.kind() {
                GoalKind::App(predicate, arg) => {
                    // TODO: fvints & argints <- polymorphic_type config should be used to determine which to use
                    match generate_reduction_info(optimizer, level, predicate, arg, fvints) {
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
                    match go_(
                        optimizer,
                        predicate,
                        level,
                        fvints,
                        argints,
                        constraint.clone(),
                    ) {
                        Some((ret, mut reduction)) => {
                            // case reduced above like App(App(Abs, arg)) -> App(Abs, arg)
                            // [feature shared_ty]
                            // TODO: fvints & argints <- polymorphic_type config should be used to determine which to use
                            return match generate_reduction_info(
                                optimizer,
                                reduction.level() + 1,
                                &ret,
                                arg,
                                fvints,
                            ) {
                                Some((ret, reduction_info)) => {
                                    reduction.append_reduction(
                                        reduction_info,
                                        ret.clone(),
                                        goal.clone(),
                                    );
                                    Some((ret, reduction))
                                }
                                None => Some((
                                    G::mk_app_t(ret, arg.clone(), goal.aux.clone()),
                                    reduction,
                                )),
                            };
                        }
                        None => (),
                    };
                    go_(optimizer, arg, level, fvints, argints, constraint.clone()).map(
                        |(arg, pred)| (G::mk_app_t(predicate.clone(), arg, goal.aux.clone()), pred),
                    )
                }
                GoalKind::Conj(g1, g2) => {
                    go_(optimizer, g1, level, fvints, argints, constraint.clone())
                        .map(|(g1, p)| (G::mk_conj_t(g1, g2.clone(), goal.aux.clone()), p))
                        .or_else(|| {
                            go_(optimizer, g2, level, fvints, argints, constraint.clone())
                                .map(|(g2, p)| (G::mk_conj_t(g1.clone(), g2, goal.aux.clone()), p))
                        })
                }
                GoalKind::Disj(g1, g2) => {
                    let c1: Option<Constraint> = g1.clone().into();
                    match c1 {
                        Some(c1) => {
                            let constraint = Constraint::mk_conj(c1.negate().unwrap(), constraint);
                            go_(optimizer, g2, level, fvints, argints, constraint).map(|(g2, p)| {
                                (G::mk_disj_t(g1.clone(), g2.clone(), goal.aux.clone()), p)
                            })
                        }
                        None => {
                            let c2: Option<Constraint> = g2.clone().into();
                            match c2 {
                                Some(c2) => {
                                    let constraint =
                                        Constraint::mk_conj(c2.negate().unwrap(), constraint);
                                    go_(optimizer, g1, level, fvints, argints, constraint).map(
                                        |(g1, p)| {
                                            (
                                                G::mk_disj_t(
                                                    g1.clone(),
                                                    g2.clone(),
                                                    goal.aux.clone(),
                                                ),
                                                p,
                                            )
                                        },
                                    )
                                }
                                None => {
                                    panic!("fatal: g1 = {}, g2 = {}", g1, g2)
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
                    let r = go_(optimizer, g, level, fvints, argints, constraint)
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

                    let r = go_(optimizer, g, level, fvints, argints, constraint)
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
            optimizer,
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
    while let Some((g, r)) = go(optimizer, &reduced, &mut level) {
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
        config: InferenceConfig,
    ) -> Context {
        // default
        let infer_polymorphic_type = config.infer_polymorphic_type;
        Context {
            normal_form,
            track_idents,
            reduction_sequence,
            infer_polymorphic_type,
        }
    }
    fn retrieve_from_track_idents(&self, model: &chc::Model, derivation: &Derivation) -> TyEnv {
        let model = &model.model;
        let mut result_env = TypeEnvironment::new();
        for (pred_name, ids) in self.track_idents.iter() {
            for id in ids {
                match derivation.expr.get_opt(id) {
                    Some(tys) => {
                        for ty in tys.iter() {
                            debug!("{}({}): {}", pred_name, id, ty);
                            let ty = ty.ty.clone();
                            let ty = ty.assign(&model);
                            let pty = PolymorphicType::poly(ty);
                            result_env.add(*pred_name, pty);
                        }
                    }
                    None => (),
                }
            }
        }
        result_env
    }
    fn infer_type_inner(
        &self,
        derivation: &mut Derivation,
        reduction: &Reduction,
        clauses: &mut Vec<chc::CHC<chc::Atom, Constraint>>,
    ) {
        ///// aux functions
        fn append_clauses(clauses: &mut Vec<chc::CHC<chc::Atom, Constraint>>, constraint: &Atom) {
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
        }
        fn append_clauses_by_subst(
            clauses: &mut Vec<chc::CHC<chc::Atom, Constraint>>,
            ts: &Vec<Ty>,
            arg_ty: &Vec<Ty>,
            constraint: &Atom,
        ) {
            if ts.len() != 1 {
                unimplemented!()
            }
            let t = &ts[0];
            // arg_ty -> result -> <: ts -> t(arg_ty)
            // ts <: arg_ty
            for s in arg_ty.iter() {
                let constraint1 = Tau::check_subtype(&constraint.clone(), s, t);
                let constraint2 = Tau::check_subtype(&constraint.clone(), t, s);
                let constraint = Atom::mk_conj(constraint1, constraint2);
                append_clauses(clauses, &constraint);
            }
        }
        ///// aux functions end

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

        // retrieve argument types
        // if argument type is non-integer, then make sure that the context of the retrieved type matches
        // the current context formula.
        let mut arg_tys = Vec::new();
        for ri in reduction.args.iter().rev() {
            let arg_ty = if ri.arg_var.ty.is_int() {
                either::Left(ri.arg_var.id)
            } else {
                // 1. get the corresponding types
                let arg_ty = match &ri.arg.aux.tys {
                    Some(tys) => tys.clone(), // when shared type exists
                    None => derivation.get_arg(&ri.level).iter().cloned().collect(),
                };
                let arg_ty = if arg_ty.len() == 0 {
                    vec![Ty::mk_bot(&ri.arg_var.ty)]
                } else {
                    arg_ty
                };
                either::Right(arg_ty)
            };
            arg_tys.push(arg_ty);
        }

        // we have to track all the temporal ids
        // since there are more than one reductions in Reduction object itself
        let mut app_exprs = Vec::new();
        let mut p = reduction.app_expr.clone();
        loop {
            match p.kind() {
                GoalKind::App(g, _) => {
                    debug!("id={}, g={}", g.aux.id, g);
                    app_exprs.push(g.clone());
                    p = g.clone();
                }
                _ => break,
            }
        }
        assert_eq!(app_exprs.len(), arg_tys.len());

        for (ret_ty_idx, ret_ty) in ret_tys.iter().enumerate() {
            // if ret_ty_idx > 0, then we push calculated types to derivation without "already exists" check
            let SavedTy {
                ty: ret_ty,
                context_ty,
            } = ret_ty.clone();
            debug!("ret_ty: {}", ret_ty);
            debug!("context_ty: {}", context_ty);

            // if there is a shared_ty, we have to use it
            let (tmp_ret_ty, is_shared_ty) = match &reduction.predicate.aux.tys {
                Some(tys) => (tys[0].clone(), true),
                None => (
                    ret_ty.clone_with_rty_template(
                        Atom::mk_true(),
                        &mut if self.infer_polymorphic_type {
                            reduction.fvints.clone()
                        } else {
                            reduction.argints.clone()
                        },
                    ),
                    false,
                ),
            };

            let mut tmp_ty = tmp_ret_ty.clone();
            let mut body_ty = ret_ty.clone();
            let mut app_expr_ty = tmp_ret_ty.clone();

            // calculate the type for app_expr
            if is_shared_ty {
                for (arg_ty, reduction) in arg_tys.iter().rev().zip(reduction.args.iter()) {
                    match arg_ty {
                        // case: arg ty is integer
                        either::Left(ident) => {
                            body_ty = body_ty.deref_ptr(ident).rename(&ident, &reduction.old_id);
                            let op: Op = reduction.arg.clone().into();
                            match app_expr_ty.kind() {
                                TauKind::IArrow(id, t) => {
                                    body_ty = body_ty.rename(&reduction.old_id, id);
                                    app_expr_ty = t.subst(id, &op);
                                }
                                TauKind::Arrow(_, _) | TauKind::Proposition(_) => {
                                    panic!("program error")
                                }
                            }
                        }
                        // case: arg ty is higher-order
                        either::Right(arg_ty) => match app_expr_ty.kind() {
                            TauKind::Arrow(ts, t_result) => {
                                append_clauses_by_subst(
                                    clauses,
                                    ts,
                                    arg_ty,
                                    &app_expr_ty.rty_no_exists(),
                                );
                                app_expr_ty = t_result.clone()
                            }
                            TauKind::IArrow(_, _) | TauKind::Proposition(_) => {
                                panic!("program error")
                            }
                        },
                    }
                }
            } else {
                for (arg_ty, reduction) in arg_tys.iter().zip(reduction.args.iter().rev()) {
                    match arg_ty {
                        either::Left(ident) => {
                            body_ty = body_ty.deref_ptr(ident).rename(&ident, &reduction.old_id);
                            let op: Op = reduction.arg.clone().into();
                            tmp_ty = Tau::mk_iarrow(reduction.old_id, tmp_ty);
                            app_expr_ty = app_expr_ty.subst(&reduction.old_id, &op);
                        }
                        either::Right(arg_ty) => {
                            tmp_ty = Ty::mk_arrow(arg_ty.clone(), tmp_ty);
                        }
                    };
                }
            }
            // 3. generate constraint from subtyping t <: arg_ty -> ret_ty, and append them to constraints
            // constrain by `old <= new_tmpty <= top`

            debug!("inferred type: {}", tmp_ty);
            debug!("body type: {}", body_ty);
            debug!("app_expr_type: {}", app_expr_ty);

            let constraint =
                Atom::mk_implies_opt(tmp_ty.rty_no_exists(), body_ty.rty_no_exists()).unwrap();

            let constraint2 =
                Atom::mk_implies_opt(context_ty.rty_no_exists(), app_expr_ty.rty_no_exists())
                    .unwrap();
            debug!("constraint1: {}", constraint);
            debug!("constraint2: {}", constraint2);
            let constraint = Atom::mk_conj(constraint, constraint2);
            append_clauses(clauses, &constraint);

            // 4. for each `level` in reduction.candidate.aux, we add t to Derivation
            for level in reduction.predicate.aux.level_arg.iter() {
                derivation.arg.insert(*level, tmp_ty.clone());
            }
            for level in reduction.app_expr.aux.level_arg.iter() {
                derivation.arg.insert(*level, app_expr_ty.clone())
            }

            debug!(
                "app_expr({}): {}",
                reduction.app_expr.aux.id, reduction.app_expr
            );

            // finally, add types to all the temporal app result
            let mut temporal_ty = tmp_ty.clone();
            for ((arg_ty, reduction), expr) in arg_tys
                .iter()
                .rev()
                .zip(reduction.args.iter())
                .zip(app_exprs.iter().rev())
            {
                debug!("saving({}): {}", expr.aux.id, temporal_ty);
                // [feature shared_ty] in the infer_type phase, we no longer have to track both shared_ty and ty.
                let temporal_saved_ty = SavedTy::mk(temporal_ty.clone(), context_ty.clone());
                derivation.memorize_type_judgement(expr, temporal_saved_ty, ret_ty_idx > 0);
                match arg_ty {
                    either::Left(_) => {
                        let op: Op = reduction.arg.clone().into();
                        let (id, t) = match temporal_ty.kind() {
                            TauKind::IArrow(id, t) => (id, t),
                            _ => panic!("fatal"),
                        };
                        temporal_ty = t.subst(id, &op);
                    }
                    either::Right(_) => {
                        temporal_ty = match temporal_ty.kind() {
                            TauKind::Arrow(_, t) => t.clone(),
                            _ => panic!("fatal"),
                        }
                    }
                };
            }

            // [feature shared_ty] in the infer_type phase, we no longer have to track both shared_ty and ty.
            let app_expr_saved_ty = SavedTy::mk(app_expr_ty.clone(), context_ty.clone());
            derivation.memorize_type_judgement(
                &reduction.app_expr,
                app_expr_saved_ty,
                ret_ty_idx > 0,
            );
            // the aux.id is saved above, so we don't have to for app_expr
            debug!("");
        }
    }
    fn infer_type(
        &mut self,
        mut derivation: Derivation,
        constraints: Stack<Atom>, // constraints generated during type checking due to type sharing
    ) -> Option<TyEnv> {
        let mut clauses = Vec::new();
        debug!("constraints generated during type checking");
        for constraint in constraints.iter() {
            debug!("constraints: {constraint}");
            match constraint.to_chcs_or_pcsps() {
                either::Left(chcs) => {
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
        }

        for reduction in self.reduction_sequence.iter().rev() {
            self.infer_type_inner(&mut derivation, reduction, &mut clauses)
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
        debug!("{}", m);
        let config = solver::interpolation::InterpolationConfig::new().use_chc_if_requied();
        let model = solver::interpolation::solve(&clauses, &config);
        debug!("interpolated:");
        debug!("{}", model);

        // ** check if the returned model is "tractable" **
        // Here, tracktable means no constraint in model does not contain existential quantifier.
        //
        // If the shared predicate is enabled, the resulting constraints are no longer acyclic-CHCs,
        // but CHCs (can contain recursive predicates).
        // Due to the background CHC solvers, in some cases, solutions can contain existential quantifers.
        // I know that hoice can return such a solution when the the given problem is so easy that its preprocessor
        // can solve it, and that there is an option to avoid such situations (simplify-clauses: false).
        // However, it seems totally an experimental feature, and at least currently, it is not functional.
        // Therefore, if we find that the solution in model contains some existential quanfiers,
        // we just return None even though it actually exists.
        if model.is_solution_tractable() {
            // collect needed predicate
            // 5. from the model, generate a type environment
            Some(self.retrieve_from_track_idents(&model, &derivation))
        } else {
            warn!("solution from CHC is untractable");
            None
        }
    }
}

fn handle_abs(
    config: &TCConfig,
    tenv: &mut Env,
    ienv: &mut HashSet<Ident>,
    all_coefficients: &mut HashSet<Ident>,
    arg_expr: &G,
    t: &Ty,
) -> PossibleDerivation<Atom> {
    fn handle_abs_inner(
        config: &TCConfig,
        tenv: &mut Env,
        ienv: &mut HashSet<Ident>,
        all_coefficients: &mut HashSet<Ident>,
        arg_expr: &G,
        t: &Ty,
    ) -> PossibleDerivation<Atom> {
        let mut pt = match arg_expr.kind() {
            GoalKind::Abs(v, g) if v.ty.is_int() => match t.kind() {
                TauKind::IArrow(id, t) if v.ty.is_int() => {
                    let t = t.rename(id, &v.id);
                    let b = ienv.insert(v.id);
                    let pt = handle_abs_inner(config, tenv, ienv, all_coefficients, g, &t);
                    if !b {
                        ienv.remove(&v.id);
                    }
                    pt.iarrow(&v.id)
                }
                _ => panic!("program error"),
            },
            GoalKind::Abs(v, g) => match t.kind() {
                TauKind::Arrow(ts, t) if !v.ty.is_int() => {
                    let mut tenv = tenv.clone();
                    for t in ts {
                        debug!("adding type {t} to tenv");
                        tenv.add(v.id, PolymorphicType::mono(t.clone()));
                    }
                    let pt = handle_abs_inner(config, &mut tenv, ienv, all_coefficients, g, t);
                    pt.arrow(ts)
                }
                _ => panic!("fatal"),
            },
            _ => {
                let mut pt =
                    type_check_inner(config, tenv, ienv, all_coefficients, arg_expr, t.clone());
                pt.coarse_type(t);
                // skip the continuation of this inner function
                return pt;
            }
        };
        save_derivation(&mut pt, arg_expr, &t);
        debug!("handle_abs: |- {} : {} ", arg_expr, pt);
        pt
    }
    // [feature shared_ty]
    match (&config.tc_mode, &arg_expr.aux.tys) {
        (TCFlag::Normal, _) | (_, None) => {
            handle_abs_inner(config, tenv, ienv, all_coefficients, arg_expr, t)
        }
        (TCFlag::Shared(_), Some(tys)) if tys.len() == 1 => {
            let mut pt = handle_abs_inner(config, tenv, ienv, all_coefficients, arg_expr, &tys[0]);
            pt.coarse_type(t);
            pt
        }
        (_, _) => panic!("program error"),
    }
}

#[derive(Clone, Debug)]
struct TCConfig {
    tc_mode: TCFlag,
    // TODO
    construct_derivation: bool,
}

#[derive(Clone, Debug)]
struct InstantiationConfig {
    derivation: Derivation,
}

#[derive(Clone, Debug)]
enum TCFlag {
    Normal,
    Shared(InstantiationConfig),
}

fn coarse_expr_for_type_sharing(config: &TCConfig, pt: &mut PossibleDerivation<Atom>, expr: &G) {
    // [feature shared_ty] template type sharing
    // if there is a shared type registered, coarse pt to obey the type.
    match (&config.tc_mode, &expr.aux.tys) {
        (TCFlag::Shared(_), Some(tys)) if tys.len() == 1 => pt.coarse_type(&tys[0]),
        (TCFlag::Normal, _) | (_, None) => (),
        (_, _) => unimplemented!(),
    }
}

fn save_derivation(pt: &mut PossibleDerivation<Atom>, expr: &G, context_ty: &Ty) {
    for level in expr.aux.level_arg.iter() {
        for ct in pt.types.iter_mut() {
            ct.memorize(*level);
        }
    }
    for ct in pt.types.iter_mut() {
        ct.set_types(expr, context_ty.clone());
    }
}

// tenv+ienv; constraint |- App(arg, ret): t
/// returns possible types for app_expr under constraint
fn handle_app(
    config: &TCConfig,
    tenv: &mut Env,
    ienv: &mut HashSet<Ident>,
    all_coefficients: &mut HashSet<Ident>,
    app_expr: &G,
    cty: Ty,
) -> PossibleDerivation<Atom> {
    fn handle_inner(
        config: &TCConfig,
        tenv: &mut Env,
        ienv: &mut HashSet<Ident>,
        all_coefficients: &mut HashSet<Ident>,
        pred: &G,
        cty: Ty, // context ty
    ) -> PossibleDerivation<Atom> {
        match pred.kind() {
            formula::hes::GoalKind::Var(x) => match tenv.get(x) {
                Some(ts) => {
                    // [feature shared_ty] if shared type mode is enabled, instantiate the polymorphic types
                    // in the same way as the previous instantiation that succeeded.
                    let types = match &config.tc_mode {
                        TCFlag::Normal => {
                            debug!("search {x} from tenv");
                            let mut coefficients = Stack::new();
                            let types = ts
                                .iter()
                                .map(|t| {
                                    let t =
                                        t.instantiate(ienv, &mut coefficients, all_coefficients);
                                    debug!("instantiate_type ienv: {:?}", ienv);
                                    debug!("instantiated: {t}");

                                    CandidateDerivation::new(
                                        t,
                                        coefficients.clone(),
                                        Stack::new(),
                                        Derivation::new(),
                                    )
                                })
                                .collect();
                            types
                        }
                        TCFlag::Shared(d) => {
                            let ct = d
                                .derivation
                                .get_expr_ty(&pred.aux.id)
                                .iter()
                                .cloned()
                                .map(|t| {
                                    CandidateDerivation::new(
                                        t.ty,
                                        Stack::new(),
                                        Stack::new(),
                                        Derivation::new(),
                                    )
                                })
                                .next()
                                .unwrap();
                            vec![ct]
                        }
                    };
                    PossibleDerivation::new(types)
                }
                None => PossibleDerivation::empty(),
            },
            formula::hes::GoalKind::App(predg, argg) => {
                let pred_pt = handle_app(config, tenv, ienv, all_coefficients, predg, cty.clone());
                // Case: the argument is integer
                match argg.check_int_expr(ienv) {
                    // Case: the type of argument is int
                    Some(op) => {
                        let types = pred_pt
                            .types
                            .into_iter()
                            .map(|t| match t.ty.kind() {
                                TauKind::IArrow(x, t2) => CandidateDerivation::new(
                                    t2.subst(x, &op),
                                    t.coefficients.clone(),
                                    t.constraints.clone(),
                                    t.derivation.clone(),
                                ),
                                _ => panic!("fatal"),
                            })
                            .collect();
                        return PossibleDerivation::new(types); // early return
                    }
                    // Otherwise, we continue.
                    None => (),
                };

                // Case: the argument is not integer
                let mut result_cts = Vec::new();
                // we calculate the argument's type. we have to enumerate all the possible type of pt1.
                for ty in pred_pt.types {
                    let (arg_t, result_t) = match ty.ty.kind() {
                        TauKind::Arrow(arg, result) => (arg, result),
                        TauKind::Proposition(_) | TauKind::IArrow(_, _) => panic!("fatal"),
                    };
                    let result_ct = CandidateDerivation::new(
                        result_t.clone(),
                        ty.coefficients.clone(),
                        ty.constraints.clone(),
                        ty.derivation.clone(),
                    );
                    let mut tmp_cts = vec![result_ct];
                    // check if there exists a derivation for all types in the intersection type.
                    for t in arg_t {
                        // check if arg_constraint |- argg: arg_t
                        let rty = cty.rty_no_exists();
                        let t_context = t.conjoin_constraint(&rty);
                        let pt = handle_abs(config, tenv, ienv, all_coefficients, argg, &t_context);

                        // permutation
                        let mut new_tmp_cts = Vec::new();
                        for ty2 in pt.types {
                            // merge
                            for tmp_ct in tmp_cts.iter() {
                                new_tmp_cts.push(CandidateDerivation::merge(&tmp_ct, &ty2));
                            }
                        }
                        tmp_cts = new_tmp_cts;
                    }
                    // Now that all the argument for `pred_pt` can be derived, we have candidatetype `result_t`
                    // with the derivations of `ct`s
                    result_cts.append(&mut tmp_cts);
                }
                PossibleDerivation::new(result_cts)
            }
            formula::hes::GoalKind::Constr(_)
            | formula::hes::GoalKind::Op(_)
            | formula::hes::GoalKind::Abs(_, _)
            | formula::hes::GoalKind::Conj(_, _)
            | formula::hes::GoalKind::Disj(_, _)
            | formula::hes::GoalKind::Univ(_, _) => panic!("fatal: {}", pred),
        }
    }
    let mut pt = handle_inner(config, tenv, ienv, all_coefficients, app_expr, cty.clone());

    coarse_expr_for_type_sharing(config, &mut pt, &app_expr);
    save_derivation(&mut pt, app_expr, &cty);

    debug!("handle_app: |- {} : {} ", app_expr, pt);
    pt
}

// body of type checking;  tenv; ienv |- c : contex_ty
// do some check in bottom up manner
fn type_check_inner(
    config: &TCConfig,
    tenv: &mut Env,
    ienv: &mut HashSet<Ident>, // V
    all_coefficients: &mut HashSet<Ident>,
    c: &G,
    context_ty: Ty,
) -> PossibleDerivation<Atom> {
    // the second element of the returned value is whether the expr was app.
    // since app is delegated to `handle_app`, after go_inner, you don't have to register the result
    // to the derivation tree again.
    fn go_inner(
        config: &TCConfig,
        tenv: &mut Env,
        ienv: &mut HashSet<Ident>,
        all_coefficients: &mut HashSet<Ident>,
        c: &G,
        context_ty: Ty,
    ) -> (PossibleDerivation<Atom>, bool) {
        // [pruning]: since we can always derive ψ: ⊥, we do not have to care about this part
        if !config.construct_derivation && context_ty.is_bot() {
            let cd = CandidateDerivation::singleton(context_ty.clone());
            return (PossibleDerivation::singleton(cd), false);
        }
        // for App, we delegate the procedure to `handle_app`
        // and in that procedure, it saves the types
        let mut already_registered = false;
        let result_pt = match c.kind() {
            formula::hes::GoalKind::Constr(c) => {
                let constraint = c.clone().into();
                let t = Ty::mk_prop_ty(constraint);
                let cd = CandidateDerivation::singleton(t);
                PossibleDerivation::singleton(cd)
            }
            formula::hes::GoalKind::Var(x) => match tenv.get(x) {
                Some(ts) => {
                    // [feature shared_ty] if shared type mode is enabled, instantiate the polymorphic types
                    // in the same way as the previous instantiation that succeeded.
                    let tys = match &config.tc_mode {
                        TCFlag::Normal => {
                            let mut tys = Vec::new();
                            for ty in ts {
                                let mut coefficients = Stack::new();
                                let ty = ty.instantiate(ienv, &mut coefficients, all_coefficients);
                                debug!("instantiate_type ienv: {:?}", ienv);
                                debug!("instantiated: {ty}");

                                let cd = CandidateDerivation::new(
                                    ty,
                                    coefficients,
                                    Stack::new(),
                                    Derivation::new(),
                                );
                                tys.push(cd);
                            }
                            tys
                        }
                        TCFlag::Shared(d) => {
                            let ty = d
                                .derivation
                                .get_expr_ty(&c.aux.id)
                                .iter()
                                .cloned()
                                .map(|t| {
                                    CandidateDerivation::new(
                                        t.ty,
                                        Stack::new(),
                                        Stack::new(),
                                        Derivation::new(),
                                    )
                                })
                                .next()
                                .unwrap();
                            vec![ty]
                        }
                    };
                    PossibleDerivation::new(tys)
                }
                None => PossibleDerivation::empty(),
            },
            formula::hes::GoalKind::Conj(g1, g2) => {
                let t1 =
                    type_check_inner(config, tenv, ienv, all_coefficients, g1, context_ty.clone());
                let t2 =
                    type_check_inner(config, tenv, ienv, all_coefficients, g2, context_ty.clone());
                PossibleDerivation::conjoin(t1, t2)
            }
            formula::hes::GoalKind::Disj(g1, g2) => {
                let c1: Option<Constraint> = g1.clone().into();
                let (c, g, g_) = match c1 {
                    Some(c) => (c, g2, g1),
                    None => (g2.clone().into(), g1, g2),
                };
                let c_neg = c.negate().unwrap();
                let t1 = type_check_inner(
                    config,
                    tenv,
                    ienv,
                    all_coefficients,
                    g,
                    context_ty.conjoin_constraint(&c_neg.into()),
                );
                // type check of constraints (to track the type derivation, checking g2 is necessary)
                let t2 = type_check_inner(
                    config,
                    tenv,
                    ienv,
                    all_coefficients,
                    g_,
                    context_ty.conjoin_constraint(&c.into()),
                );
                PossibleDerivation::disjoin(t1, t2)
            }
            formula::hes::GoalKind::Univ(x, g) => {
                let b = ienv.insert(x.id);
                let mut pt =
                    type_check_inner(config, tenv, ienv, all_coefficients, &g, context_ty.clone());
                if b {
                    ienv.remove(&x.id);
                }
                // quantify all the constraint.
                pt.quantify(&x.id);
                pt
            }
            formula::hes::GoalKind::App(_, _) => {
                already_registered = true;
                handle_app(config, tenv, ienv, all_coefficients, c, context_ty.clone())
            }
            formula::hes::GoalKind::Abs(_v, _g) => {
                panic!("fatal error")
            }
            // op is always handled by App(x, op)
            formula::hes::GoalKind::Op(_) => panic!("fatal error"),
        };
        (result_pt, already_registered)
    }
    let (mut pt, already_registered) =
        go_inner(config, tenv, ienv, all_coefficients, c, context_ty.clone());

    if !already_registered {
        coarse_expr_for_type_sharing(config, &mut pt, &c);
        save_derivation(&mut pt, c, &context_ty);
    }

    crate::pdebug!("type_check_go(", c.aux.id, ") |- ", c, " : ", pt ; bold);
    pt
}

// we assume conjunction normal form and has the form (θ => a₁ a₂ ⋯) ∧ ⋯
/// V; Γ ⊢ c : t
/// function go constructs possible derivation trees by induction on the structure of c(ψ)
///
fn type_check(
    tenv: &mut Env,
    ienv: &mut HashSet<Ident>, // V
    c: &G,
    t: &PTy,
) -> bool {
    for fv in t.vars.iter() {
        ienv.insert(*fv);
        debug!("type_check ienv: {ienv:?}");
    }
    let mut all_coefficients = HashSet::new();
    let config = TCConfig {
        tc_mode: TCFlag::Normal,
        construct_derivation: false,
    };
    let pt = handle_abs(&config, tenv, ienv, &mut all_coefficients, c, &t.ty);
    //pt.coarse_type(constraint, t);
    pt.check_derivation().is_some()
}

/// ε; true ; Γ ⊢ ψ : •<T>
///
/// tenv: Γ
/// candidate: ψ
/// assumption: candidate has a beta-normal form of type *.
fn type_check_top_with_derivation(psi: &G, tenv: &mut Env) -> Option<Derivation> {
    title!("type_check_top");
    debug!("tenv: {}", tenv);
    debug!("target: {}", psi);
    let mut ienv = HashSet::new();
    let mut all_coefficients = HashSet::new();
    let config = TCConfig {
        tc_mode: TCFlag::Normal,
        construct_derivation: true,
    };
    let mut pt = type_check_inner(
        &config,
        tenv,
        &mut ienv,
        &mut all_coefficients,
        &psi,
        Ty::mk_prop_ty(Atom::mk_true()),
    );
    pt.coarse_type(&Ty::mk_prop_ty(Atom::mk_true()));

    // check if there is an actually possible derivation
    pt.check_derivation()
}

/// ε; true ; Γ ⊢ ψ : •<T>
///
/// tenv: Γ
/// candidate: ψ
/// assumption: candidate has a beta-normal form of type *.
fn type_check_top_with_derivation_and_constraints(
    previous_derivation: Derivation,
    psi: &G,
    tenv: &mut Env,
) -> (Derivation, Stack<Atom>) {
    title!("type_check_top_with_derivation_and_constraints");
    // debug
    let ts = previous_derivation.expr.get(&psi.aux.id);
    for t in ts.iter() {
        debug!("saved top: {t}");
    }
    // using previous derivation,
    // constraints that are required for shared types can be generated.
    let mut ienv = HashSet::new();
    let mut all_coefficients = HashSet::new();
    let ic = InstantiationConfig {
        derivation: previous_derivation,
    };
    let config = TCConfig {
        tc_mode: TCFlag::Shared(ic),
        construct_derivation: true,
    };
    let mut pt = type_check_inner(
        &config,
        tenv,
        &mut ienv,
        &mut all_coefficients,
        &psi,
        Ty::mk_prop_ty(Atom::mk_true()),
    );
    pt.coarse_type(&Ty::mk_prop_ty(Atom::mk_true()));

    // check if there is an actually possible derivation
    // since the derivation has the same shape as `previous_derivation`,
    // we do not have more than one derivation in pt.
    assert!(pt.types.len() == 1);
    let derivation = pt.types[0].derivation.clone();

    let constraints = pt.types[0].constraints.clone();
    (derivation, constraints)
}

/// Γ ⊢ ψ : •<T>
///
/// tenv: Γ
/// candidate: ψ
/// assumption: candidate has a beta-normal form of type *.
pub fn type_check_top(candidate: &Candidate, tenv: &TyEnv) -> bool {
    let g = candidate.clone().into();
    let mut tenv = tenv.into();
    let b = type_check_top_with_derivation(&g, &mut tenv).is_some();
    b
}

fn reduce_until_normal_form(
    candidate: &Candidate,
    problem: &Problem,
    config: InferenceConfig,
    optimizer: &mut dyn Optimizer,
) -> Context {
    let mut track_idents = HashMap::new();
    let candidate = candidate.clone().into(); // assign `aux` to candidate.
    let goal = subst_predicate(&candidate, problem, &mut track_idents);
    let goal = goal.alpha_renaming();
    title!("generate_reduction_sequence");
    let (reduction_sequence, normal_form) = generate_reduction_sequence(&goal, optimizer);
    Context::new(normal_form, track_idents, reduction_sequence, config)
}

#[derive(Clone, Debug)]
struct SavedTy {
    ty: Ty,
    context_ty: Ty, // to be coarsed
}

impl fmt::Display for SavedTy {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.ty)
    }
}
impl formula::Subst for SavedTy {
    type Item = Op;
    type Id = Ident;

    fn subst(&self, x: &Self::Id, v: &Self::Item) -> Self {
        let ty = self.ty.subst(x, v);
        let context_ty = self.context_ty.subst(x, v);
        SavedTy::mk(ty, context_ty)
    }
}

impl SavedTy {
    fn mk(ty: Ty, context_ty: Ty) -> SavedTy {
        SavedTy { ty, context_ty }
    }
}

impl Rename for SavedTy {
    fn rename(&self, x: &Ident, y: &Ident) -> Self {
        let ty = self.ty.rename(x, y);
        let context_ty = self.context_ty.rename(x, y);
        SavedTy::mk(ty, context_ty)
    }
}

#[derive(Clone, Debug)]
struct DerivationMap<ID: Eq + std::hash::Hash + Copy, T>(HashTrieMap<ID, Stack<T>>);

impl<ID: Eq + std::hash::Hash + Copy + fmt::Display, T: Clone + fmt::Display> fmt::Display
    for DerivationMap<ID, T>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for (k, stack) in self.0.iter() {
            write!(f, "{}: ", k)?;
            let mut first = true;
            for t in stack.iter() {
                if first {
                    first = false;
                    write!(f, "{}", t)?;
                } else {
                    write!(f, ", {}", t)?;
                }
            }
            writeln!(f, "")?;
        }
        Ok(())
    }
}
impl<ID: Eq + std::hash::Hash + Copy, T: Clone + Subst<Item = Op, Id = Ident>>
    DerivationMap<ID, T>
{
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
    fn push(&mut self, ident: ID, ty: T) {
        let tys = match self.0.get(&ident) {
            Some(tys) => tys.push(ty),
            None => Stack::new().push(ty),
        };
        self.0 = self.0.insert(ident, tys);
    }
    fn get(&self, level: &ID) -> Stack<T> {
        self.0.get(level).cloned().unwrap_or(Stack::new())
    }
    fn get_opt(&self, level: &ID) -> Option<Stack<T>> {
        self.0.get(level).cloned()
    }
    fn update_with_model(&mut self, m: &solver::Model) {
        let mut new_map = HashTrieMap::new();
        for (k, tys) in self.0.iter() {
            let mut new_tys = Stack::new();
            for ty in tys.iter() {
                let mut ty = ty.clone();
                for (var, val) in m.model.iter() {
                    ty = ty.subst(var, &Op::mk_const(*val));
                }
                new_tys.push_mut(ty);
            }
            new_map.insert_mut(*k, new_tys);
        }
        *self = DerivationMap(new_map)
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
    fn memorize_type_judgement(&mut self, expr: &G, ty: SavedTy, allow_duplicate: bool) {
        if let Some(t) = self.get_expr_ty(&expr.aux.id).iter().next() {
            if !allow_duplicate {
                panic!("already registered!: {}: {}", expr, t);
            } else {
            }
        }
        for id in expr.aux.old_ids.iter() {
            self.expr.push(*id, ty.clone())
        }
        self.expr.push(expr.aux.id, ty);
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
    fn update_with_model(&mut self, m: &solver::Model) {
        self.arg.update_with_model(&m);
        self.expr.update_with_model(&m);
    }
}

#[derive(Clone, Debug)]
struct CandidateDerivation<C> {
    ty: Ty,
    coefficients: Stack<Ident>,
    constraints: Stack<C>,
    // level -> type map appeared in the derivation of ty so far.
    derivation: Derivation,
}

// inner purpose
enum Method {
    Conj,
    Disj,
}
impl<C: Refinement> CandidateDerivation<C> {
    fn new(
        ty: Ty,
        coefficients: Stack<Ident>,
        constraints: Stack<C>,
        derivation: Derivation,
    ) -> CandidateDerivation<C> {
        CandidateDerivation {
            ty,
            coefficients,
            constraints,
            derivation,
        }
    }
    fn singleton(ty: Ty) -> Self {
        Self::new(ty, Stack::new(), Stack::new(), Derivation::new())
    }
    fn memorize(&mut self, level: usize) {
        self.derivation.memorize(level, self.ty.clone())
    }
    fn set_types(&mut self, expr: &G, context_ty: Ty) {
        let ty = self.ty.clone();
        let saved_ty = SavedTy::mk(ty, context_ty);
        self.derivation
            .memorize_type_judgement(expr, saved_ty, false);
    }
    fn merge_derivation(&mut self, derivation: &Derivation) {
        self.derivation.merge(derivation);
    }
    fn merge_coefficients(&mut self, coefficients: &Stack<Ident>) {
        for c in coefficients.iter() {
            self.coefficients.push_mut(*c);
        }
    }
    fn merge_constraints(&mut self, constraints: &Stack<C>) {
        for c in constraints.iter() {
            self.constraints.push_mut(c.clone());
        }
    }
    fn merge_inner(&mut self, c: &CandidateDerivation<C>, method: Method) {
        self.ty = match (self.ty.kind(), c.ty.kind()) {
            (TauKind::Proposition(c1), TauKind::Proposition(c2)) => match method {
                Method::Conj => Ty::mk_prop_ty(Atom::mk_conj(c1.clone(), c2.clone())),
                Method::Disj => Ty::mk_prop_ty(Atom::mk_disj(c1.clone(), c2.clone())),
            },
            (_, _) => panic!("fatal: self.ty={} and c.ty={}", self.ty, c.ty),
        };
        self.merge_derivation(&c.derivation);
        self.merge_coefficients(&c.coefficients);
        self.merge_constraints(&c.constraints);
    }
    // only for bool type
    fn conjoin(c1: &Self, c2: &Self) -> Self {
        let mut c1 = c1.clone();
        c1.merge_inner(c2, Method::Conj);
        c1
    }
    fn disjoin(c1: &Self, c2: &Self) -> Self {
        let mut c1 = c1.clone();
        c1.merge_inner(c2, Method::Disj);
        c1
    }
    fn merge(c1: &Self, c2: &Self) -> Self {
        let mut c1 = c1.clone();
        c1.merge_derivation(&c2.derivation);
        c1.merge_coefficients(&c2.coefficients);
        c1.merge_constraints(&c2.constraints);
        c1
    }
    fn quantify(&mut self, x: Ident) {
        let ty = match self.ty.kind() {
            TauKind::Proposition(c1) => Ty::mk_prop_ty(Atom::mk_quantifier_int(
                crate::formula::QuantifierKind::Universal,
                x,
                c1.clone(),
            )),
            TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => panic!("fatal"),
        };
        self.ty = ty;
    }
    fn iarrow(mut self, x: &Ident) -> Self {
        let ty = self.ty.clone();
        self.ty = Ty::mk_iarrow(*x, ty);

        self
    }
    fn arrow(mut self, ts: &Vec<Ty>) -> Self {
        let ty = self.ty.clone();
        self.ty = Ty::mk_arrow(ts.clone(), ty);

        self
    }
}
impl CandidateDerivation<Atom> {
    // generate constraints from the subsumption rules
    fn coarse_type(&mut self, t: &Ty) {
        let s = self.ty.clone();
        debug!("coarse_type: |- {s} <: {t}");
        let constraint_ty = Ty::check_subtype(&Atom::mk_true(), &s, t);
        debug!("constraint: {constraint_ty}");
        self.constraints.push_mut(constraint_ty);
        self.ty = t.clone();
    }
}

impl<C: Refinement> fmt::Display for CandidateDerivation<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.ty)
    }
}

impl<C: Refinement> Pretty for CandidateDerivation<C> {
    fn pretty<'b, D, A>(
        &'b self,
        al: &'b D,
        config: &mut crate::util::printer::Config,
    ) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        self.ty.pretty(al, config)
    }
}

/// Since type environment can contain multiple candidate types,
/// we make sure that which one is suitable by considering them parallely.
#[derive(Debug)]
struct PossibleDerivation<C: Refinement> {
    types: Vec<CandidateDerivation<C>>,
}
impl<C: Refinement> fmt::Display for PossibleDerivation<C> {
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

impl<C: Refinement> Pretty for PossibleDerivation<C> {
    fn pretty<'b, D, A>(
        &'b self,
        al: &'b D,
        config: &mut crate::util::printer::Config,
    ) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        let docs = self.types.iter().map(|t| t.pretty(al, config));
        al.intersperse(docs, al.line().append(al.text("/\\ ")))
            .hang(2)
            .group()
    }
}

impl<C: Refinement> PossibleDerivation<C> {
    fn new(types: Vec<CandidateDerivation<C>>) -> Self {
        PossibleDerivation { types }
    }

    fn empty() -> Self {
        PossibleDerivation::new(Vec::new())
    }

    fn singleton(cd: CandidateDerivation<C>) -> Self {
        Self::new(vec![cd])
    }

    fn conjoin(pt1: Self, pt2: Self) -> Self {
        let mut ts = Vec::new();
        for pt1 in pt1.types.iter() {
            for pt2 in pt2.types.iter() {
                let pt1 = CandidateDerivation::conjoin(pt1, pt2);
                ts.push(pt1);
            }
        }
        PossibleDerivation::new(ts)
    }
    fn disjoin(pt1: Self, pt2: Self) -> Self {
        let mut ts = Vec::new();
        for pt1 in pt1.types.iter() {
            for pt2 in pt2.types.iter() {
                let pt1 = CandidateDerivation::disjoin(pt1, pt2);
                ts.push(pt1);
            }
        }
        PossibleDerivation::new(ts)
    }
    fn quantify(&mut self, x: &Ident) {
        for pt1 in self.types.iter_mut() {
            pt1.quantify(*x);
        }
    }
    fn iarrow(self, x: &Ident) -> PossibleDerivation<C> {
        let types = self.types.into_iter().map(|ct| ct.iarrow(x)).collect();
        PossibleDerivation { types }
    }
    fn arrow(self, ts: &Vec<Ty>) -> PossibleDerivation<C> {
        let types = self.types.into_iter().map(|ct| ct.arrow(ts)).collect();
        PossibleDerivation { types }
    }
}
impl PossibleDerivation<Atom> {
    fn coarse_type(&mut self, t: &Ty) {
        for ct in self.types.iter_mut() {
            ct.coarse_type(t);
        }
    }
    /// check if there is a valid derivation by solving constraints generated
    /// on subsumptions, and returns one if exists.
    fn check_derivation(&self) -> Option<Derivation> {
        for ct in self.types.iter() {
            let mut constraint = Constraint::mk_true();
            for c in ct.constraints.iter() {
                constraint = Constraint::mk_conj(constraint, c.clone().into());
            }
            debug!("check_derivation constraint: {constraint}");
            let fvs = constraint.fv();
            let exists: HashSet<Ident> = ct.coefficients.iter().cloned().collect();
            let vars = fvs.difference(&exists).cloned().collect();
            #[cfg(debug)]
            {
                debug!("variables used for coefficients of linear templates");
                let s = exists
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join(",");
                debug!("exists: {s}");
            }

            let mut solver = solver::smt::smt_solver(solver::SMTSolverType::Auto);
            let m = solver.solve_with_model(&constraint, &vars, &exists);
            match m {
                Ok(m) => {
                    debug!("constraint was sat: {}", constraint);
                    debug!("model is {}", m);
                    // replace all the integer coefficient
                    let mut derivation = ct.derivation.clone();
                    derivation.update_with_model(&m);

                    return Some(derivation);
                }
                Err(_) => (),
            }
        }
        None
    }
}

#[derive(Clone, Copy)]
pub struct InferenceConfig {
    pub infer_polymorphic_type: bool,
}
impl InferenceConfig {
    pub fn new() -> InferenceConfig {
        InferenceConfig {
            infer_polymorphic_type: true,
        }
    }
    pub fn infer_polymorphic_type(mut self, infer_polymorphic_type: bool) -> InferenceConfig {
        self.infer_polymorphic_type = infer_polymorphic_type;
        self
    }
}

pub fn search_for_type(
    candidate: &Candidate,
    problem: &Problem,
    tenv: &mut Env,
    config: InferenceConfig,
) -> Option<TyEnv> {
    crate::title!("search_for_type");
    debug!("{}", candidate);
    let infer_polymorphic_type = config.infer_polymorphic_type;
    // TODO: expand candidate once based on problem.
    let mut optimizer = optimizer::NaiveOptimizer::new();
    while optimizer.continuable() {
        let mut ctx = reduce_until_normal_form(candidate, problem, config, &mut optimizer);
        debug!("{}", ctx.normal_form);
        //let candidate = ctx.normal_form.clone();
        let derivation = type_check_top_with_derivation(&ctx.normal_form, tenv)?;
        let (derivation, constraints) =
            type_check_top_with_derivation_and_constraints(derivation, &ctx.normal_form, tenv);
        match ctx.infer_type(derivation, constraints) {
            Some(x) => {
                optimizer.report_inference_result(InferenceResult::new(true));
                return Some(x);
            }
            None => (),
        }
        optimizer.report_inference_result(InferenceResult::new(false));
    }
    if infer_polymorphic_type {
        // must succeed in theory
        panic!("program error: constructing derivation failed")
    } else {
        None
    }
}

// Γ ⊢ Γ
pub fn check_inductive(env: &TyEnv, problem: &Problem) -> bool {
    let tenv: Env = env.into();
    for (id, ts) in env.map.iter() {
        let clause = problem.get_clause(id).unwrap();
        let mut env = tenv.clone();
        for t in ts.iter() {
            let t = t.clone().into();
            if !type_check(
                &mut env,
                &mut HashSet::new(),
                &clause.body.clone().into(),
                &t,
            ) {
                return false;
            }
        }
    }
    true
}

pub fn saturate(env: &TyEnv, problem: &Problem) -> TyEnv {
    let mut current_env = env.clone();
    loop {
        let mut new_env = TypeEnvironment::new();
        let mut saturated = true;
        for (id, ts) in current_env.map.iter() {
            let clause = problem.get_clause(id).unwrap();
            for t in ts.iter() {
                let mut env: Env = (&current_env).into();
                if type_check(
                    &mut env,
                    &mut HashSet::new(),
                    &clause.body.clone().into(),
                    &t.clone().into(),
                ) {
                    new_env.add(*id, t.clone());
                } else {
                    saturated = false;
                }
            }
        }
        current_env = new_env;
        if saturated {
            return current_env;
        }
    }
}
