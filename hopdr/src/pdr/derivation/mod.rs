mod derive_tree;
mod tree;

use self::derive_tree::DeriveNode;

use super::optimizer;
use super::optimizer::{variable_info, InferenceResult, Optimizer};
use super::rtype::{PolymorphicType, Refinement, TBot, Tau, TauKind, TyEnv, TypeEnvironment};
use derive_tree::Derivation;

use crate::formula::hes::{Goal, GoalBase, GoalKind, Problem as ProblemBase};
use crate::formula::{self, DerefPtr, FirstOrderLogic};
use crate::formula::{
    chc, fofml, Constraint, Fv, Ident, Logic, Negation, Op, Rename, Subst, Top, Variable,
};
use crate::solver;
use crate::util::Pretty;
use crate::{pdebug, title};

use rpds::Stack;

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
    reduction_info: ReductionInfo,
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
        write!(f, "[Reduction {}]", self.reduction_info.level)?;
        write!(f, "] fvints: {:?}", self.fvints)?;
        writeln!(f, " constraint: {}", self.constraint)?;
        writeln!(f, "{} ", self.predicate)?;
        // for arg in self.args.iter() {
        //     writeln!(f, "- {} ", arg.arg)?;
        // }
        write!(f, "\n ==> {}", self.result)
    }
}

impl Pretty for Reduction {
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
        al.text("[Reduction ")
            .append(self.reduction_info.level.to_string())
            .append(al.text(format!(
                "] fvints: {:?} constraint: {}",
                self.fvints, self.constraint
            )))
            .append(al.hardline())
            .append(
                self.predicate
                    .pretty(al, config)
                    .append(al.hardline())
                    .append(self.reduction_info.level.to_string())
                    .append("==> ")
                    .append(self.result.pretty(al, config))
                    .hang(2),
            )
    }
}

impl Reduction {
    fn new(
        app_expr: G,
        predicate: G,
        result: G,
        arg: ReductionInfo,
        fvints: HashSet<Ident>,
        argints: HashSet<Ident>,
        constraint: Constraint,
    ) -> Reduction {
        Reduction {
            app_expr,
            predicate,
            reduction_info: arg,
            result,
            fvints,
            argints,
            constraint,
        }
    }
    // fn append_reduction(&mut self, reduction_info: ReductionInfo, result: G, app_expr: G) {
    //     if reduction_info.arg_var.ty.is_int() {
    //         self.fvints.insert(reduction_info.old_id);
    //         self.argints.insert(reduction_info.old_id);
    //     }
    //     self.result = result;
    //     self.app_expr = app_expr;
    //     self.args.push(reduction_info);
    // }
    fn level(&self) -> usize {
        self.reduction_info.level
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
                                reduction_info,
                                fvints.clone(),
                                argints.clone(),
                                constraint.clone(),
                            );

                            return Some((ret.clone(), reduction));
                        }
                        None => (),
                    };
                    // case where App(pred, arg) cannot be reduced.
                    // then, we try to reduce pred or arg.
                    go_(
                        optimizer,
                        predicate,
                        level,
                        fvints,
                        argints,
                        constraint.clone(),
                    )
                    .map(|(ret, reduction)| {
                        (G::mk_app_t(ret, arg.clone(), goal.aux.clone()), reduction)
                    })
                    .or_else(|| {
                        go_(optimizer, arg, level, fvints, argints, constraint.clone()).map(
                            |(arg, pred)| {
                                (G::mk_app_t(predicate.clone(), arg, goal.aux.clone()), pred)
                            },
                        )
                    })
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
        pdebug!("->  ", reduced);

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
    fn retrieve_from_track_idents(
        &self,
        model: &chc::Model,
        derivation: &Derivation<Atom>,
    ) -> TyEnv {
        let model = &model.model;
        let mut result_env = TypeEnvironment::new();
        for (pred_name, ids) in self.track_idents.iter() {
            for id in ids {
                for ty in derivation.get_types_by_id(id) {
                    debug!("{}({}): {}", pred_name, id, ty);
                    let ty = ty.assign(&model);
                    let pty = PolymorphicType::poly(ty);
                    result_env.add(*pred_name, pty);
                }
            }
        }
        result_env
    }
    ///// aux functions
    fn append_clauses(clauses: &mut Vec<chc::CHC<chc::Atom, Constraint>>, constraint: &Atom) {
        match constraint.to_chcs_or_pcsps() {
            either::Left(chcs) => {
                pdebug!("constraints" ; title);
                for c in chcs {
                    pdebug!("  -", c);
                    clauses.push(c);
                }
            }
            either::Right(pcsps) => {
                pdebug!("constriant: ", constraint);
                pdebug!("failed to translate the constraint to chcs");
                for c in pcsps {
                    pdebug!(c)
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
            Self::append_clauses(clauses, &constraint);
        }
    }

    fn insert_derivation(
        &self,
        node_id: tree::ID,
        derivation: &mut Derivation<Atom>,
        arg_derivations: Vec<Derivation<Atom>>,
        pred_ty: &Ty,
        app_expr_ty: &Ty,
    ) {
        unimplemented!()
    }

    ///// aux functions end
    fn expand_int_node(
        &self,
        node_id: tree::ID,
        app_exprs: &Vec<G>,
        derivation: &mut Derivation<Atom>,
        reduction: &Reduction,
        ri: &ReductionInfo,
        is_shared_ty: bool,
        tmp_ret_ty: &Ty,
        clauses: &mut Vec<chc::CHC<chc::Atom, Constraint>>,
    ) {
        // constructing body derivation
        let arg_derivations =
            derivation.replace_derivation_at_level_with_var(node_id, &ri.level, ri.arg_var.id);
        assert_eq!(arg_derivations.len(), 0);

        // all Ptr(id) in the constraints in ty should be dereferenced
        derivation.traverse_and_recover_int_var(node_id, &ri.arg_var.id, &ri.old_id);

        let pred_ty = if is_shared_ty {
            match tmp_ret_ty.kind() {
                TauKind::IArrow(id, t) => {
                    derivation.rename_int_var(node_id, &ri.old_id, id);
                    tmp_ret_ty.clone()
                }
                TauKind::Arrow(_, _) | TauKind::Proposition(_) => {
                    panic!("program error")
                }
            }
        } else {
            Tau::mk_iarrow(ri.old_id, tmp_ret_ty.clone())
        };
        // generate derivation and constraints
        todo!()
    }
    fn expand_pred_node(
        &self,
        node_id: tree::ID,
        app_exprs: &Vec<G>,
        derivation: &mut Derivation<Atom>,
        reduction: &Reduction,
        ri: &ReductionInfo,
        is_shared_ty: bool,
        tmp_ret_ty: &Ty,
        clauses: &mut Vec<chc::CHC<chc::Atom, Constraint>>,
    ) {
        // TODO: we also have to replace the expr of each node in the derivation
        let mut arg_derivations =
            derivation.replace_derivation_at_level_with_var(node_id, &ri.level, ri.arg_var.id);

        let (arg_ty, arg_derivations) = if arg_derivations.is_empty() {
            (
                vec![Ty::mk_bot(&ri.arg_var.ty)],
                vec![Derivation::rule_atom(
                    ri.arg.clone(),
                    Ty::mk_bot(&ri.arg_var.ty),
                )],
            )
        } else {
            // if a shared_ty is attached with the predicate we are focusing on, we have to use it
            match &ri.arg.aux.tys {
                Some(tys) => (tys.clone(), arg_derivations),
                None => (
                    arg_derivations
                        .iter()
                        .map(|d| d.root_ty().clone())
                        .collect(),
                    vec![arg_derivations.pop().unwrap()],
                ),
            }
        };

        let (pred_ty, app_expr_ty) = if is_shared_ty {
            match tmp_ret_ty.kind() {
                TauKind::Arrow(ts, t_result) => {
                    Self::append_clauses_by_subst(
                        clauses,
                        ts,
                        &arg_ty,
                        &tmp_ret_ty.rty_no_exists(),
                    );
                    let app_expr_ty = t_result.clone();
                    (tmp_ret_ty.clone(), app_expr_ty)
                }
                TauKind::IArrow(_, _) | TauKind::Proposition(_) => {
                    panic!("program error")
                }
            }
        } else {
            let tmp_ty = Ty::mk_arrow(arg_ty.clone(), tmp_ret_ty.clone());
            (tmp_ty, tmp_ret_ty.clone())
        };
        // generate derivation and generate constraints
    }
    // (\x. g) g' -> [g'/x] g
    fn expand_node(
        &self,
        node_id: tree::ID,
        app_exprs: &Vec<G>,
        derivation: &mut Derivation<Atom>,
        reduction: &Reduction,
        clauses: &mut Vec<chc::CHC<chc::Atom, Constraint>>,
    ) {
        // if ret_ty_idx > 0, then we push calculated types to derivation without "already exists" check
        let ret_ty = derivation.node_id_to_ty(&node_id).clone();
        pdebug!("ret_ty: ", ret_ty);
        let ri = &reduction.reduction_info;

        // prepare a template type for predicate g
        // if a shared_ty is attached with the predicate we are focusing on, we have to use it
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

        // case where the argument is an integer
        if ri.arg_var.ty.is_int() {
            // case where the argument is a predicate
            self.expand_int_node(
                node_id,
                app_exprs,
                derivation,
                reduction,
                ri,
                is_shared_ty,
                &tmp_ret_ty,
                clauses,
            )
        } else {
            self.expand_pred_node(
                node_id,
                app_exprs,
                derivation,
                reduction,
                ri,
                is_shared_ty,
                &tmp_ret_ty,
                clauses,
            )
        };

        pdebug!(
            "app_expr(",
            reduction.app_expr.aux.id,
            "): ",
            reduction.app_expr
        );
    }
    fn infer_type_inner(
        &self,
        derivation: &mut Derivation<Atom>,
        reduction: &Reduction,
        clauses: &mut Vec<chc::CHC<chc::Atom, Constraint>>,
    ) {
        title!("Reduction");
        pdebug!(reduction);
        let node_ids: Stack<_> = derivation
            .get_nodes_by_id(&reduction.result.aux.id)
            .map(|n| n.id)
            .collect();
        if node_ids.iter().len() == 0 {
            pdebug!(
                "search for id=",
                reduction.result.aux.id,
                ",expr=",
                reduction.result,
                " ",
            );
            title!("no ret_tys");
            panic!("fatal");
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

        for node_id in node_ids.iter() {
            self.expand_node(*node_id, &app_exprs, derivation, reduction, clauses);
        }
    }
    fn infer_type(&mut self, mut derivation: Derivation<Atom>) -> Option<TyEnv> {
        let mut clauses = Vec::new();
        debug!("constraints generated during type checking");
        for constraint in derivation.constraints.iter() {
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
                    pt.iarrow(arg_expr.clone(), &v.id)
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
                    pt.arrow(arg_expr.clone(), ts)
                }
                _ => panic!("fatal"),
            },
            _ => {
                let pt =
                    type_check_inner(config, tenv, ienv, all_coefficients, arg_expr, t.clone());
                // skip the continuation of this inner function
                return pt.coarse_type(t);
            }
        };
        pdebug!("handle_abs: |- ", arg_expr, " :",  pt ; bold ; white, " ",);
        pt
    }
    // [feature shared_ty]
    match (&config.tc_mode, &arg_expr.aux.tys) {
        (TCFlag::Normal, _) | (_, None) => {
            handle_abs_inner(config, tenv, ienv, all_coefficients, arg_expr, t)
        }
        (TCFlag::Shared(_), Some(tys)) if tys.len() == 1 => {
            let mut pt = handle_abs_inner(config, tenv, ienv, all_coefficients, arg_expr, &tys[0]);
            pt.coarse_type(t)
        }
        (_, _) => panic!("program error"),
    }
}

#[derive(Clone)]
struct TCConfig {
    tc_mode: TCFlag,
    // TODO
    construct_derivation: bool,
}

#[derive(Clone)]
struct InstantiationConfig {
    derivation: Derivation<Atom>,
}

#[derive(Clone)]
enum TCFlag {
    Normal,
    Shared(InstantiationConfig),
}

fn coarse_expr_for_type_sharing(
    config: &TCConfig,
    pt: PossibleDerivation<Atom>,
    expr: &G,
) -> PossibleDerivation<Atom> {
    // [feature shared_ty] template type sharing
    // if there is a shared type registered, coarse pt to obey the type.
    match (&config.tc_mode, &expr.aux.tys) {
        (TCFlag::Shared(_), Some(tys)) if tys.len() == 1 => pt.coarse_type(&tys[0]),
        (TCFlag::Normal, _) | (_, None) => pt,
        (_, _) => unimplemented!(),
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
        pred_expr: &G,
        cty: Ty, // context ty
    ) -> PossibleDerivation<Atom> {
        match pred_expr.kind() {
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
                                    Derivation::rule_var(pred_expr.clone(), t, coefficients.clone())
                                })
                                .collect();
                            types
                        }
                        // replay the previous instantiation here
                        TCFlag::Shared(d) => {
                            let ct: Vec<_> =
                                d.derivation.get_types_by_id(&pred_expr.aux.id).collect();
                            // TODO: actually we have to consider the case where multiple types are assigned to one expr
                            // This happens when intersection types are inferred; however, in the current setting,
                            // if shared type is enabled, there is no intersection types.
                            // So I just leave it as a future work.
                            // To tackle this issue, there are multiple methods:
                            //   1. track the current branches that we have passed so far every time intersection rules have been applied
                            //   2. track the current node of the previous derivation in d, so that corresponding node of d can easily be
                            //      retrieved
                            //   3. ?
                            assert!(ct.len() == 1);
                            let d = Derivation::rule_atom(pred_expr.clone(), ct[0].clone());
                            vec![d]
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
                            .map(|d| Derivation::rule_iapp(predg.clone(), d, &op))
                            .collect();
                        return PossibleDerivation::new(types); // early return
                    }
                    // Otherwise, we continue.
                    None => (),
                };

                // Case: the argument is not integer
                let mut result_cts = Vec::new();
                // we calculate the argument's type. we have to enumerate all the possible type of pt1.
                for pred_derivation in pred_pt.types {
                    let (arg_t, result_t) = match pred_derivation.root_ty().kind() {
                        TauKind::Arrow(arg, result) => (arg, result),
                        TauKind::Proposition(_) | TauKind::IArrow(_, _) => panic!("fatal"),
                    };
                    let mut arg_derivations = vec![Stack::new()];
                    // check if there exists a derivation for all types in the intersection type.
                    let arg_pts = arg_t.iter().map(|t| {
                        // check if arg_constraint |- argg: arg_t
                        let rty = cty.rty_no_exists();
                        let t_context = t.conjoin_constraint(&rty);
                        handle_abs(config, tenv, ienv, all_coefficients, argg, &t_context)
                    });
                    // Assume pred_pt = t1 /\ t2 -> t
                    // then, we have to derive arg_t: t1 and arg_t: t2
                    // for arg_t: t1, assume there are two derivations d1 and d2 (= arg_pts[0])
                    // for arg_t: t2, also d3 and d4 (= arg_pts[1])
                    // then possible derivations are [d1, d3], [d1, d4],  [d2, d3] and [d2, d4]
                    for pt in arg_pts {
                        let mut new_tmp_cts = Vec::new();
                        // di = d1
                        for di in pt.types {
                            // merge
                            for arg_derivations_so_far in arg_derivations.iter() {
                                new_tmp_cts.push(arg_derivations_so_far.push(di.clone()));
                            }
                        }
                        arg_derivations = new_tmp_cts
                    }
                    // Now that all the argument for `pred_pt` can be derived, we have candidatetype `result_t`
                    // with the derivations of `ct`s
                    for arg_derivation in arg_derivations {
                        result_cts.push(Derivation::rule_app(
                            pred_expr.clone(),
                            pred_derivation.clone(),
                            arg_derivation.iter().cloned(),
                        ));
                    }
                }
                PossibleDerivation::new(result_cts)
            }
            formula::hes::GoalKind::Constr(_)
            | formula::hes::GoalKind::Op(_)
            | formula::hes::GoalKind::Abs(_, _)
            | formula::hes::GoalKind::Conj(_, _)
            | formula::hes::GoalKind::Disj(_, _)
            | formula::hes::GoalKind::Univ(_, _) => panic!("fatal: {}", pred_expr),
        }
    }
    let pt = handle_inner(config, tenv, ienv, all_coefficients, app_expr, cty.clone());

    let pt = coarse_expr_for_type_sharing(config, pt, &app_expr);

    pdebug!("handle_abs: |- ", app_expr, " : ", pt ; bold ; white, " ",);
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
        expr: &G,
        context_ty: Ty,
    ) -> (PossibleDerivation<Atom>, bool) {
        // [pruning]: since we can always derive ψ: ⊥, we do not have to care about this part
        if !config.construct_derivation && context_ty.is_bot() {
            let cd = Derivation::rule_atom(expr.clone(), context_ty.clone());
            return (PossibleDerivation::singleton(cd), false);
        }
        // for App, we delegate the procedure to `handle_app`
        // and in that procedure, it saves the types
        let mut already_registered = false;
        let result_pt = match expr.kind() {
            formula::hes::GoalKind::Constr(constraint) => {
                let constraint = constraint.clone().into();
                let t = Ty::mk_prop_ty(constraint);
                let cd = Derivation::rule_atom(expr.clone(), t);
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

                                let cd = Derivation::rule_var(expr.clone(), ty, coefficients);
                                tys.push(cd);
                            }
                            tys
                        }
                        TCFlag::Shared(d) => {
                            let ct: Vec<_> = d.derivation.get_types_by_id(&expr.aux.id).collect();
                            // TODO: actually we have to consider the case where multiple types are assigned to one expr
                            // This happens when intersection types are inferred; however, in the current setting,
                            // if shared type is enabled, there is no intersection types.
                            // So I just leave it as a future work.
                            // To tackle this issue, there are multiple methods:
                            //   1. track the current branches that we have passed so far every time intersection rules have been applied
                            //   2. track the current node of the previous derivation in d, so that corresponding node of d can easily be
                            //      retrieved
                            //   3. ?
                            assert!(ct.len() == 1);
                            let d = Derivation::rule_atom(expr.clone(), ct[0].clone());
                            vec![d]
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
                PossibleDerivation::conjoin(expr.clone(), t1, t2)
            }
            formula::hes::GoalKind::Disj(g1, g2) => {
                let c1: Option<Constraint> = g1.clone().into();
                let (constr, g, g_) = match c1 {
                    Some(c) => (c, g2, g1),
                    None => (g2.clone().into(), g1, g2),
                };
                let c_neg = constr.negate().unwrap();
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
                    context_ty.conjoin_constraint(&constr.into()),
                );
                PossibleDerivation::disjoin(expr.clone(), t1, t2)
            }
            formula::hes::GoalKind::Univ(x, g) => {
                let b = ienv.insert(x.id);
                let mut pt =
                    type_check_inner(config, tenv, ienv, all_coefficients, &g, context_ty.clone());
                if b {
                    ienv.remove(&x.id);
                }
                // quantify all the constraint.
                pt.quantify(expr.clone(), &x.id);
                pt
            }
            formula::hes::GoalKind::App(_, _) => {
                already_registered = true;
                handle_app(
                    config,
                    tenv,
                    ienv,
                    all_coefficients,
                    expr,
                    context_ty.clone(),
                )
            }
            formula::hes::GoalKind::Abs(_v, _g) => {
                panic!("fatal error")
            }
            // op is always handled by App(x, op)
            formula::hes::GoalKind::Op(_) => panic!("fatal error"),
        };
        (result_pt, already_registered)
    }
    let (pt, _) = go_inner(config, tenv, ienv, all_coefficients, c, context_ty.clone());

    pdebug!("type_check_go(", c.aux.id, ") |- ", c, " : ", pt ; bold);
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
fn type_check_top_with_derivation(psi: &G, tenv: &mut Env) -> Option<Derivation<Atom>> {
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
    let pt = pt.coarse_type(&Ty::mk_prop_ty(Atom::mk_true()));

    // check if there is an actually possible derivation
    pt.check_derivation()
}

/// ε; true ; Γ ⊢ ψ : •<T>
///
/// tenv: Γ
/// candidate: ψ
/// assumption: candidate has a beta-normal form of type *.
fn type_check_top_with_derivation_and_constraints(
    previous_derivation: Derivation<Atom>,
    psi: &G,
    tenv: &mut Env,
) -> Derivation<Atom> {
    title!("type_check_top_with_derivation_and_constraints");
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
    let mut pt = pt.coarse_type(&Ty::mk_prop_ty(Atom::mk_true()));

    // check if there is an actually possible derivation
    // since the derivation has the same shape as `previous_derivation`,
    // we do not have more than one derivation in pt.
    assert!(pt.types.len() == 1);
    let derivation = pt.types.remove(0);

    derivation
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

/// Since type environment can contain multiple candidate types,
/// we make sure that which one is suitable by considering them parallely.
struct PossibleDerivation<C: Refinement> {
    types: Vec<Derivation<C>>,
}
// impl<C: Refinement> fmt::Display for PossibleDerivation<C> {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         if self.types.len() > 0 {
//             write!(f, "{}", self.types[0])?;
//             for t in self.types[1..].iter() {
//                 write!(f, " /\\ {}", t)?;
//             }
//         }
//         Ok(())
//     }
// }

impl Pretty for PossibleDerivation<Atom> {
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
        let docs = self.types.iter().map(|t| t.root_ty().pretty(al, config));
        al.intersperse(docs, al.line().append(al.text("/\\ ")))
            .hang(2)
            .group()
    }
}

impl PossibleDerivation<Atom> {
    fn new(types: Vec<Derivation<Atom>>) -> Self {
        PossibleDerivation { types }
    }

    fn empty() -> Self {
        PossibleDerivation::new(Vec::new())
    }

    fn singleton(cd: Derivation<Atom>) -> Self {
        Self::new(vec![cd])
    }

    fn conjoin(expr: G, pt1: Self, pt2: Self) -> Self {
        let mut ts = Vec::new();
        for d1 in pt1.types.iter() {
            for d2 in pt2.types.iter() {
                let d1 = d1.clone();
                let d2 = d2.clone();
                ts.push(Derivation::rule_conjoin(expr.clone(), d1, d2));
            }
        }
        PossibleDerivation::new(ts)
    }
    fn disjoin(expr: G, pt1: Self, pt2: Self) -> Self {
        let mut ts = Vec::new();
        for d1 in pt1.types.iter() {
            for d2 in pt2.types.iter() {
                let d1 = d1.clone();
                let d2 = d2.clone();
                ts.push(Derivation::rule_disjoin(expr.clone(), d1, d2));
            }
        }
        PossibleDerivation::new(ts)
    }
    fn quantify(&mut self, expr: G, x: &Ident) {
        self.types = self
            .types
            .iter()
            .cloned()
            .map(|d| Derivation::rule_quantifier(expr.clone(), d, x))
            .collect();
    }
    fn iarrow(self, expr: G, x: &Ident) -> Self {
        let types = self
            .types
            .into_iter()
            .map(|ct| Derivation::rule_iarrow(expr.clone(), ct, x))
            .collect();
        PossibleDerivation { types }
    }
    fn arrow(self, expr: G, ts: &Vec<Ty>) -> Self {
        let types = self
            .types
            .into_iter()
            .map(|d| Derivation::rule_arrow(expr.clone(), d, ts.to_vec()))
            .collect();
        PossibleDerivation { types }
    }
}
impl PossibleDerivation<Atom> {
    fn coarse_type(mut self, t: &Ty) -> Self {
        self.types = self
            .types
            .into_iter()
            .map(|d| Derivation::rule_subsumption(d, t.clone()))
            .collect();
        self
    }
    /// check if there is a valid derivation by solving constraints generated
    /// on subsumptions, and returns one if exists.
    fn check_derivation(self) -> Option<Derivation<Atom>> {
        for mut ct in self.types.into_iter() {
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
                    ct.update_with_model(&m);

                    return Some(ct);
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
        let derivation =
            type_check_top_with_derivation_and_constraints(derivation, &ctx.normal_form, tenv);
        match ctx.infer_type(derivation) {
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
