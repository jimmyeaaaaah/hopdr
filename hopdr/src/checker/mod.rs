mod ai;
mod executor;
mod mode;
mod mode_infer;

use crate::formula::hes::{GoalBase, GoalKind, Problem, ProblemBase};
use crate::formula::{Bot, Constraint, Fv, Ident, Logic, Op, PredKind, Type as HFLType};
use crate::ml::{optimize, Expr, Function, Program, Range, Type as SType, Variable};
use crate::preprocess::Context;
use crate::stat::check::stat;
use crate::util::Pretty;
pub use executor::ExecResult;
use hoice::common::keywords::op::ge_;
use mode::{Mode, ModeEnv};

use std::collections::HashMap;

// trace functions
const T_MK_APP: &str = "mk_app";
const T_MK_CONJ: &str = "mk_conj";
const T_MK_DISJ: &str = "mk_disj";
const T_MK_UNIV: &str = "mk_univ";
const T_MK_EMPTY_TRACE: &str = "mk_empty_trace";
const TRACE_VARIABLE: &str = "check_trace_variable";

const TRACE_CONJ_LEFT: i64 = 0;
const TRACE_CONJ_RIGHT: i64 = 1;

fn mk_app_trace(name: String, args: Expr) -> Expr {
    let tag = Expr::mk_tag(name);
    let values = vec![tag, args, Expr::mk_tag(TRACE_VARIABLE.to_string())];
    Expr::mk_call_named_fun(T_MK_APP, values)
}
fn mk_conj_trace(idx: i64, cur: Expr) -> Expr {
    let idx = Expr::mk_op(Op::mk_const(idx));
    let values = vec![idx, cur];
    Expr::mk_call_named_fun(T_MK_CONJ, values)
}

fn mk_disj_trace(left: Expr, right: Expr) -> Expr {
    Expr::mk_call_named_fun(T_MK_DISJ, vec![left, right])
}

fn mk_univ_trace(v: Expr, cur: Expr) -> Expr {
    let values = vec![v, cur];
    Expr::mk_call_named_fun(T_MK_UNIV, values)
}

fn mk_empty_trace() -> Expr {
    Expr::mk_call_named_fun(T_MK_EMPTY_TRACE, vec![Expr::mk_unit()])
}

#[derive(Clone)]
pub struct Config {
    context: Context,
    print_check_log: bool,
    no_mode_analysis: bool,
}

impl Config {
    pub fn new(context: &Context, print_check_log: bool, no_mode_analysis: bool) -> Self {
        Config {
            context: context.clone(),
            print_check_log,
            no_mode_analysis,
        }
    }
}

struct Translator {
    config: Config,
    clause_idents: HashMap<Ident, HFLType>,
    track_trace: bool,
}

#[derive(Clone, Debug)]
pub enum DisjInfo {
    Left,
    Right,
}

#[derive(Clone, Debug)]
struct Aux {
    env: ModeEnv,
    mode: Mode,
    // this field is used for univ quantifier and abs
    introduced_mode: Option<Mode>,
    disj_info: Option<DisjInfo>,
}

impl Aux {
    fn new(env: ModeEnv, mode: Mode) -> Self {
        Self {
            env,
            mode,
            introduced_mode: None,
            disj_info: None,
        }
    }
    fn introduced_mode(self, mode: Mode) -> Self {
        Self {
            introduced_mode: Some(mode),
            ..self
        }
    }
    fn disj_info(self, info: DisjInfo) -> Self {
        Self {
            disj_info: Some(info),
            ..self
        }
    }

    fn get_univ_mode(&self) -> &Mode {
        &self.introduced_mode.as_ref().unwrap()
    }
    fn get_disj_info(&self) -> &DisjInfo {
        self.disj_info.as_ref().unwrap()
    }
    fn new_univ(env: ModeEnv, introduced: Mode) -> Self {
        Self::new(env, Mode::mk_prop()).introduced_mode(introduced)
    }
    fn new_disj(env: ModeEnv) -> Self {
        Self::new(env, Mode::mk_prop())
    }
    fn mk_prop(env: ModeEnv) -> Self {
        Self::new(env, Mode::mk_prop())
    }
}

// The type of intermediate representation for each formula
type GoalM = GoalBase<Constraint, Aux>;
type ProblemM = ProblemBase<Constraint, Aux>;

impl<'a> Translator {
    fn new(config: Config, problem: &Problem<Constraint>) -> Self {
        Self {
            config,
            clause_idents: problem
                .clauses
                .iter()
                .map(|x| (x.head.id, x.head.ty.clone()))
                .collect(),
            track_trace: false,
        }
    }
    #[cfg(test)]
    fn new_with_clause_idents(
        config: Config,
        clause_idents: HashMap<Ident, HFLType>,
        track_trace: bool,
    ) -> Self {
        Self {
            config,
            clause_idents,
            track_trace,
        }
    }
    fn translate_type_arg(&self, arg: &Mode, t: &HFLType) -> SType {
        match (arg.kind(), t.kind()) {
            (mode::ModeKind::In, crate::formula::TypeKind::Integer) => SType::mk_type_int(),
            (mode::ModeKind::Out, crate::formula::TypeKind::Integer) => panic!("program error"),
            _ => self.translate_type(arg, t),
        }
    }
    fn translate_type(&self, arg: &Mode, t: &HFLType) -> SType {
        fn inner(arg: &Mode, t: &HFLType, n_int: usize) -> SType {
            match (arg.kind(), t.kind()) {
                (mode::ModeKind::Prop, crate::formula::TypeKind::Proposition) => {
                    if n_int == 0 {
                        SType::mk_type_arrow(SType::mk_type_unit(), SType::mk_type_unit())
                    } else {
                        let mut args = Vec::new();
                        for _ in 0..n_int {
                            args.push(SType::mk_type_int());
                        }
                        SType::mk_tuple(args)
                    }
                }
                (mode::ModeKind::Fun(m1, m2), crate::formula::TypeKind::Arrow(t1, t2)) => {
                    match (m1.kind(), t1.kind()) {
                        (mode::ModeKind::In, crate::formula::TypeKind::Integer) => {
                            SType::mk_type_arrow(SType::mk_type_int(), inner(m2, t2, n_int))
                        }
                        (mode::ModeKind::Out, crate::formula::TypeKind::Integer) => {
                            SType::mk_type_arrow(SType::mk_type_unit(), inner(m2, t2, n_int + 1))
                        }
                        (_, _) => {
                            let t1 = inner(m1, t1, 0);
                            let t2 = inner(m2, t2, n_int);
                            SType::mk_type_arrow(t1, t2)
                        }
                    }
                }
                (_, _) => panic!("program error"),
            }
        }
        inner(arg, t, 0)
    }
    fn gen_prop<F>(f: F) -> Expr
    where
        F: FnOnce(Ident) -> Expr,
    {
        let p = Ident::fresh();
        let v = Variable::mk(p, SType::mk_type_unit());
        let body = f(p);
        Expr::mk_fun(v, body)
    }
    fn handle_app_arg(&mut self, goal: GoalM) -> Expr {
        if goal.aux.mode.is_int() {
            let o: Op = goal.clone().into();
            Expr::mk_op(o)
        } else {
            self.translate_predicates(&goal, Vec::new())
        }
    }
    fn handle_app(&mut self, goal: GoalM, p: Ident, cont: Expr) -> Expr {
        fn handle_out_arg(g: &GoalM, rets: &mut Vec<Ident>, env: &ModeEnv) -> Option<(Ident, Op)> {
            let o = match g.kind() {
                GoalKind::Var(v) => {
                    rets.push(*v);
                    return None;
                }
                GoalKind::Op(o) => o,
                _ => panic!("mode inference error?: {}", g),
            };
            match o.kind() {
                crate::formula::OpExpr::Var(v) => {
                    rets.push(*v);
                    None
                }
                _ => {
                    // case where the argument is not just an argument
                    let tmp_variable = Ident::fresh();
                    let tmp_var = Op::mk_var(tmp_variable);

                    let fv = o.fv();
                    let mut target = None;
                    // find the target output variable, which must be unique
                    for i in fv.iter() {
                        if env.get(i).unwrap().is_out() {
                            assert!(target.is_none());
                            target = Some(*i);
                        }
                    }
                    let target = target.unwrap();
                    let o = Op::solve_for(&target, &tmp_var, &o).unwrap();
                    rets.push(tmp_variable);
                    Some((target, o.clone()))
                }
            }
        }

        let mut args = Vec::new();
        let mut rets = Vec::new();
        let mut pred = goal;
        let mut checks = Vec::new();

        // this vector handles the continuation of the application for handling non-variable arguments
        // E.g.
        // A y (x + 1) -> let z = A y in let x = z - 1 in ...
        let mut cont_lets = Vec::new();

        loop {
            match pred.kind() {
                GoalKind::App(g1, g2) => {
                    let pred_arg_mode = g1.aux.mode.is_fun().unwrap().0;
                    let env = &g1.aux.env;
                    match pred_arg_mode.kind() {
                        mode::ModeKind::Out => match g2.aux.mode.kind() {
                            mode::ModeKind::Out => handle_out_arg(g2, &mut rets, env)
                                .into_iter()
                                .for_each(|t| cont_lets.push(t)),
                            mode::ModeKind::In => {
                                let temp_var = Ident::fresh();
                                rets.push(temp_var);

                                let o: Op = g2.clone().into();
                                checks.push((temp_var, o));
                            }
                            _ => panic!("program error"),
                        },
                        mode::ModeKind::In | mode::ModeKind::Prop => {
                            let arg = self.handle_app_arg(g2.clone());
                            args.push(arg);
                        }
                        mode::ModeKind::Fun(_, _) if &g2.aux.mode == pred_arg_mode => {
                            let arg = self.handle_app_arg(g2.clone());
                            args.push(arg);
                        }
                        mode::ModeKind::Fun(_, _) => {
                            unimplemented!()
                        }
                        mode::ModeKind::InOut | mode::ModeKind::Var(_) => panic!("program error"),
                    }
                    pred = g1.clone();
                }
                _ => break,
            }
        }
        let mut body = self.translate_predicates(&pred, Vec::new());
        for arg in args.into_iter().rev() {
            body = Expr::mk_app(body, arg);
        }
        // case for handling subsumption (passing input variables as the output)
        body = Expr::mk_app(body, Expr::mk_var(p));
        let mut cont = cont;
        if checks.len() > 0 {
            let check = checks
                .into_iter()
                .fold(Constraint::mk_false(), |acc, (v, o)| {
                    Constraint::mk_disj(acc, Constraint::mk_neq(Op::mk_var(v), o))
                });
            cont = Expr::mk_if(Expr::mk_constraint(check), Expr::mk_raise(), cont);
        }
        // case for handling non-variable outputs
        for (t, o) in cont_lets.into_iter().rev() {
            cont = Expr::mk_let(t, Expr::mk_op(o), cont);
        }
        Expr::mk_let_tuple(rets, body, cont)
    }
    // [\x. Ψ] = fun x -> [Ψ]
    // [Ψ1 Ψ2] = [Ψ1] [Ψ2]
    // [Ψ a] = [Ψ] a
    fn translate_predicates(&mut self, goal: &GoalM, mut variables: Vec<Ident>) -> Expr {
        let m = &goal.aux.mode;
        if m.is_prop() {
            let cont = if variables.len() == 0 {
                Expr::mk_unit()
            } else {
                let exprs = variables.into_iter().map(|x| Expr::mk_var(x)).collect();
                Expr::mk_tuple(exprs)
            };
            return self.translate_goalm(goal, cont);
        }
        match goal.kind() {
            GoalKind::Var(x) => Expr::mk_var(*x),
            GoalKind::Abs(v, g) if v.ty.is_int() => {
                let arg = m.is_fun().unwrap().0;
                match arg.kind() {
                    mode::ModeKind::In => {
                        let v = Variable::mk(v.id, self.translate_type_arg(arg, &v.ty));
                        let body = self.translate_predicates(g, variables);
                        Expr::mk_fun(v, body)
                    }
                    mode::ModeKind::Out => {
                        variables.push(v.id);
                        self.translate_predicates(g, variables)
                    }
                    // well-formedness violation
                    mode::ModeKind::Prop
                    | mode::ModeKind::Fun(_, _)
                    | mode::ModeKind::InOut
                    | mode::ModeKind::Var(_) => {
                        panic!("program error")
                    }
                }
            }
            GoalKind::Abs(v, g) => {
                let arg = m.is_fun().unwrap().0;
                let v = Variable::mk(v.id, self.translate_type(arg, &v.ty));
                let body = self.translate_predicates(g, variables);
                Expr::mk_fun(v, body)
            }
            GoalKind::App(_, _) => panic!("eta expansiton fails?"),
            GoalKind::Constr(_)
            | GoalKind::Op(_)
            | GoalKind::Conj(_, _)
            | GoalKind::Disj(_, _)
            | GoalKind::Univ(_, _)
            | GoalKind::ITE(_, _, _) => panic!("program error"),
        }
    }

    fn handle_constr(&self, c: &Constraint, cont: Expr, env: &ModeEnv) -> Expr {
        let fvs = c.fv();
        assert!(!fvs.iter().any(|x| env.get(x).unwrap().is_out()));

        Expr::mk_if(Expr::mk_constraint(c.clone()), Expr::mk_raise(), cont)
    }

    fn handle_neq(&mut self, o1: &Op, o2: &Op, cont: Expr, env: &ModeEnv) -> Expr {
        let mut fvs = o1.fv();
        o2.fv_with_vec(&mut fvs);
        let v: Vec<&Ident> = fvs
            .iter()
            .filter(|x| matches!(env.get(x).unwrap().kind(), mode::ModeKind::Out))
            .collect();
        if v.len() == 0 {
            return self.handle_constr(&Constraint::mk_neq(o1.clone(), o2.clone()), cont, env);
        }
        assert_eq!(v.len(), 1);

        let v = v[0];

        let o = Op::solve_for(v, o1, o2).unwrap();
        Expr::mk_let(*v, Expr::mk_op(o), cont)
    }

    fn translate_constraintm(&mut self, c: &Constraint, cont: Expr, env: &ModeEnv) -> Expr {
        match c.kind() {
            crate::formula::ConstraintExpr::Pred(PredKind::Neq, l) if l.len() == 2 => {
                self.handle_neq(&l[0], &l[1], cont, env)
            }
            _ => self.handle_constr(c, cont, env),
        }
    }

    fn mk_demonic_branch(&self, e1: Expr, e2: Expr) -> Expr {
        let ident = Ident::fresh();
        let c = Constraint::mk_eq(Op::mk_var(ident), Op::zero());
        let body = Expr::mk_if(Expr::mk_constraint(c), e1, e2);
        Expr::mk_let_bool_rand(ident, body)
    }

    fn destruct_trace<F>(&self, e: Expr, f: F) -> Expr
    where
        F: FnOnce(Expr) -> Expr,
    {
        if self.track_trace {
            let x = Ident::fresh();
            let cont = f(Expr::mk_var(x));
            Expr::mk_let(x, e, cont)
        } else {
            e
        }
    }
    fn with_empty_trace(&self, e: Expr) -> Expr {
        if self.track_trace {
            Expr::mk_sequential(
                e,
                Expr::mk_call_named_fun(T_MK_EMPTY_TRACE, vec![Expr::mk_unit()]),
            )
        } else {
            e
        }
    }

    // TODO: merge predicate2 and predicate
    fn translate_predicates2(&mut self, goal: &GoalM) -> Expr {
        let m = &goal.aux.mode;
        if m.is_prop() {
            return self.translate_goalm2(goal);
        }
        match goal.kind() {
            GoalKind::Var(x) => Expr::mk_var(*x),
            GoalKind::Abs(v, g) if v.ty.is_int() => {
                let arg = m.is_fun().unwrap().0;
                let v = Variable::mk(v.id, self.translate_type_arg(arg, &v.ty));
                let body = self.translate_predicates2(g);
                Expr::mk_fun(v, body)
            }
            GoalKind::Abs(v, g) => {
                let arg = m.is_fun().unwrap().0;
                let v = Variable::mk(v.id, self.translate_type(arg, &v.ty));
                let body = self.translate_predicates2(g);
                Expr::mk_fun(v, body)
            }
            GoalKind::App(_, _) => panic!("eta expansiton fails?"),
            GoalKind::Constr(_)
            | GoalKind::Op(_)
            | GoalKind::Conj(_, _)
            | GoalKind::Disj(_, _)
            | GoalKind::Univ(_, _)
            | GoalKind::ITE(_, _, _) => panic!("program error"),
        }
    }
    fn handle_app2(&mut self, goal: &GoalM, p: Ident) -> Expr {
        let mut pred = goal.clone();
        let mut args = Vec::new();
        let mut memos = Vec::new();
        loop {
            match pred.kind() {
                GoalKind::App(g1, g2) => {
                    let arg = self.translate_predicates2(g2);
                    args.push(arg.clone());
                    if g2.aux.mode.is_int() {
                        memos.push(arg);
                    }
                    pred = g1.clone();
                }
                _ => break,
            }
        }
        let mut body = self.translate_predicates2(&pred);
        for arg in args.into_iter().rev() {
            body = Expr::mk_app(body, arg);
        }
        body = Expr::mk_app(body, Expr::mk_var(p));
        let tr = match pred.kind() {
            GoalKind::Var(x) => match self.config.context.inverse_map.get(x) {
                Some(c) => mk_app_trace(c.clone(), Expr::mk_list(memos)),
                None => mk_empty_trace(),
            },
            _ => mk_empty_trace(),
        };
        Expr::mk_sequential(body, tr)
    }

    // * = trace
    fn translate_goalm2(&mut self, goal: &GoalM) -> Expr {
        println!("translating: {}", goal.pretty_display());
        use crate::formula::Negation;
        Self::gen_prop(|p| match goal.kind() {
            GoalKind::Constr(c) => {
                self.with_empty_trace(Expr::mk_assert(Expr::mk_constraint(c.negate().unwrap())))
            }
            GoalKind::Op(_) => panic!("program error"),
            GoalKind::Var(x) => {
                let v = Expr::mk_var(*x);
                let body = Expr::mk_unit();
                self.with_empty_trace(Expr::mk_app(v, body))
            }
            GoalKind::Abs(_, _) => {
                panic!("program error")
            }
            GoalKind::App(_, _) => self.handle_app2(goal, p),
            GoalKind::Conj(g1_fml, g2_fml) => {
                let g1 = self.translate_goalm2(g1_fml);
                let g1 = self.destruct_trace(g1, |x| mk_conj_trace(TRACE_CONJ_LEFT, x));
                let g2 = self.translate_goalm2(g1_fml);
                let g2 = self.destruct_trace(g2, |x| mk_conj_trace(TRACE_CONJ_RIGHT, x));
                let left = Expr::mk_try_with(g1.clone(), g2.clone());
                let right = Expr::mk_try_with(g2.clone(), g2.clone());
                if Into::<Option<Constraint>>::into(g1_fml.clone()).is_some() {
                    left
                } else if Into::<Option<Constraint>>::into(g2_fml.clone()).is_some() {
                    right
                } else {
                    self.mk_demonic_branch(left, right)
                }
            }
            GoalKind::Disj(g1, g2) => {
                println!("disj");
                let e1 = self.translate_goalm2(g1);
                let e2 = self.translate_goalm2(g2);
                self.destruct_trace(e1, |x| self.destruct_trace(e2, |y| mk_disj_trace(x, y)))
            }
            GoalKind::Univ(v, g) => {
                let body = self.translate_goalm2(g);
                self.destruct_trace(body, |x| mk_univ_trace(Expr::mk_var(v.id), x))
            }
            GoalKind::ITE(c, g1, g2) => {
                let e1 = self.translate_goalm2(g1);
                let g1 = self.destruct_trace(e1, |x| mk_conj_trace(TRACE_CONJ_LEFT, x));
                let e2 = self.translate_goalm2(g2);
                let g2 = self.destruct_trace(e2, |x| mk_conj_trace(TRACE_CONJ_RIGHT, x));
                Expr::mk_if(Expr::mk_constraint(c.clone()), g1, g2)
            }
        })
    }

    fn translate_goalm(&mut self, goal: &GoalM, cont: Expr) -> Expr {
        debug!("tranlsate goal: {}: {}", goal, goal.aux.mode);
        Self::gen_prop(|p| {
            match goal.kind() {
                GoalKind::Constr(c) => self.translate_constraintm(c, cont, &goal.aux.env),
                GoalKind::Var(x) => {
                    Expr::mk_sequential(Expr::mk_app(Expr::mk_var(*x), Expr::mk_var(p)), cont)
                }
                GoalKind::App(_, _) => self.handle_app(goal.clone(), p, cont),
                GoalKind::Conj(g1_fml, g2_fml) => {
                    let fvs: Vec<Ident> = cont
                        .fv()
                        .into_iter()
                        .filter(|x| !self.clause_idents.contains_key(x))
                        .filter(|x| match goal.aux.env.get(x) {
                            Some(x) => x.is_out(),
                            None => false,
                        })
                        .collect();

                    let cont_v = Expr::mk_tuple(fvs.iter().map(|x| Expr::mk_var(*x)).collect());

                    let g1 = self.translate_goalm(g1_fml, cont_v.clone());
                    let g1 = Expr::mk_app(g1, Expr::mk_var(p));
                    let g2 = self.translate_goalm(g2_fml, cont_v);
                    let g2 = Expr::mk_app(g2, Expr::mk_var(p));

                    //[θ /\ Ψ2] = fun p -> [θ] p; [Ψ2]p
                    //[Ψ1 /\ θ] = fun p -> [θ] p; [Ψ1]p
                    //[Ψ1 /\ Ψ2] = fun p -> let tr = 1::tr in [Ψ1] p * [Ψ2] p
                    let left = Expr::mk_try_with(g1.clone(), g2.clone());
                    let right = Expr::mk_try_with(g2, g1);
                    let body = if Into::<Option<Constraint>>::into(g1_fml.clone()).is_some() {
                        mk_conj_trace(0, left)
                    } else if Into::<Option<Constraint>>::into(g2_fml.clone()).is_some() {
                        mk_conj_trace(1, right)
                    } else {
                        self.mk_demonic_branch(left, right)
                    };
                    Expr::mk_let_tuple(fvs, body, cont)
                }
                GoalKind::Disj(g1, g2) => {
                    let (g1, g2) = match goal.aux.get_disj_info() {
                        DisjInfo::Left => (g1, g2),
                        DisjInfo::Right => (g2, g1),
                    };
                    let cont = Expr::mk_app(self.translate_goalm(g2, cont), Expr::mk_var(p));
                    Expr::mk_app(self.translate_goalm(g1, cont), Expr::mk_var(p))
                }
                GoalKind::Univ(v, g) => {
                    let body = Expr::mk_app(self.translate_goalm(g, cont), Expr::mk_var(p));
                    let m = goal.aux.get_univ_mode();
                    let body = self.destruct_trace(body, |x| mk_univ_trace(Expr::mk_var(v.id), x));
                    match m.kind() {
                        mode::ModeKind::Out => {
                            // TODO: assert(!body.fv().contains(&v.id));
                            body
                        }
                        mode::ModeKind::In => {
                            assert!(v.ty.is_int() || v.ty.is_bit());
                            let mut range = ai::analyze(v.id, g);
                            if v.ty.is_bit() {
                                range = range.meet(Range::boolean())
                            }
                            Expr::mk_letrand(v.id, range, body)
                        }
                        mode::ModeKind::InOut => unimplemented!(), // This is another case where it is unreachable in theory
                        mode::ModeKind::Prop
                        | mode::ModeKind::Fun(_, _)
                        | mode::ModeKind::Var(_) => {
                            panic!("program error")
                        }
                    }
                }
                GoalKind::ITE(c, g1, g2) => {
                    let g1 = self.translate_goalm(g1, cont.clone());
                    let g2 = self.translate_goalm(g2, cont.clone());
                    Expr::mk_app(
                        Expr::mk_if(Expr::mk_constraint(c.clone()), g1, g2),
                        Expr::mk_var(p),
                    )
                }
                GoalKind::Op(_) | GoalKind::Abs(_, _) => {
                    panic!("program error: mode inference is wrong?")
                }
            }
        })
    }
    fn translate(&mut self, problem: ProblemM) -> Program {
        let functions: Vec<_> = problem
            .clauses
            .iter()
            .map(|c| {
                let name = c.head.id;
                let ty = self.translate_type(&c.body.aux.mode, &c.head.ty);
                if self.track_trace {
                    let body = self.translate_predicates2(&c.body);
                    Function { name, ty, body }
                } else {
                    let body = self.translate_predicates(&c.body, Vec::new());
                    Function { name, ty, body }
                }
            })
            .collect();
        let main = if self.track_trace {
            self.translate_goalm2(&problem.top)
        } else {
            self.translate_goalm(&problem.top, Expr::mk_unit())
        };
        let main = Expr::mk_app(main, Expr::mk_unit());
        Program {
            functions,
            main,
            ctx: &self.config.context,
        }
    }
}

#[cfg(test)]
fn gen_fml_for_test() -> GoalM {
    // P = \x. \y. ∀w. (x < 101 \/ y != x - 10) /\ (x >= 101 \/ (P (x+11) w \/ P w y)).
    let x = Ident::fresh();
    let y = Ident::fresh();
    let w = Ident::fresh();
    let p = Ident::fresh();
    let mp = Mode::mk_fun(Mode::mk_in(), Mode::mk_fun(Mode::mk_out(), Mode::mk_prop()));
    let c = Constraint::mk_geq(Op::mk_var(x), Op::mk_const(101));
    let c2 = Constraint::mk_neq(Op::mk_var(y), Op::mk_sub(Op::mk_var(x), Op::mk_const(10)));

    let env = ModeEnv::new();
    let env = env.insert(x, Mode::mk_in()).insert(y, Mode::mk_out());

    let g1 = GoalBase::mk_constr_t(
        c2,
        Aux {
            env: env.insert(w, Mode::mk_in()),
            mode: Mode::mk_prop(),
            introduced_mode: None,
            disj_info: None,
        },
    );

    let gen_aux = |mode| Aux {
        env: env.insert(w, Mode::mk_in()),
        mode,
        introduced_mode: None,
        disj_info: None,
    };
    // P w
    let g2: GoalBase<Constraint, Aux> = GoalBase::mk_app_t(
        GoalBase::mk_var_t(p, gen_aux(mp.clone())),
        GoalBase::mk_var_t(w, gen_aux(Mode::mk_in())),
        gen_aux(Mode::mk_fun(Mode::mk_out(), Mode::mk_prop())),
    );
    // P w y
    let g2 = GoalBase::mk_app_t(
        g2,
        GoalBase::mk_var_t(y, gen_aux(Mode::mk_out())),
        gen_aux(Mode::mk_prop()),
    );

    // P (x + 11)
    let g3: GoalBase<Constraint, Aux> = GoalBase::mk_app_t(
        GoalBase::mk_var_t(p, gen_aux(mp)),
        GoalBase::mk_op_t(
            Op::mk_add(Op::mk_var(x), Op::mk_const(11)),
            gen_aux(Mode::mk_in()),
        ),
        gen_aux(Mode::mk_fun(Mode::mk_out(), Mode::mk_prop())),
    );
    // P (x + 11) w
    let g3 = GoalBase::mk_app_t(
        g3,
        GoalBase::mk_var_t(w, gen_aux(Mode::mk_out())),
        gen_aux(Mode::mk_prop()),
    );

    // P w y \/ P (x + 11) w
    let g4 = GoalBase::mk_disj_t(
        g2,
        g3,
        Aux {
            env: env.insert(w, Mode::mk_inout()),
            mode: Mode::mk_prop(),
            introduced_mode: None,
            disj_info: Some(DisjInfo::Right),
        },
    );
    let g5 = GoalBase::mk_ite_t(c, g1, g4, gen_aux(Mode::mk_prop()));

    let gen_aux = |mode| Aux {
        env: env.clone(),
        mode,
        introduced_mode: None,
        disj_info: None,
    };
    let g6 = GoalBase::mk_univ_t(
        crate::formula::Variable::mk(w, HFLType::mk_type_int()),
        g5,
        Aux {
            env: env.clone(),
            mode: Mode::mk_prop(),
            introduced_mode: Some(Mode::mk_out()),
            disj_info: None,
        },
    );
    let g7 = GoalBase::mk_abs_t(
        crate::formula::Variable::mk(y, HFLType::mk_type_int()),
        g6,
        gen_aux(Mode::mk_fun(Mode::mk_out(), Mode::mk_prop())),
    );
    let g8 = GoalBase::mk_abs_t(
        crate::formula::Variable::mk(x, HFLType::mk_type_int()),
        g7,
        gen_aux(Mode::mk_fun(
            Mode::mk_in(),
            Mode::mk_fun(Mode::mk_out(), Mode::mk_prop()),
        )),
    );
    println!("{g8}");
    g8
}

#[test]
fn test_translate_predicate() {
    let g8 = gen_fml_for_test();
    let ctx = Context::empty();
    let mut tr =
        Translator::new_with_clause_idents(Config::new(&ctx, true, false), HashMap::new(), false);
    let e = tr.translate_predicates(&g8, Vec::new());
    println!("{}", e.print_expr(&ctx));
}

#[test]
fn test_translate_predicate_trace() {
    //let g8 = gen_fml_for_test();

    let ctx = Context::empty();
    /// Currently, mode out is not supported in the trace mode
    //let mut tr =
    //    Translator::new_with_clause_idents(Config::new(&ctx, true, false), HashMap::new(), true);
    //let e = tr.translate_predicates2(&g8);
    //println!("clause 1: {}", g8.pretty_display());
    //println!("{}", e.print_expr(&ctx));

    // P = \x. \y. ∀w. x < y \/ y < w
    let x = Ident::fresh();
    let y = Ident::fresh();
    let w = Ident::fresh();
    let c = Constraint::mk_lt(Op::mk_var(x), Op::mk_var(y));
    let c2 = Constraint::mk_lt(Op::mk_var(y), Op::mk_var(w));
    let g = GoalBase::mk_constr_t(
        c,
        Aux {
            env: ModeEnv::new()
                .insert(y, Mode::mk_in())
                .insert(x, Mode::mk_in()),
            mode: Mode::mk_prop(),
            introduced_mode: None,
            disj_info: None,
        },
    );
    let g2 = GoalBase::mk_constr_t(
        c2,
        Aux {
            env: ModeEnv::new()
                .insert(w, Mode::mk_in())
                .insert(y, Mode::mk_in()),
            mode: Mode::mk_prop(),
            introduced_mode: None,
            disj_info: None,
        },
    );
    let g3 = GoalBase::mk_disj_t(
        g,
        g2,
        Aux {
            env: ModeEnv::new()
                .insert(w, Mode::mk_in())
                .insert(x, Mode::mk_in())
                .insert(y, Mode::mk_in()),
            mode: Mode::mk_prop(),
            introduced_mode: None,
            disj_info: Some(DisjInfo::Right),
        },
    );
    let g4 = GoalBase::mk_univ_t(
        crate::formula::Variable::mk(w, HFLType::mk_type_int()),
        g3,
        Aux {
            env: ModeEnv::new()
                .insert(x, Mode::mk_in())
                .insert(y, Mode::mk_in()),
            mode: Mode::mk_prop(),
            introduced_mode: Some(Mode::mk_in()),
            disj_info: None,
        },
    );

    let g5 = GoalBase::mk_abs_t(
        crate::formula::Variable::mk(y, HFLType::mk_type_int()),
        g4,
        Aux {
            env: ModeEnv::new().insert(x, Mode::mk_in()),
            mode: Mode::mk_fun(Mode::mk_in(), Mode::mk_prop()),
            introduced_mode: None,
            disj_info: None,
        },
    );

    let g6 = GoalBase::mk_abs_t(
        crate::formula::Variable::mk(x, HFLType::mk_type_int()),
        g5,
        Aux {
            env: ModeEnv::new(),
            mode: Mode::mk_fun(Mode::mk_in(), Mode::mk_fun(Mode::mk_in(), Mode::mk_prop())),
            introduced_mode: None,
            disj_info: None,
        },
    );

    let mut tr =
        Translator::new_with_clause_idents(Config::new(&ctx, true, false), HashMap::new(), true);
    let e = tr.translate_predicates2(&g6);
    println!("\nclause 2: {}", g6.pretty_display());
    println!("{}", e.print_expr(&ctx));
}

pub async fn run(problem: Problem<Constraint>, config: Config) -> executor::ExecResult {
    if config.print_check_log {
        println!("translated nu hflz");
        println!("{}", problem.pretty_display_with_context(&config.context));
    }
    let mut trans = Translator::new(config.clone(), &problem);
    let problem_with_mode = stat("mode infer", || {
        mode_infer::infer(problem, config.no_mode_analysis)
    });
    let prog = stat("translate", || trans.translate(problem_with_mode));

    let prog = stat("optimize", || optimize(prog));
    let s = stat("dump_ml", || prog.dump_ml());
    if config.print_check_log {
        println!("(* Generated Program *)");
        println!("{s}");
    }
    stat("execute", || executor::executor(s)).await
}

/// This function is used to calculate the difficulty score of the problem.
///
/// Current implementation returns 2 * number of quantifiers in the clauses + number of quantifiers in the top formula.
pub fn difficulty_score(problem: &Problem<Constraint>) -> usize {
    let mut score = 0;
    for c in &problem.clauses {
        score += 2 * c.body.count_quantifier();
    }
    score += problem.top.count_quantifier();
    score
}
