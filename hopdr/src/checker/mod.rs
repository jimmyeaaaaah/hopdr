mod ai;
mod executor;
mod mode;
mod mode_infer;

use crate::formula::hes::{GoalBase, GoalKind, Problem, ProblemBase};
use crate::formula::{Constraint, Fv, Ident, Op, PredKind, Type as HFLType};
use crate::ml::{optimize, Expr, Function, Program, Type as SType, Variable};
use crate::preprocess::Context;
use mode::{Mode, ModeEnv};

pub struct Config<'a> {
    context: &'a Context,
}

impl<'a> Config<'a> {
    pub fn new(context: &'a Context) -> Self {
        Config { context }
    }
}

struct Translator<'a> {
    config: Config<'a>,
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

impl<'a> Translator<'a> {
    fn new(config: Config<'a>) -> Self {
        Self { config }
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
        let mut args = Vec::new();
        let mut rets = Vec::new();
        let mut pred = goal;
        loop {
            match pred.kind() {
                GoalKind::App(g1, g2) => {
                    match g2.aux.mode.kind() {
                        mode::ModeKind::Out => {
                            let v = g2.var();
                            rets.push(*v);
                        }
                        mode::ModeKind::In | mode::ModeKind::Prop | mode::ModeKind::Fun(_, _) => {
                            let arg = self.handle_app_arg(g2.clone());
                            args.push(arg);
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
        // For handling delay
        body = Expr::mk_app(body, Expr::mk_var(p));
        // TODO: rev?
        Expr::mk_let_tuple(rets, body, cont)
    }
    // [\x. Ψ] = fun x -> [Ψ]
    // [Ψ1 Ψ2] = [Ψ1] [Ψ2]
    // [Ψ a] = [Ψ] a
    fn translate_predicates(&mut self, goal: &GoalM, mut variables: Vec<Ident>) -> Expr {
        let m = &goal.aux.mode;
        if m.is_prop() {
            return if variables.len() == 0 {
                self.translate_goalm(goal, Expr::mk_unit())
            } else {
                let exprs = variables.into_iter().map(|x| Expr::mk_var(x)).collect();
                let cont = Expr::mk_tuple(exprs);
                self.translate_goalm(goal, cont)
            };
        }
        match goal.kind() {
            GoalKind::Var(x) => Expr::mk_var(*x),
            GoalKind::Abs(v, g) if v.ty.is_int() => {
                let arg = m.is_fun().0;
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
                let arg = m.is_fun().0;
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

    fn translate_goalm(&mut self, goal: &GoalM, cont: Expr) -> Expr {
        debug!("tranlsate goal: {}: {}", goal, goal.aux.mode);
        Self::gen_prop(|p| {
            match goal.kind() {
                GoalKind::Constr(c) => self.translate_constraintm(c, cont, &goal.aux.env),
                GoalKind::App(_, _) => self.handle_app(goal.clone(), p, cont),
                GoalKind::Var(x) => Expr::mk_if(Expr::mk_var(*x), Expr::mk_raise(), cont),
                GoalKind::Conj(g1_fml, g2_fml) => {
                    let g1 = self.translate_goalm(g1_fml, cont.clone());
                    let g1 = Expr::mk_app(g1, Expr::mk_var(p));
                    let g2 = self.translate_goalm(g2_fml, cont);
                    let g2 = Expr::mk_app(g2, Expr::mk_var(p));

                    //[θ /\ Ψ2] = fun p -> [θ] p; [Ψ2]p
                    //[Ψ1 /\ θ] = fun p -> [θ] p; [Ψ1]p
                    let left = Expr::mk_try_with(g1.clone(), g2.clone());
                    let right = Expr::mk_try_with(g2, g1);
                    if Into::<Option<Constraint>>::into(g1_fml.clone()).is_some() {
                        left
                    } else if Into::<Option<Constraint>>::into(g2_fml.clone()).is_some() {
                        right
                    } else {
                        self.mk_demonic_branch(left, right)
                    }
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
                    match m.kind() {
                        mode::ModeKind::Out => {
                            // TODO: assert(!body.fv().contains(&v.id));
                            body
                        }
                        mode::ModeKind::In => {
                            assert!(v.ty.is_int());
                            let range = ai::analyze(v.id, g);
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
                let body = self.translate_predicates(&c.body, Vec::new());
                Function { name, ty, body }
            })
            .collect();
        let main = self.translate_goalm(&problem.top, Expr::mk_unit());
        let main = Expr::mk_app(main, Expr::mk_unit());
        Program {
            functions,
            main,
            ctx: &self.config.context,
        }
    }
}

#[test]
fn test_translate_predicate() {
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
        gen_aux(Mode::mk_prop()),
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
    let ctx = Context::empty();
    let mut tr = Translator::new(Config::new(&ctx));
    let e = tr.translate_predicates(&g8, Vec::new());
    println!("{}", e.print_expr(&ctx));
}

pub fn run(problem: Problem<Constraint>, config: Config) {
    println!("translated nu hflz");
    println!("{problem}");
    let mut trans = Translator::new(config);
    let problem_with_mode = mode_infer::infer(problem);
    let prog = trans.translate(problem_with_mode);

    println!("UnOptimized Program");
    println!("{}", prog.dump_ml());
    let prog = optimize(prog);
    let s = prog.dump_ml();
    println!("(* Generated Program *)");
    println!("{s}");

    print!("Verification Result: ");
    match executor::executor(s) {
        executor::ExecResult::Unknown => println!("Unknown"),
        executor::ExecResult::Invalid => println!("Invalid"),
        executor::ExecResult::Fail(s) => println!("Fail\nReason: {s}"),
    }
}
