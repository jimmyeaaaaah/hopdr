mod ai;
mod executor;

use crate::formula::hes::{Goal, GoalKind, Problem};
use crate::formula::{Constraint, Ident, Logic, Negation, Op, Type as HFLType};
use crate::ml::{optimize, Expr, Function, Program, Type as SType, Variable};
use crate::preprocess::Context;

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
type G = Goal<Constraint>;
impl<'a> Translator<'a> {
    fn new(config: Config<'a>) -> Self {
        Self { config }
    }
    fn translate_type(&self, t: &HFLType) -> SType {
        match t.kind() {
            crate::formula::TypeKind::Proposition => {
                SType::mk_type_arrow(SType::mk_type_unit(), SType::mk_type_unit())
            }
            crate::formula::TypeKind::Integer => SType::mk_type_int(),
            crate::formula::TypeKind::Arrow(t1, t2) => {
                let t1 = self.translate_type(t1);
                let t2 = self.translate_type(t2);
                SType::mk_type_arrow(t1, t2)
            }
        }
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
    fn translate_constraint_inner(&self, c: &Constraint) -> either::Either<Constraint, Expr> {
        match c.kind() {
            crate::formula::ConstraintExpr::True
            | crate::formula::ConstraintExpr::False
            | crate::formula::ConstraintExpr::Pred(_, _) => either::Left(c.clone()),
            crate::formula::ConstraintExpr::Conj(c1, c2) => {
                let c1 = self.translate_constraint_inner(c1);
                let c2 = self.translate_constraint_inner(c2);
                match (c1, c2) {
                    (either::Left(c1), either::Left(c2)) => {
                        either::Left(Constraint::mk_conj(c1, c2))
                    }
                    (either::Left(c), either::Right(e)) | (either::Right(e), either::Left(c)) => {
                        either::Right(Expr::mk_and(Expr::mk_constraint(c), e))
                    }
                    (either::Right(e1), either::Right(e2)) => either::Right(Expr::mk_and(e1, e2)),
                }
            }
            crate::formula::ConstraintExpr::Disj(c1, c2) => {
                let c1 = self.translate_constraint_inner(c1);
                let c2 = self.translate_constraint_inner(c2);
                match (c1, c2) {
                    (either::Left(c1), either::Left(c2)) => {
                        either::Left(Constraint::mk_disj(c1, c2))
                    }
                    (either::Left(c), either::Right(e)) | (either::Right(e), either::Left(c)) => {
                        either::Right(Expr::mk_or(Expr::mk_constraint(c), e))
                    }
                    (either::Right(e1), either::Right(e2)) => either::Right(Expr::mk_or(e1, e2)),
                }
            }
            crate::formula::ConstraintExpr::Quantifier(_, _, _) => todo!(),
        }
    }
    fn translate_constraint(&self, c: &Constraint) -> Expr {
        let e = match self.translate_constraint_inner(c) {
            either::Left(c) => Expr::mk_constraint(c),
            either::Right(e) => e,
        };
        Self::gen_prop(|_| Expr::mk_if(e, Expr::mk_unit(), Expr::mk_raise()))
    }
    fn handle_conj_disj(&self, g11: &G, g12: &G, g21: &G, g22: &G) -> Option<Expr> {
        let s11: Option<Constraint> = g11.clone().into();
        let s12: Option<Constraint> = g12.clone().into();
        let s21: Option<Constraint> = g21.clone().into();
        let s22: Option<Constraint> = g22.clone().into();

        let (c1, g1) = match (s11, s12) {
            (Some(c), _) => (c, g12),
            (_, Some(c)) => (c, g11),
            _ => return None,
        };
        let (c2, g2) = match (s21, s22) {
            (Some(c), _) => (c, g22),
            (_, Some(c)) => (c, g21),
            _ => return None,
        };

        if c1.negate().unwrap() == c2 {
            Some(Translator::gen_prop(move |p| {
                let g1 = self.translate_goal(g1.clone());
                let g2 = self.translate_goal(g2.clone());
                let g1 = Expr::mk_app(g1.clone(), Expr::mk_var(p));
                let g2 = Expr::mk_app(g2.clone(), Expr::mk_var(p));
                Expr::mk_if(self.translate_constraint(&c2), g1, g2)
            }))
        } else {
            None
        }
    }
    // [θ] = fun p -> if not [θ] then raise FalseExc
    // [\x. Ψ] = fun x -> [Ψ]
    // [Ψ1 Ψ2] = [Ψ1] [Ψ2]
    // [Ψ a] = [Ψ] a
    // [Ψ1 /\ Ψ2] = fun p -> if * then [Ψ1] p else [Ψ2]p
    // [θ /\ Ψ2] = fun p -> [θ] p; [Ψ2]p
    // [Ψ1 /\ θ] = fun p -> [θ] p; [Ψ1]p
    // [Ψ1 \/ Ψ2] = fun p -> try [Ψ1]p with FalseExc -> [Ψ2]p
    // [(¬θ \/ Ψ1) /\ (θ \/ Ψ2)] = fun p -> if [θ] then [Ψ1] else  [Ψ2]
    // [∀x. Ψ] = fun p -> let x = * in [Ψ] p
    fn translate_goal(&self, goal: G) -> Expr {
        match goal.kind() {
            GoalKind::Constr(c) => self.translate_constraint(c),
            GoalKind::Op(_) => {
                unreachable!()
            }
            GoalKind::Var(x) => Expr::mk_var(*x),
            GoalKind::Abs(x, g) => {
                let body = self.translate_goal(g.clone());
                let v = Variable::mk(x.id, self.translate_type(&x.ty));
                Expr::mk_fun(v, body)
            }
            GoalKind::App(g1, g2) => {
                let g1 = self.translate_goal(g1.clone());
                // TODO: check the type of g1 so that we can infer g2 is op or not
                // corner case: g2 is a variable
                // I think they are preprocessed but I forgot it
                match g2.kind() {
                    GoalKind::Op(o) => Expr::mk_iapp(g1, o.clone()),
                    _ => {
                        let g2 = self.translate_goal(g2.clone());
                        Expr::mk_app(g1, g2)
                    }
                }
            }
            //
            GoalKind::Conj(g1_fml, g2_fml) => Self::gen_prop(|p| {
                match (g1_fml.kind(), g2_fml.kind()) {
                    (GoalKind::Disj(g11, g12), GoalKind::Disj(g21, g22)) => {
                        match self.handle_conj_disj(g11, g12, g21, g22) {
                            Some(x) => return x,
                            _ => (),
                        }
                    }
                    _ => (),
                };

                let g1 = self.translate_goal(g1_fml.clone());
                let g1 = Expr::mk_app(g1, Expr::mk_var(p));
                let g2 = self.translate_goal(g2_fml.clone());
                let g2 = Expr::mk_app(g2, Expr::mk_var(p));
                let ident = Ident::fresh();
                let c = Constraint::mk_eq(Op::mk_var(ident), Op::zero());

                //[θ /\ Ψ2] = fun p -> [θ] p; [Ψ2]p
                //[Ψ1 /\ θ] = fun p -> [θ] p; [Ψ1]p
                if Into::<Option<Constraint>>::into(g1_fml.clone()).is_some() {
                    Expr::mk_sequential(g1, g2)
                } else if Into::<Option<Constraint>>::into(g2_fml.clone()).is_some() {
                    Expr::mk_sequential(g2, g1)
                } else {
                    let body = Expr::mk_if(Expr::mk_constraint(c), g1, g2);
                    Expr::mk_let_bool_rand(ident, body)
                }
            }),
            GoalKind::Disj(g1, g2) => Self::gen_prop(|p| {
                let g1 = Expr::mk_app(self.translate_goal(g1.clone()), Expr::mk_var(p));
                let g2 = Expr::mk_app(self.translate_goal(g2.clone()), Expr::mk_var(p));
                Expr::mk_try_with(g1, g2)
            }),
            GoalKind::Univ(v, g) => Self::gen_prop(|p| {
                let body = self.translate_goal(g.clone());
                assert!(v.ty.is_int());
                let range = ai::analyze(v.id, g);
                Expr::mk_letrand(v.id, range, Expr::mk_app(body, Expr::mk_var(p)))
            }),
        }
    }
    fn translate(&self, problem: Problem<Constraint>) -> Program {
        let functions: Vec<_> = problem
            .clauses
            .iter()
            .map(|c| {
                let name = c.head.id;
                let ty = self.translate_type(&c.head.ty);
                let body = self.translate_goal(c.body.clone());
                Function { name, ty, body }
            })
            .collect();
        let main = self.translate_goal(problem.top.clone());
        let main = Expr::mk_app(main, Expr::mk_unit());
        Program {
            functions,
            main,
            ctx: &self.config.context,
        }
    }
}

pub fn run(problem: Problem<Constraint>, config: Config) {
    println!("{problem}");
    let trans = Translator::new(config);
    let prog = trans.translate(problem);
    println!("{}", prog.dump_ml());
    let prog = optimize(prog);
    let s = prog.dump_ml();
    println!("{s}");

    match executor::executor(s) {
        executor::ExecResult::Unknown => println!("Unknown"),
        executor::ExecResult::Invalid => println!("Invalid"),
        executor::ExecResult::Fail(s) => println!("Fail\nReason: {s}"),
    }
}
