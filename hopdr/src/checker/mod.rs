use crate::formula::hes::{Goal, Problem};
use crate::formula::{Constraint, Ident, Op, Type as SType, Variable};
use crate::ml::syntax::{Expr, Program};
use crate::ml::Function;
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
impl<'a> Translator<'a> {
    fn new(config: Config<'a>) -> Self {
        Self { config }
    }
    fn translate_type(&self, t: &SType) -> SType {
        match t.kind() {
            crate::formula::TypeKind::Proposition => {
                SType::mk_type_arrow(SType::mk_type_prop(), SType::mk_type_prop())
            }
            crate::formula::TypeKind::Integer => t.clone(),
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
        let v = Variable::mk(p, SType::mk_type_prop());
        let body = f(p);
        Expr::mk_fun(v, body)
    }
    // [θ] = fun p -> θ || p
    // [\x. Ψ] = fun x -> [Ψ]
    // [Ψ1 Ψ2] = [Ψ1] [Ψ2]
    // [Ψ a] = [Ψ] a
    // [Ψ1 /\ Ψ2] = fun p -> if * then [Ψ1]p else [Ψ2]p
    // [Ψ1 \/ Ψ2] = fun p -> [Ψ1] ([Ψ2] p)
    // [∀x. Ψ] = fun p -> let x = * in [Ψ] p
    // [X] = X
    //
    // [X =u Ψ] = let rec X = [Ψ]
    // [({X=u Ψ}, φ)] = [X=u Ψ] in assert([φ] false)
    fn translate_goal(&self, goal: Goal<Constraint>) -> Expr {
        match goal.kind() {
            crate::formula::hes::GoalKind::Constr(c) => {
                Self::gen_prop(|p| Expr::mk_or(Expr::mk_constraint(c.clone()), Expr::mk_var(p)))
            }
            crate::formula::hes::GoalKind::Op(_) => {
                unreachable!()
            }
            crate::formula::hes::GoalKind::Var(x) => Expr::mk_var(*x),
            crate::formula::hes::GoalKind::Abs(x, g) => {
                let body = self.translate_goal(g.clone());
                let v = Variable::mk(x.id, self.translate_type(&x.ty));
                Expr::mk_fun(v, body)
            }
            crate::formula::hes::GoalKind::App(g1, g2) => {
                let g1 = self.translate_goal(g1.clone());
                match g2.kind() {
                    crate::formula::hes::GoalKind::Op(o) => Expr::mk_iapp(g1, o.clone()),
                    _ => {
                        let g2 = self.translate_goal(g2.clone());
                        Expr::mk_app(g1, g2)
                    }
                }
            }
            crate::formula::hes::GoalKind::Conj(g1, g2) => Self::gen_prop(|p| {
                let g1 = self.translate_goal(g1.clone());
                let g1 = Expr::mk_app(g1, Expr::mk_var(p));
                let g2 = self.translate_goal(g2.clone());
                let g2 = Expr::mk_app(g2, Expr::mk_var(p));
                let ident = Ident::fresh();
                let c = Constraint::mk_eq(Op::mk_var(ident), Op::zero());
                let body = Expr::mk_if(c, g1, g2);
                Expr::mk_letrand(ident, body)
            }),
            crate::formula::hes::GoalKind::Disj(g1, g2) => Self::gen_prop(|p| {
                let g1 = self.translate_goal(g1.clone());
                let g2 = self.translate_goal(g2.clone());
                Expr::mk_app(g1, Expr::mk_app(g2, Expr::mk_var(p)))
            }),
            crate::formula::hes::GoalKind::Univ(v, g) => Self::gen_prop(|p| {
                let body = self.translate_goal(g.clone());
                Expr::mk_letrand(v.id, body)
            }),
        }
    }
    fn translate(&self, problem: Problem<Constraint>) -> Program {
        let functions = problem
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
        Program {
            functions,
            main,
            ctx: &self.config.context,
        }
    }
}

pub fn run(problem: Problem<Constraint>, config: Config) {
    let program = Translator::new(config).translate(problem);
}
