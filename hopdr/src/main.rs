#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate log;

pub mod engine;
pub mod formula;
pub mod parse;
pub mod preprocess;
pub mod smt;
pub mod util;

use engine::infer;

use env_logger::Env;
use nom::error::VerboseError;

fn main() {
    env_logger::init();
    // RUST_LOG=info (trace, debug, etc..)
    debug!("starting up");
    let (_, f) = parse::parse::<VerboseError<&str>>(
        "
        S n k = (n != 0 | k n) & (n = 0 | S (n - 1) (L n k));
        K m n = m <= n;
        L n k m = k (n + m);
        M = S 1 (K 1);
         ",
    )
    .unwrap();

    match &f {
        parse::Problem::NuHFLZValidityChecking(vc) => {
            for fml in vc.formulas.iter() {
                println!("{}", fml);
            }
        }
    }

    let (vc, ctx) = preprocess::hes::preprocess(f);
    for fml in vc.clauses.iter() {
        println!("{}", fml);
    }


    let mut types = Vec::new();
    {
        use engine::*;
        use rtype::Tau;
        use formula::{Constraint, Top, Ident, PredKind, Op};
        // S
        let n = Ident::fresh();
        let m = Ident::fresh();
        let t = Tau::mk_iarrow(m, Tau::mk_prop_ty(Constraint::mk_pred(PredKind::Leq, vec![Op::mk_var(n), Op::mk_var(m)])));
        let t = Tau::mk_arrow(t, Tau::mk_prop_ty(Constraint::mk_true()));
        let t = Tau::mk_iarrow(n, t);
        types.push(t);

        // K
        let n = Ident::fresh();
        let m = Ident::fresh();
        let t = Tau::mk_iarrow(m, Tau::mk_prop_ty(Constraint::mk_pred(PredKind::Leq, vec![Op::mk_var(n), Op::mk_var(m)])));
        let t = Tau::mk_iarrow(n, t);
        types.push(t);

        // L
        let n = Ident::fresh();
        let m = Ident::fresh();
        let p = Ident::fresh();
        let t = Tau::mk_iarrow(p, Tau::mk_prop_ty(Constraint::mk_pred(PredKind::Leq, vec![Op::mk_var(n), Op::mk_var(p)])));
        let s = Tau::mk_iarrow(m, Tau::mk_prop_ty(Constraint::mk_pred(PredKind::Leq, vec![Op::mk_var(n), Op::mk_var(m)])));
        let t = Tau::mk_arrow(s, t);
        let t = Tau::mk_iarrow(n, t);
        types.push(t);
    }

    let mut env = engine::rtype::Environment::new();

    for (fml, ty) in vc.clauses.iter().zip(types.iter()) {
        env.tadd(fml.head.id, ty.clone());
    }

    for (fml, ty) in vc.clauses.iter().zip(types.iter()) {
        engine::rtype::type_check_clause(fml, ty.clone(), &mut env);
    }

    //println!("{}", infer(vc));
    //use engine::*;
    //use formula::{Variable, Ident, Constraint, PredKind, Op};
    //// S n k = (n != 0 \/ k m) /\ (n = 0 | S (n - 1) k)

    //let n = Variable::mk(Ident::fresh(), Type::mk_type_int());
    //let k = Variable::mk(Ident::fresh(), Type::mk_type_arrow(Type::mk_type_int(), Type::mk_type_prop()));

    //let expr_1 = Goal::mk_constr(Constraint::mk_pred(PredKind::Neq, vec![Op::mk_var(n.id()), Op::mk_const(0)]));
    //let expr_2 = Goal::mk_constr(Constraint::mk_atom)

    //let args = vec![n, k];
    //let s = Ident::fresh();

    //let clause = engine::Clause::new()
}
