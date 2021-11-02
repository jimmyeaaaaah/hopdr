extern crate lazy_static;
#[macro_use]
extern crate log;
extern crate hopdr;

use hopdr::*;

use nom::error::VerboseError;

fn main() {
    env_logger::init();
    // RUST_LOG=info (trace, debug, etc..)
    debug!("starting up");

    //main3();

    let (_, f) = parse::parse::<VerboseError<&str>>(
        "
        S n k = (n > 0 | k 0) & (n <= 0 | S (n - 1) (L n k));
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

    let (vc, _ctx) = preprocess::hes::preprocess(f);
    for fml in vc.clauses.iter() {
        println!("{}", fml);
    }

    let mut types = Vec::new();
    {
        use engine::*;
        use formula::{Constraint, Ident, Op, PredKind, Top};
        use rtype::Tau;
        // S
        let n = Ident::fresh();
        let m = Ident::fresh();
        let t = Tau::mk_iarrow(
            m,
            Tau::mk_prop_ty(Constraint::mk_pred(
                PredKind::Leq,
                vec![Op::mk_var(n), Op::mk_var(m)],
            )),
        );
        let t = Tau::mk_arrow(t, Tau::mk_prop_ty(Constraint::mk_true()));
        let t = Tau::mk_iarrow(n, t);
        println!("{}", &t);
        types.push(t);

        // K
        let n = Ident::fresh();
        let m = Ident::fresh();
        let t = Tau::mk_iarrow(
            m,
            Tau::mk_prop_ty(Constraint::mk_pred(
                PredKind::Leq,
                vec![Op::mk_var(n), Op::mk_var(m)],
            )),
        );
        let t = Tau::mk_iarrow(n, t);
        println!("{}", &t);
        types.push(t);

        // L
        let n = Ident::fresh();
        let m = Ident::fresh();
        let p = Ident::fresh();
        let t = Tau::mk_iarrow(
            p,
            Tau::mk_prop_ty(Constraint::mk_pred(
                PredKind::Leq,
                vec![Op::mk_const(0), Op::mk_var(p)],
            )),
        );
        //let t = Tau::mk_iarrow(p, Tau::mk_prop_ty(Constraint::mk_true()));
        let s = Tau::mk_iarrow(
            m,
            Tau::mk_prop_ty(Constraint::mk_pred(
                PredKind::Leq,
                vec![Op::mk_var(n), Op::mk_var(m)],
            )),
        );
        let t = Tau::mk_arrow(s, t);
        let t = Tau::mk_iarrow(n, t);
        println!("{}", &t);
        types.push(t);
    }

    let mut env = engine::rtype::PosEnvironment::new();

    for (fml, ty) in vc.clauses.iter().zip(types.iter()) {
        env.add(fml.head.id, ty.clone());
    }

    for (fml, ty) in vc.clauses.iter().zip(types.iter()) {
        let env = (&env).into();
        println!(
            "{}:{}\n -> {:?}",
            fml,
            ty.clone(),
            engine::rtype::type_check_clause(fml, ty.clone(), env)
        );
    }
}

#[allow(dead_code)]
fn main3() {
    println!("starting PDR...");
    let (_, f) = parse::parse::<VerboseError<&str>>(
        "
        S n k = (n > 0 | k 0) & (n <= 0 | S (n - 1) (L n k));
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

    let (vc, _ctx) = preprocess::hes::preprocess(f);
    for fml in vc.clauses.iter() {
        println!("{}", fml);
    }

    engine::infer(vc);
}
