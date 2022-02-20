extern crate hopdr;

use hopdr::*;
use nom::error::VerboseError;

#[test]
fn type_check_1() {
    let (_, f) = parse::parse::<VerboseError<&str>>(
        "
		S n k =v (n > 0 || k 0) && (n <= 0 || S (n - 1) (L n k)).
		K m n =v m <= n.
		L n k m =v k (n + m).
		M =v ∀x. S x (K x).
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
        use formula::{Constraint, Ident, Op, PredKind, Top};
        use hopdr::pdr::*;
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
        let t = Tau::mk_arrow_single(t, Tau::mk_prop_ty(Constraint::mk_true()));
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
        let t = Tau::mk_arrow_single(s, t);
        let t = Tau::mk_iarrow(n, t);
        println!("{}", &t);
        types.push(t);
    }
    use pdr::rtype::*;

    let mut env = TyEnv::new();

    for (fml, ty) in vc.clauses.iter().zip(types.iter()) {
        env.add(fml.head.id, ty.clone());
    }

    let vc = vc.into();
    assert!(pdr::fml::check_inductive(&env, &vc))
}

/*
   test HES

   X n f =v f n && X (n + 1) f.
   Y n f =v f n && Y (n - 1) f.
   E n =v n != 0.
   Z x =v X x E || Y x E.
   M =v ∀x. x = 0 || Z x.
*/
fn gen_tyenv_for_test(
    clauses: &[hopdr::formula::hes::Clause<hopdr::formula::Constraint>],
) -> hopdr::pdr::rtype::TyEnv {
    let mut types = Vec::new();
    {
        use formula::{Constraint, Ident, Op, PredKind};
        use hopdr::pdr::*;
        use rtype::Tau;
        // X
        let n = Ident::fresh();
        let m = Ident::fresh();
        let t = Tau::mk_iarrow(
            m,
            Tau::mk_prop_ty(Constraint::mk_pred(
                PredKind::Neq,
                vec![Op::mk_const(0), Op::mk_var(m)],
            )),
        );
        let t = Tau::mk_arrow_single(
            t,
            Tau::mk_prop_ty(Constraint::mk_pred(
                PredKind::Gt,
                vec![Op::mk_var(n), Op::mk_const(0)],
            )),
        );
        let t = Tau::mk_iarrow(n, t);
        println!("{}", &t);
        types.push(t);

        // Y
        let n = Ident::fresh();
        let m = Ident::fresh();
        let t = Tau::mk_iarrow(
            m,
            Tau::mk_prop_ty(Constraint::mk_pred(
                PredKind::Neq,
                vec![Op::mk_const(0), Op::mk_var(m)],
            )),
        );
        let t = Tau::mk_arrow_single(
            t,
            Tau::mk_prop_ty(Constraint::mk_pred(
                PredKind::Lt,
                vec![Op::mk_var(n), Op::mk_const(0)],
            )),
        );
        let t = Tau::mk_iarrow(n, t);
        println!("{}", &t);
        types.push(t);

        // E
        let n = Ident::fresh();
        let t = Tau::mk_iarrow(
            n,
            Tau::mk_prop_ty(Constraint::mk_pred(
                PredKind::Neq,
                vec![Op::mk_var(n), Op::mk_const(0)],
            )),
        );
        println!("{}", &t);
        types.push(t.clone());

        // Z
        types.push(t);
    }

    use pdr::rtype::*;

    let mut env = TyEnv::new();

    for (fml, ty) in clauses.iter().zip(types.iter()) {
        println!("{}: {}", fml.head.id, ty.clone());
        env.add(fml.head.id, ty.clone());
    }
    env
}

#[test]
fn type_check_2() {
    let (_, f) = parse::parse::<VerboseError<&str>>(
        "
	    X n f =v f n && X (n + 1) f.
	    Y n f =v f n && Y (n - 1) f.
	    E n =v n != 0.
	    Z x =v X x E || Y x E.
	    M =v ∀x. x = 0 || Z x.
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

    let env = gen_tyenv_for_test(&vc.clauses);
    let vc = vc.into();
    assert!(pdr::fml::check_inductive(&env, &vc))
}

fn type_check_e() {
    let (_, f) = parse::parse::<VerboseError<&str>>(
        "
	    X n f =v f n && X (n + 1) f.
	    Y n f =v f n && X (n - 1) f.
	    E n =v n != 0.
	    Z x =v X x E || Y x E.
	    M =v ∀x. x = 0 || Z x.
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
    let env = gen_tyenv_for_test(&vc.clauses);
    let vc = vc.into();
    assert!(!pdr::fml::check_inductive(&env, &vc))
}
