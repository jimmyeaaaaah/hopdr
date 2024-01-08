extern crate hopdr;

use hopdr::*;
use nom::error::VerboseError;

#[test]
fn type_check_1() {
    let (_, f) = parse::parse::<VerboseError<&str>>(
        "
        %HES
		M =v ∀x. S x (K x).
		S n k =v (n > 0 || k 0) && (n <= 0 || S (n - 1) (L n k)).
		K m n =v m <= n.
		L n k m =v k (n + m).
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

    let (vc, _ctx) = preprocess::hes::preprocess_with_default_config(f);
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
        env.add(fml.head.id, Tau::poly(ty.clone()));
    }

    let vc = vc.into();
    assert!(pdr::derivation::check_inductive(&env, &vc))
}

/*
   test HES

   X n f =v f n && X (n + 1) f.
   Y n f =v f n && Y (n - 1) f.
   E n =v n != 0.
   Z x =v X x E || Y x E.
   M =v ∀x. x = 0 || Z x.
*/
#[allow(dead_code)]
fn gen_tyenv_for_test(
    clauses: &[hopdr::formula::hes::Clause<hopdr::formula::Constraint>],
) -> hopdr::pdr::rtype::TyEnv {
    let mut types = Vec::new();
    {
        use formula::{Constraint, Ident, Op, PredKind};
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
        env.add(fml.head.id, Tau::poly(ty.clone()));
    }
    env
}

// [Note] 2022-10-12
// this test is currently unavailable since the input is not conjunctive-nu-HFLZ
// #[test]
// fn type_check_2() {
//     let (_, f) = parse::parse::<VerboseError<&str>>(
//         "
//         %HES
// 	    M =v ∀x. x = 0 || Z x.
// 	    X n f =v f n && X (n + 1) f.
// 	    Y n f =v f n && Y (n - 1) f.
// 	    E n =v n != 0.
// 	    Z x =v X x E || Y x E.
// 	     ",
//     )
//     .unwrap();
//     match &f {
//         parse::Problem::NuHFLZValidityChecking(vc) => {
//             for fml in vc.formulas.iter() {
//                 println!("{}", fml);
//             }
//         }
//     }
//
//     let (vc, _ctx) = preprocess::hes::preprocess(f);
//     for fml in vc.clauses.iter() {
//         println!("{}", fml);
//     }
//
//     let env = gen_tyenv_for_test(&vc.clauses);
//     let vc = vc.into();
//     assert!(pdr::derivation::check_inductive(&env, &vc))
// }

#[test]
fn type_check_poly() {
    let (_, f) = parse::parse::<VerboseError<&str>>(
        "
        %HES
        M =v ∀x. App (\\y. y = x) x.
        App f x =v f x && App f x.
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

    let (vc, _ctx) = preprocess::hes::preprocess_with_default_config(f);
    for fml in vc.clauses.iter() {
        println!("{}", fml);
    }

    let mut types = Vec::new();
    {
        use formula::{Constraint, Ident, Op};
        use hopdr::pdr::*;
        use rtype::Tau;
        // App
        // ∀x.(y:int → •[x=y]) → r:int → •[r=x]
        let x = Ident::fresh();
        let y = Ident::fresh();
        let r = Ident::fresh();
        // y:int → •[x=y]
        let t = Tau::mk_iarrow(
            y,
            Tau::mk_prop_ty(Constraint::mk_eq(Op::mk_var(x), Op::mk_var(y))),
        );
        let s = Tau::mk_iarrow(
            r,
            Tau::mk_prop_ty(Constraint::mk_eq(Op::mk_var(x), Op::mk_var(r))),
        );
        let t = Tau::mk_arrow_single(t, s);
        println!("{}", &t);
        types.push(t);
    }
    use pdr::rtype::*;
    let mut env = TyEnv::new();

    for (fml, ty) in vc.clauses.iter().zip(types.iter()) {
        println!("{}: {}", fml.head.id, ty.clone());
        env.add(fml.head.id, Tau::poly(ty.clone()));
    }

    let vc = vc.into();
    assert!(pdr::derivation::check_inductive(&env, &vc))
}
// [Note] 2022-10-12
// this test is currently unavailable since the input is not conjunctive-nu-HFLZ
// #[test]
// fn type_check_e() {
//     let (_, f) = parse::parse::<VerboseError<&str>>(
//         "
//         %HES
// 	    M =v ∀x. x = 0 || Z x.
// 	    X n f =v f n && X (n + 1) f.
// 	    Y n f =v f n && X (n - 1) f.
// 	    E n =v n != 0.
// 	    Z x =v X x E || Y x E.
// 	     ",
//     )
//     .unwrap();
//     match &f {
//         parse::Problem::NuHFLZValidityChecking(vc) => {
//             for fml in vc.formulas.iter() {
//                 println!("{}", fml);
//             }
//         }
//     }
//
//     let (vc, _ctx) = preprocess::hes::preprocess(f);
//     for fml in vc.clauses.iter() {
//         println!("{}", fml);
//     }
//     let env = gen_tyenv_for_test(&vc.clauses);
//     let vc = vc.into();
//     assert!(!pdr::derivation::check_inductive(&env, &vc))
// }

// #[test]
// fn test_pdr() {
//     let (_, f) = parse::parse::<VerboseError<&str>>(
//         "
//         %HES
//         M =v ∀ x. S x (\\r. r >= x).
//         S n k =v (n > 0 || k n) && (n <= 0 || S (n - 1) (\\r. k (r + n))).
//          ",
//     )
//     .unwrap();
//     match &f {
//         parse::Problem::NuHFLZValidityChecking(vc) => {
//             for fml in vc.formulas.iter() {
//                 println!("{}", fml);
//             }
//             println!("TOP={}", vc.toplevel);
//         }
//     }
//     let (vc, _ctx) = preprocess::hes::preprocess(f);
//
//     match pdr::run(vc) {
//         pdr::VerificationResult::Valid => {
//             assert!(true);
//         }
//         pdr::VerificationResult::Invalid => {
//             assert!(false);
//         }
//         pdr::VerificationResult::Unknown => {
//             assert!(false);
//         }
//     }
// }
//
