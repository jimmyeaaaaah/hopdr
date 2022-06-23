extern crate clap;
extern crate hopdr;
extern crate lazy_static;
#[macro_use]
extern crate log;

use hopdr::*;

use clap::Parser;
use colored::Colorize;
use hopdr::title;
use nom::error::VerboseError;

use std::fs;

/// Validity checker for νHFL(Z)
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// Name of the person to greet
    #[clap(short, long)]
    input: String,
}

fn puyu() {
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

    let (vc, _ctx) = preprocess::hes::preprocess(f);
    for fml in vc.clauses.iter() {
        println!("{}", fml);
    }

    let mut types = Vec::new();
    {
        use formula::{Constraint, Ident, Op, PredKind};
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
        env.add(fml.head.id, ty.clone());
    }

    let vc = vc.into();
    assert!(pdr::fml::check_inductive(&env, &vc))
}

fn main() {
    // setting logs
    env_logger::builder()
        .format_timestamp(None)
        .format_module_path(false)
        .format_level(false)
        .init();
    // when the output is redirected to somewhere not a terminal, turn off `colored'
    if !atty::is(atty::Stream::Stdout) || !atty::is(atty::Stream::Stderr) {
        colored::control::set_override(false);
    }
    puyu();

    // parsing command line args
    let args = Args::parse();

    let contents = fs::read_to_string(&args.input).expect("Something went wrong reading the file");

    // RUST_LOG=info (trace, debug, etc..)
    debug!("starting PDR...");
    let (_, f) = parse::parse::<VerboseError<&str>>(&contents).unwrap();

    title!("problem");
    match &f {
        parse::Problem::NuHFLZValidityChecking(vc) => {
            for fml in vc.formulas.iter() {
                debug!("{}", fml);
            }
            debug!("TOP={}", vc.toplevel);
        }
    }

    title!("proprocessed");
    let (vc, _ctx) = preprocess::hes::preprocess(f);
    for fml in vc.clauses.iter() {
        debug!("{}", fml);
    }

    match pdr::run(vc) {
        pdr::VerificationResult::Valid => {
            println!("{}", "Valid".green());
        }
        pdr::VerificationResult::Invalid => {
            println!("{}", "Invalid".red());
        }
        pdr::VerificationResult::Unknown => {
            println!("{}", "Unknown".red());
        }
    }
}
