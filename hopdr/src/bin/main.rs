extern crate clap;
extern crate hopdr;
extern crate lazy_static;
extern crate log;

use hopdr::*;

use clap::Parser;
use colored::Colorize;
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

fn main() {
    // setting logs
    env_logger::builder()
        .format_timestamp(None)
        .format_module_path(false)
        .format_level(false)
        .init();

    // parsing command line args
    let args = Args::parse();

    let contents = fs::read_to_string(&args.input).expect("Something went wrong reading the file");

    // RUST_LOG=info (trace, debug, etc..)
    println!("starting PDR...");
    let (s, f) = parse::parse::<VerboseError<&str>>(&contents).unwrap();
    //let (s, f) = parse::parse::<VerboseError<&str>>(
    //    "
    //    S n k =v (n > 0 || k n) && (n <= 0 || S (n - 1) (\\r. k (r + n))).
    //    M =v ∀ x. S x (\\r. r >= x).
    //     ",
    //)
    //.unwrap();
    // println!("{}", s);

    match &f {
        parse::Problem::NuHFLZValidityChecking(vc) => {
            for fml in vc.formulas.iter() {
                println!("{}", fml);
            }
            println!("TOP={}", vc.toplevel);
        }
    }

    let (vc, _ctx) = preprocess::hes::preprocess(f);
    //for fml in vc.clauses.iter() {
    //    println!("{}", fml);
    //}

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
