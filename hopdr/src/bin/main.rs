extern crate hopdr;
extern crate lazy_static;
extern crate log;

use hopdr::*;

use nom::error::VerboseError;

fn main() {
    env_logger::builder()
        .format_timestamp(None)
        .format_module_path(false)
        .format_level(false)
        .init();
    // RUST_LOG=info (trace, debug, etc..)
    println!("starting PDR...");
    let (_, f) = parse::parse::<VerboseError<&str>>(
        "
        S n k = (n > 0 | k 0) & (n <= 0 | S (n - 1) (L n k));
        K m n = m <= n;
        L n k m = k (n + m);
        M = ∀ x. S x (K x);
         ",
    )
    .unwrap();

    match &f {
        parse::Problem::NuHFLZValidityChecking(vc) => {
            for fml in vc.formulas.iter() {
                println!("{}", fml);
            }
            println!("TOP={}", vc.toplevel);
        }
    }

    let (vc, _ctx) = preprocess::hes::preprocess(f);
    for fml in vc.clauses.iter() {
        println!("{}", fml);
    }

    //engine::infer(vc);
}
