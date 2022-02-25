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
    let (s, f) = parse::parse::<VerboseError<&str>>(
        "
        S n k =v (n > 0 || k n) && (n <= 0 || S (n - 1) (\\r. k (r + n))).
        M =v ∀ x. S x (\\r. r >= x).
         ",
    )
    .unwrap();
    println!("{}", s);

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

    pdr::run(vc);
}
