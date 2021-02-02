#[macro_use]
extern crate lazy_static;

pub mod formula;
pub mod engine;
pub mod smt;
pub mod parse;
pub mod util;
pub mod preprocess;

use nom::error::VerboseError;


fn main() {
    let (_, f) = parse::parse::<VerboseError<&str>>(
        "
        S n m k = (n != 0 | k m) & (n = 0 | S (n - 1) (m + n) k);
        K m n = m <= n;
        M n = S n 0 (K n);
         ",
    )
    .unwrap();
    let parse::Problem::NuHFLZValidityChecking(nvc) = f;
    for fml in nvc.formulas.iter() {
        println!("{}", fml);
    }
}
