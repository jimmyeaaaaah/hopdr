#[macro_use]
extern crate lazy_static;

pub mod formula;
pub mod engine;
pub mod smt;
pub mod parse;
pub mod util;
pub mod preprocess;

use formula::Type;
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

    let vc = preprocess::hes::ValidityChecking::from(f);
    for fml in vc.formulas.iter() {
        println!("{}", fml);
    }

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
