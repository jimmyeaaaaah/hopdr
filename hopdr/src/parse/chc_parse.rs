use crate::formula::chc;
use crate::formula::Constraint;
use hoice::instance;
use hoice::parse;

fn parse_file(input: &str) -> Result<Vec<chc::CHC<chc::Atom, Constraint>>, String> {
    println!("wow");
    let mut instance = instance::Instance::new();
    println!("nice");
    let mut cxt = parse::ParserCxt::new();
    println!("hello");
    let res = cxt
        .parser(input, 0, &hoice::common::Profiler::new())
        .parse(&mut instance)
        .expect("parse fail");
    assert_eq!(res, parse::Parsed::CheckSat);

    Ok(Vec::new())
}

#[test]
fn test_parse_file() {
    let input = "(set-logic HORN)
(declare-fun mc91 ( Int Int ) Bool)
(assert (forall ((n Int)) (=> (> n 100) (mc91 n (- n 10)))))
(assert (forall ((n Int) (t Int) (r Int))
    (=>
        (and
            (<= n 100)
            (mc91 (+ n 11) t)
            (mc91 t r)
        )
        (mc91 n r)
    )
))
(assert (forall ((n Int) (r Int))
    (=>
        (and
            (<= n 101)
            (not (= r 91))
            (mc91 n r)
        )
        false
    )
))
(check-sat)
    ";
    parse_file(input).unwrap();
}
