pub mod formula;
pub mod engine;
pub mod smt;

fn main() {
    let v = formula::parse::parse("hello");
    println!("{:?}", v);
}
