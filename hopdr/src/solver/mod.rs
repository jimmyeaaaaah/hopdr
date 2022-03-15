pub mod chc;
pub mod interpolantion;
pub mod smt;
mod util;

#[derive(Copy, Clone)]
pub enum SMT2Style {
    Z3,
}

#[derive(Debug)]
pub enum SolverResult {
    Sat,
    Unsat,
    Unknown,
    Timeout,
}
