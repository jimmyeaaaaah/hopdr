pub mod chc;
pub mod disj;
pub mod interpolation;
pub mod sat;
pub mod smt;
mod util;

#[derive(Copy, Clone)]
pub enum SMT2Style {
    Z3,
    CVC,
}

#[derive(Debug)]
pub enum SolverResult {
    Sat,
    Unsat,
    Unknown,
    Timeout,
}

impl SolverResult {
    pub fn is_sat(&self) -> bool {
        match self {
            SolverResult::Sat => true,
            _ => false,
        }
    }
    pub fn is_unsat(&self) -> bool {
        match self {
            SolverResult::Unsat => true,
            _ => false,
        }
    }
    pub fn is_unknown(&self) -> bool {
        match self {
            SolverResult::Unknown => true,
            _ => false,
        }
    }
    pub fn is_timeout(&self) -> bool {
        match self {
            SolverResult::Timeout => true,
            _ => false,
        }
    }
}
