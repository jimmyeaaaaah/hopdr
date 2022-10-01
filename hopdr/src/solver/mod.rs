pub mod chc;
pub mod disj;
pub mod interpolation;
pub mod sat;
pub mod smt;
mod util;

#[derive(Copy, Clone)]
pub enum SMTSolverType {
    Z3,
    CVC,
    Auto,
}

#[derive(Debug)]
pub enum SolverResult {
    Sat,
    Unsat,
    Unknown,
    Timeout,
}

#[derive(Debug)]
pub struct Model {
    pub model: std::collections::HashMap<crate::formula::Ident, i64>,
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
