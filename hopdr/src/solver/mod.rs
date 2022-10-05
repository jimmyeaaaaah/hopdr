use std::fmt;

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

impl fmt::Display for Model {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut keys: Vec<_> = self.model.keys().collect();
        keys.sort();
        for k in keys {
            let v = self.model.get(k).unwrap();
            writeln!(f, "{k}={v};")?;
        }
        Ok(())
    }
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
