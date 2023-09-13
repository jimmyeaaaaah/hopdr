use std::{collections::HashSet, fmt};

pub mod chc;
mod csisat;
pub mod disj;
pub mod interpolation;
pub mod qe;
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

impl Model {
    fn compensate(&mut self, fvs: &HashSet<crate::formula::Ident>) {
        for fv in fvs.iter() {
            if !self.model.contains_key(fv) {
                self.model.insert(*fv, 0);
            }
        }
    }
}

impl SolverResult {
    pub fn is_sat(&self) -> bool {
        matches!(self, SolverResult::Sat)
    }
    pub fn is_unsat(&self) -> bool {
        matches!(self, SolverResult::Unsat)
    }
    pub fn is_unknown(&self) -> bool {
        matches!(self, SolverResult::Unknown)
    }
    pub fn is_timeout(&self) -> bool {
        matches!(self, SolverResult::Timeout)
    }
}
