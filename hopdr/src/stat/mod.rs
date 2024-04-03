//! Singleton Object Statistics is initialized when the program is loaded.
//! By utilizing the functions for updating the statistics, users can register their data.

pub mod chc;
pub mod interpolation;
pub mod overall;
pub mod preprocess;
pub mod smt;

use once_cell::sync::Lazy;
use std::sync::Mutex;

use chc::CHCStatistics;
use interpolation::InterpolationStatistics;
use overall::OverallStatistics;
use preprocess::PreprocessStatistics;
use smt::SMTStatistics;

struct Statistics {
    smt: SMTStatistics,
    overall: OverallStatistics,
    interpolation: InterpolationStatistics,
    chc: CHCStatistics,
    preprocess: PreprocessStatistics,
}

impl Statistics {
    fn new() -> Statistics {
        Statistics {
            chc: CHCStatistics::new(),
            smt: SMTStatistics::new(),
            overall: OverallStatistics::new(),
            interpolation: InterpolationStatistics::new(),
            preprocess: PreprocessStatistics::new(),
        }
    }
}

impl std::fmt::Display for Statistics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "[Preprocess]")?;
        writeln!(f, "{}", self.preprocess)?;
        writeln!(f, "[SMT]")?;
        writeln!(f, "{}", self.smt)?;
        writeln!(f, "[Interpolation]")?;
        writeln!(f, "{}", self.interpolation)?;
        writeln!(f, "[CHC]")?;
        writeln!(f, "{}", self.chc)?;
        writeln!(f, "[Overall]")?;
        writeln!(f, "{}", self.overall)?;
        Ok(())
    }
}

static STAT: Lazy<Mutex<Statistics>> = Lazy::new(|| Mutex::new(Statistics::new()));

pub fn dump() {
    println!("{}", STAT.lock().unwrap());
}

pub fn finalize() {
    crate::stat::overall::finalize();
    self::interpolation::finalize();
    self::smt::finalize();
}
