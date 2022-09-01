use super::STAT;
use std::{sync::Mutex, time::Duration};
pub struct SMTStatistics {
    smt_count: usize,
    smt_duration: Duration,
}

impl std::fmt::Display for SMTStatistics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "number of invokes of SMT solver: {}", self.smt_count)?;
        writeln!(f, "total time: {:.2} sec", self.smt_duration.as_secs_f32())?;
        Ok(())
    }
}

impl SMTStatistics {
    pub fn new() -> SMTStatistics {
        SMTStatistics {
            smt_count: 0,
            smt_duration: Duration::ZERO,
        }
    }
}

pub fn smt_count() {
    STAT.lock().unwrap().smt.smt_count += 1
}
pub fn timer_smt(duration: Duration) {
    STAT.lock().unwrap().smt.smt_duration += duration;
}
