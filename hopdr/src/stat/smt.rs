use super::STAT;
use std::time::{Duration, Instant};

pub struct SMTStatistics {
    smt_count: usize,
    smt_duration: Duration,
    clock_starts_at: Option<Instant>,
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
            clock_starts_at: None,
        }
    }
}

impl Default for SMTStatistics {
    fn default() -> Self {
        Self::new()
    }
}

pub fn smt_count() {
    STAT.lock().unwrap().smt.smt_count += 1
}

pub fn start_clock() {
    let now = Instant::now();

    STAT.lock().unwrap().smt.clock_starts_at = Some(now)
}

pub fn end_clock() {
    let st = {
        STAT.lock()
            .unwrap()
            .smt
            .clock_starts_at
            .expect("program error")
    };
    let dur = st.elapsed();
    let smt = &mut STAT.lock().unwrap().smt;
    smt.smt_duration += dur;
    smt.clock_starts_at = None;
}

pub fn finalize() {
    let r = { STAT.lock().unwrap().smt.clock_starts_at };
    if r.is_some() {
        end_clock()
    }
}
