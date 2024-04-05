use super::STAT;
use std::time::{Duration, Instant};

pub struct QEStatistics {
    qe_count: usize,
    qe_duration: Duration,
    clock_starts_at: Option<Instant>,
}

impl std::fmt::Display for QEStatistics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "number of invokes of QE solver: {}", self.qe_count)?;
        writeln!(f, "total time: {:.2} sec", self.qe_duration.as_secs_f32())?;
        Ok(())
    }
}

impl QEStatistics {
    pub fn new() -> QEStatistics {
        QEStatistics {
            qe_count: 0,
            qe_duration: Duration::ZERO,
            clock_starts_at: None,
        }
    }
}

impl Default for QEStatistics {
    fn default() -> Self {
        Self::new()
    }
}

pub fn qe_count() {
    STAT.lock().unwrap().qe.qe_count += 1
}

pub fn start_clock() {
    let now = Instant::now();

    STAT.lock().unwrap().qe.clock_starts_at = Some(now)
}

pub fn end_clock() {
    let st = {
        STAT.lock()
            .unwrap()
            .qe
            .clock_starts_at
            .expect("program error")
    };
    let dur = st.elapsed();
    let qe = &mut STAT.lock().unwrap().qe;
    qe.qe_duration += dur;
    qe.clock_starts_at = None;
}

pub fn finalize() {
    let r = { STAT.lock().unwrap().qe.clock_starts_at };
    if r.is_some() {
        end_clock()
    }
}
