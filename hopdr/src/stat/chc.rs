use super::STAT;
use std::time::Duration;
pub struct CHCStatistics {
    count: usize,
    total_time: Duration,
}

impl std::fmt::Display for CHCStatistics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "count: {}", self.count)?;
        writeln!(f, "total time: {:.2} sec", self.total_time.as_secs_f32())?;
        Ok(())
    }
}

impl CHCStatistics {
    pub fn new() -> CHCStatistics {
        CHCStatistics {
            total_time: Duration::ZERO,
            count: 0,
        }
    }
}

impl Default for CHCStatistics {
    fn default() -> Self {
        Self::new()
    }
}

pub fn count() {
    STAT.lock().unwrap().chc.count += 1;
}

pub fn total_time(total_time: Duration) {
    STAT.lock().unwrap().chc.total_time += total_time
}
