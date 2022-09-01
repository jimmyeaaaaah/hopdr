use super::STAT;
use std::{sync::Mutex, time::Duration};
pub struct OverallStatistics {
    total_time: Option<Duration>,
}

impl std::fmt::Display for OverallStatistics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.total_time {
            Some(tot) => writeln!(f, "total time: {:.2} sec", tot.as_secs_f32())?,
            None => (),
        };
        Ok(())
    }
}

impl OverallStatistics {
    pub fn new() -> OverallStatistics {
        OverallStatistics { total_time: None }
    }
}

pub fn register_total_time(total_time: Duration) {
    STAT.lock().unwrap().overall.total_time = Some(total_time)
}
