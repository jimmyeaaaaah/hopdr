use super::STAT;
use std::time::Duration;
pub struct InterpolationStatistics {
    count: usize,
    total_time: Duration,
}

impl std::fmt::Display for InterpolationStatistics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "count: {}", self.count)?;
        writeln!(f, "total time: {:.2} sec", self.total_time.as_secs_f32())?;
        Ok(())
    }
}

impl InterpolationStatistics {
    pub fn new() -> InterpolationStatistics {
        InterpolationStatistics {
            total_time: Duration::ZERO,
            count: 0,
        }
    }
}

pub fn count() {
    STAT.lock().unwrap().interpolation.count += 1;
}

pub fn total_time(total_time: Duration) {
    STAT.lock().unwrap().interpolation.total_time += total_time
}
