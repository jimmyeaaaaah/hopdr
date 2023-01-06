use super::STAT;
use std::time::Duration;
use std::time::Instant;
pub struct InterpolationStatistics {
    count: usize,
    total_time: Duration,
    clock_starts_at: Option<Instant>,
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
            clock_starts_at: None,
        }
    }
}

impl Default for InterpolationStatistics {
    fn default() -> Self {
        Self::new()
    }
}

pub fn count() {
    STAT.lock().unwrap().interpolation.count += 1;
}

pub fn start_clock() {
    let now = Instant::now();

    STAT.lock().unwrap().interpolation.clock_starts_at = Some(now)
}

pub fn end_clock() {
    let mut stat = STAT.lock().unwrap();
    let st = stat.interpolation.clock_starts_at.expect("program error");
    let dur = st.elapsed();
    stat.interpolation.total_time += dur;
    stat.interpolation.clock_starts_at = None;
}

pub fn finalize() {
    let r = { STAT.lock().unwrap().interpolation.clock_starts_at };
    if r.is_some() {
        end_clock()
    }
}
