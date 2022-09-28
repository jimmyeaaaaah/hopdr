use super::STAT;
use either::Either;
use std::time::{Duration, Instant};
pub struct OverallStatistics {
    total_time: Either<Instant, Duration>,
}

impl std::fmt::Display for OverallStatistics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.total_time {
            Either::Left(tot) => writeln!(
                f,
                "still ongoing: accumurated time: {:.2} sec",
                tot.elapsed().as_secs_f32()
            )?,
            Either::Right(tot) => {
                writeln!(f, "finished: total time: {:.2} sec", tot.as_secs_f32())?
            }
        };
        Ok(())
    }
}

impl OverallStatistics {
    pub fn new() -> OverallStatistics {
        OverallStatistics {
            total_time: Either::Left(Instant::now()),
        }
    }
}

pub fn finalize() {
    let duration = match STAT.lock().unwrap().overall.total_time {
        Either::Left(now) => now.elapsed(),
        Either::Right(dur) => dur,
    };
    STAT.lock().unwrap().overall.total_time = Either::Right(duration);
}
