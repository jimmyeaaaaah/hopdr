use super::STAT;
use std::time::{Duration, Instant};

use std::collections::HashMap;

pub struct State {
    in_progress: Option<Instant>,
    duration: Duration,
    count: usize,
}

impl State {
    fn new() -> State {
        State {
            in_progress: None,
            duration: Duration::ZERO,
            count: 0,
        }
    }
    fn update(&mut self, duration: Duration) {
        self.duration += duration;
        self.count += 1;
        self.in_progress = None;
    }
    fn end_clock(&mut self) {
        let dr = self.in_progress.expect("program error").elapsed();
        self.update(dr);
    }
    fn is_in_progress(&self) -> bool {
        self.in_progress.is_some()
    }
}

impl std::fmt::Display for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} times, ", self.count)?;
        write!(f, "{:.2} sec", self.duration.as_secs_f32())?;
        Ok(())
    }
}

pub struct PreprocessStatistics {
    sub_clocks: HashMap<&'static str, State>,
}

impl std::fmt::Display for PreprocessStatistics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "total duration: {:.2} sec",
            self.total_duration().as_secs_f32()
        )?;
        for i in self.sub_clocks.iter() {
            writeln!(f, "- {}: {}", i.0, i.1)?;
        }
        Ok(())
    }
}

impl PreprocessStatistics {
    pub fn new() -> PreprocessStatistics {
        PreprocessStatistics {
            sub_clocks: HashMap::new(),
        }
    }
    pub fn total_duration(&self) -> Duration {
        let mut total = Duration::ZERO;
        for (_, state) in self.sub_clocks.iter() {
            total += state.duration;
        }
        total
    }
}

impl Default for PreprocessStatistics {
    fn default() -> Self {
        Self::new()
    }
}

pub fn start_clock(name: &'static str) {
    let now = Instant::now();
    let s = &mut STAT.lock().unwrap().preprocess;
    s.sub_clocks.entry(name).or_insert(State::new()).in_progress = Some(now);
}

pub fn end_clock(name: &'static str) {
    let stat = &mut STAT.lock().unwrap().preprocess;
    let st = stat.sub_clocks.get_mut(name).expect("program error");
    st.end_clock();
}

pub fn finalize() {
    let stat = &mut STAT.lock().unwrap().preprocess;
    stat.sub_clocks.iter_mut().for_each(|(_, state)| {
        if state.is_in_progress() {
            state.end_clock()
        }
    })
}
