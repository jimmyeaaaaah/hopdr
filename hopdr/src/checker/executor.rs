use crate::ml::FAIL_STRING;
use crate::solver::util;

use std::fmt;
use std::time::Duration;
use tempfile::NamedTempFile;

pub enum ExecResult {
    Unknown,
    Invalid(Option<String>),
    Fail(String),
}

pub(super) fn save_prog(prog: String) -> NamedTempFile {
    util::save_to_file(prog)
}

fn parse_trace(s: &str) -> Option<String> {
    let mut flag = false;
    for line in s.lines() {
        if flag {
            return Some(line.to_string());
        }
        if line.starts_with("[[trace]]") {
            flag = true;
        }
    }
    None
}

#[derive(Debug, Clone, Copy)]
pub struct CounterStats {
    retry: usize,
    recursion: usize,
    rand_int: usize,
}

impl fmt::Display for CounterStats {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "retry: {}, recursion: {}, rand_int: {}",
            self.retry, self.recursion, self.rand_int
        )
    }
}

fn parse_counter_stats(s: &str) -> Option<CounterStats> {
    let mut flag = false;
    let mut itr = s.lines();
    while let Some(line) = itr.next() {
        if line.starts_with("[[counter stats]]") {
            flag = true;
            break;
        }
    }
    if !flag {
        return None;
    }
    let s_retry = itr.next()?;
    let s_recursion = itr.next()?;
    let s_rand_int = itr.next()?;

    let retry = s_retry.split(": ").nth(1)?.parse::<usize>().ok()?;
    let recursion = s_recursion.split(": ").nth(1)?.parse::<usize>().ok()?;
    let rand_int = s_rand_int.split(": ").nth(1)?.parse::<usize>().ok()?;
    Some(CounterStats {
        retry,
        recursion,
        rand_int,
    })
}

#[test]
fn test_parse_counter_stats() {
    let s = r#"
XYZ
YAYY
[[trace]]
hello
[[counter stats]]
retry: 1
recursion: 2
rand_int: 3
next
retry: 1
    "#;
    let stats = parse_counter_stats(s).unwrap();
    assert_eq!(stats.retry, 1);
    assert_eq!(stats.recursion, 2);
    assert_eq!(stats.rand_int, 3);
}

fn parse(s: &str) -> ExecResult {
    if s.contains("FalseExc") {
        ExecResult::Invalid(parse_trace(s))
    } else if s.contains(FAIL_STRING) {
        ExecResult::Unknown
    } else {
        ExecResult::Fail(s.to_string())
    }
}

pub async fn executor(s: String) -> (ExecResult, Option<CounterStats>) {
    let f = save_prog(s);
    let args = vec![f.path().to_str().unwrap()];
    debug!("filename: {}", &args[0]);
    let out = util::exec_input_with_timeout_async(
        "hopdr-check-runner",
        &args,
        &[],
        Duration::from_secs(1),
    )
    .await;
    let s = String::from_utf8(out).unwrap();
    debug!("result: {s}");
    let stats = parse_counter_stats(&s);
    println!("stats: {:?}", stats);
    (parse(&s), stats)
}
