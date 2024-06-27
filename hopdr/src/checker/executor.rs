use crate::ml::FAIL_STRING;
use crate::solver::util;

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

fn parse(s: &str) -> ExecResult {
    if s.contains("FalseExc") {
        ExecResult::Invalid(parse_trace(s))
    } else if s.contains(FAIL_STRING) {
        ExecResult::Unknown
    } else {
        ExecResult::Fail(s.to_string())
    }
}

pub async fn executor(s: String) -> ExecResult {
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
    parse(&s)
}
