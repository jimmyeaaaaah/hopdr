use std::time::Duration;

use tempfile::NamedTempFile;

use crate::solver::util;
pub enum ExecResult {
    Unknown,
    Invalid,
}

pub(super) fn save_prog(prog: String) -> NamedTempFile {
    util::save_to_file(prog)
}

fn parse(s: &str) -> ExecResult {
    if s.contains(&"FalseExc") {
        ExecResult::Invalid
    } else {
        ExecResult::Unknown
    }
}

pub fn executor(s: String) -> ExecResult {
    let f = save_prog(s);
    let args = vec![f.path().to_str().unwrap()];
    debug!("filename: {}", &args[0]);
    let out =
        util::exec_input_with_timeout("hopdr-check-runner", &args, &[], Duration::from_secs(1));
    let s = String::from_utf8(out).unwrap();
    debug!("result: {s}");
    parse(&s)
}
