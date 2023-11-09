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
    ExecResult::Unknown
}

pub fn executor(s: String) -> ExecResult {
    let f = save_prog(s);
    let args = vec![f.path().to_str().unwrap()];
    println!("filename: {}", &args[0]);
    crate::util::wait_for_line();
    let out =
        util::exec_input_with_timeout("hopdr-check-runner", &args, &[], Duration::from_secs(1));
    let s = String::from_utf8(out).unwrap();
    println!("result: {s}");
    parse(&s)
}
