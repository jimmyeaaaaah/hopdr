use tempfile::NamedTempFile;

use std::io::Write;
use std::process::Command;
use std::time::Duration;

pub fn save_to_file(s: String) -> NamedTempFile {
    let mut tf = NamedTempFile::new().unwrap();
    // debug!("{}", &s);
    write!(tf, "{}", s).unwrap();
    tf
}

pub fn exec_with_timeout(cmd: &str, args: &[&str], _timeout: Duration) -> Vec<u8> {
    // todo: timeout
    let output = Command::new(cmd).args(args).output().unwrap();
    output.stdout
}

pub fn exec_input_with_timeout(
    cmd: &str,
    args: &[&str],
    input: &[u8],
    _timeout: Duration,
) -> Vec<u8> {
    // todo: timeout
    let mut proc = Command::new(cmd)
        .args(args)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .unwrap();

    proc.stdin.as_mut().unwrap().write_all(&input).unwrap();
    let output = proc.wait_with_output().unwrap();
    output.stdout
}

#[test]
fn test_exec_input_with_timeout() {
    let output = exec_input_with_timeout("cat", &[], b"hello", Duration::from_secs(1));
    assert_eq!(output, b"hello");
}
