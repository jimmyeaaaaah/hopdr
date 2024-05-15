use hoice::common::Discard;
use tempfile::NamedTempFile;

use std::io::Write;
use std::process::Command;
use std::time::Duration;

use tokio;
use tokio::io::AsyncWriteExt;

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

pub async fn exec_input_with_timeout_async(
    cmd: &str,
    args: &[&str],
    input: &[u8],
    _timeout: Duration,
) -> Vec<u8> {
    let mut child = tokio::process::Command::new(cmd)
        .kill_on_drop(true)
        .args(args)
        .args(args)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();

    let mut stdin = child.stdin.take().unwrap();
    stdin.write_all(input).await.unwrap();
    stdin.discard();
    child.wait_with_output().await.unwrap().stdout
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
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();

    proc.stdin.as_mut().unwrap().write_all(&input).unwrap();
    let output = proc.wait_with_output().unwrap();
    output.stdout
}

#[tokio::test]
async fn test_exec_input_with_timeout_async() {
    let output =
        exec_input_with_timeout_async("cat", &[], b"hello\n", Duration::from_secs(1)).await;
    assert_eq!(output, b"hello\n".to_vec());
}

#[test]
fn test_exec_input_with_timeout() {
    let output = exec_input_with_timeout("cat", &[], b"hello\n", Duration::from_secs(1));
    assert_eq!(output, b"hello\n".to_vec());
}
