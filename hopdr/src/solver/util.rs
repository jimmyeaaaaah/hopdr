use tempfile::NamedTempFile;

use std::io::Write;
use std::process::Command;
use std::time::Duration;

pub fn save_to_file(s: String) -> NamedTempFile {
    let mut tf = NamedTempFile::new().unwrap();
    debug!("data");
    debug!("{}", &s);
    debug!("data end");
    write!(tf, "{}", s).unwrap();
    tf
}

pub fn exec_with_timeout(cmd: &str, args: &[&str], _timeout: Duration) -> Vec<u8> {
    // todo: timeout
    let output = Command::new(cmd).args(args).output().unwrap();
    output.stdout
}
