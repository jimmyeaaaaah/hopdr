use std::io::{self, Write};
use std::process::{Command, Stdio};

#[derive(Debug)]
pub enum Error {
    Preprocessor(String),
    UTFEncode,
    FailedToExecute(io::Error),
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Self {
        Error::FailedToExecute(e)
    }
}

impl From<std::string::FromUtf8Error> for Error {
    fn from(_: std::string::FromUtf8Error) -> Self {
        Error::UTFEncode
    }
}

/// check if the given byte slice starts with "(check-sat"
///
/// This can detect check-sat and check-sat-assuming commands
fn starts_with_check_sat(s: &[u8]) -> bool {
    let check_sat = b"(check-sat";
    s.starts_with(check_sat)
}

/// reads until it encounters "(check-sat" and writes the content to the given buffer
/// then returns Ok(s) where s is the continuation of the clauses
/// such as "(check-sat)\n(exit)" if succeeds
fn inputs_smt2_to_z3(filename: &str, mut buf: impl Write) -> Result<(), Error> {
    let data = std::fs::read(filename).unwrap();
    let mut idx = 0;
    let len = data.len();
    while idx < len {
        if starts_with_check_sat(&data[idx..]) {
            buf.write_all(&data[..idx])?;
            buf.write_all(b"\n(apply (then horn-simplify) :print false :print-benchmark true)")?;
            buf.write_all(b"\n(exit)")?;
            return Ok(());
        }
        idx += 1
    }
    Err(Error::Preprocessor("check-sat not found".to_string()))
}

/// Preprocess the given file and returns the HFLz formula string
///
/// Before open `filename`, `open_file_with_preprocess` executes command `hfl-preprocessor` (github.com/moratorium08/hfl-preprocessor`,
/// which transforms hfls with some heuristics without changing the validity (inlining, removing disjunctions, etc)
/// These functionalities should be implemented in hopdr in the future.
pub fn open_file_with_preprocess(filename: &str) -> Result<String, Error> {
    crate::stat::preprocess::start_clock("spacer-preprocessor");

    const CMD: &str = "z3";

    let args = vec!["-in"];
    let mut child = Command::new(CMD)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    let child_stdin = child.stdin.as_mut().unwrap();

    inputs_smt2_to_z3(filename, child_stdin)?;

    let output = child.wait_with_output()?;
    let s = String::from_utf8(output.stdout)?;
    crate::stat::preprocess::end_clock("spacer-preprocessor");

    if s.starts_with("(error") {
        debug!("{s}");
        Err(Error::Preprocessor("fail".to_string()))
    } else {
        Ok("(set-logic HORN)\n".to_string() + &s)
    }
}

#[test]
fn test_spacer_preprocessor() {
    use tempfile::NamedTempFile;
    let s = "
    (set-logic HORN)
(declare-fun mc91 ( Int Int ) Bool)
(assert (forall ((n Int)) (=> (> n 100) (mc91 n (- n 10)))))
(assert (forall ((n Int) (t Int) (r Int))
    (=>
        (and
            (<= n 100)
            (mc91 (+ n 11) t)
            (mc91 t r)
        )
        (mc91 n r)
    )
))
(assert (forall ((n Int) (r Int))
    (=>
        (and
            (<= n 101)
            (not (= r 91))
            (mc91 n r)
        )
        false
    )
))
(check-sat)
    ";
    println!("before preprocessing: \n{}", s);
    let mut tf = NamedTempFile::new().unwrap();
    tf.write_all(s.as_bytes()).unwrap();

    let s = open_file_with_preprocess(tf.path().to_str().unwrap()).unwrap();
    println!("after preprocessing: \n{}", s);

    assert!(s.starts_with("(set-logic HORN)"));
}
