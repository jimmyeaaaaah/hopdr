use std::process::Command;

use std::io;

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

/// Preprocess the given file and returns the HFLz formula string
///
/// Before open `filename`, `open_file_with_preprocess` executes command `hfl-preprocessor` (github.com/moratorium08/hfl-preprocessor`,
/// which transforms hfls with some heuristics without changing the validity (inlining, removing disjunctions, etc)
/// These functionalities should be implemented in hopdr in the future.
pub fn open_file_with_preprocess(
    filename: &str,
    config: &crate::Configuration,
) -> Result<String, Error> {
    //let contents = fs::read_to_string(&args.input).expect("Something went wrong reading the file");
    const CMD: &str = "hfl-preprocessor";

    let mut args = Vec::new();
    if !config.inlining {
        args.push("--no-inlining");
    }
    if config.remove_disjunction {
        args.push("--remove-disjunction");
    }
    args.push(filename);
    let output = Command::new(CMD).args(args).output()?;
    let s = String::from_utf8(output.stdout)?;
    if s.starts_with("%HES") {
        Ok(s)
    } else {
        Err(Error::Preprocessor(s))
    }
}
