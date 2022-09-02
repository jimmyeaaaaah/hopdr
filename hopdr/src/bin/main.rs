extern crate clap;
extern crate hopdr;
extern crate lazy_static;
#[macro_use]
extern crate log;

use hopdr::*;

use clap::Parser;
use colored::Colorize;
use hopdr::title;
use nom::error::VerboseError;

use std::fs;
use std::time;

/// Validity checker for νHFL(Z)
#[derive(Parser, Debug)]
#[clap(author = "Hiroyuki Katsura", version, about, long_about = None)]
struct Args {
    /// Name of the person to greet
    #[clap(short, long)]
    input: String,
    #[clap(short, long)]
    no_preprocess: bool,
    #[clap(short, long)]
    print_stat: bool,
    /// Timeout (sec); if set to 0, no timeout
    #[clap(short, long, default_value_t = 0)]
    timeout: u64,
}

fn pdr_main(contents: String) -> hopdr::pdr::VerificationResult {
    debug!("starting PDR...");
    let (_, f) = parse::parse::<VerboseError<&str>>(&contents).unwrap();

    title!("problem");
    match &f {
        parse::Problem::NuHFLZValidityChecking(vc) => {
            for fml in vc.formulas.iter() {
                debug!("{}", fml);
            }
            debug!("TOP={}", vc.toplevel);
        }
    }

    title!("proprocessed");
    let (vc, _ctx) = preprocess::hes::preprocess(f);
    for fml in vc.clauses.iter() {
        debug!("{}", fml);
    }

    pdr::run(vc)
}

fn main() {
    let solver_total_time = std::time::Instant::now();
    // setting logs
    env_logger::builder()
        .format_timestamp(None)
        .format_module_path(false)
        .format_level(false)
        .init();
    // when the output is redirected to somewhere not a terminal, turn off `colored'
    if !atty::is(atty::Stream::Stdout) || !atty::is(atty::Stream::Stderr) {
        colored::control::set_override(false);
    }

    // parsing command line args
    let args = Args::parse();

    let contents = if args.no_preprocess || true {
        fs::read_to_string(&args.input).expect("Something went wrong reading the file")
    } else {
        preprocess::hfl_preprocessor::open_file_with_preprocess(&args.input).unwrap()
    };

    // RUST_LOG=info (trace, debug, etc..)

    // executes PDR with timeout
    // following https://gist.github.com/junha1/8ebaf53f46ea6fc14ab6797b9939b0f8

    let r = if args.timeout == 0 {
        Ok(pdr_main(contents))
    } else {
        let timeout = time::Duration::from_secs(args.timeout);
        util::executes_with_timeout(move || pdr_main(contents), timeout)
    };
    match r {
        Ok(pdr::VerificationResult::Valid) => {
            println!("{}", "Valid".green());
        }
        Ok(pdr::VerificationResult::Invalid) => {
            println!("{}", "Invalid".red());
        }
        Ok(pdr::VerificationResult::Unknown) => {
            println!("{}", "Unknown".red());
        }
        Err(util::ExecutionError::Timeout) => {
            println!("{}", "Timeout".red());
        }
        Err(util::ExecutionError::Panic) => {
            println!("{}", "Fail".red());
        }
    }
    crate::stat::overall::register_total_time(solver_total_time.elapsed());

    if args.print_stat {
        crate::stat::dump();
    }
}
