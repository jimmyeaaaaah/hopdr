extern crate clap;
extern crate hopdr;
extern crate lazy_static;
#[macro_use]
extern crate log;
extern crate ctrlc;

use hopdr::*;

use clap::Parser;
use colored::Colorize;
use hopdr::pdr::PDRConfig;
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
    #[clap(long)]
    no_preprocess: bool,
    #[clap(long)]
    print_stat: bool,
    /// Timeout (sec); if set to 0, no timeout
    #[clap(short, long, default_value_t = 0)]
    timeout: u64,
    #[clap(long)]
    dump_tex_progress: bool,
    #[clap(long)]
    no_inlining: bool,
    #[clap(long)]
    remove_disjunction: bool,
    #[clap(long)]
    smt_interpol: Option<String>,
}

fn pdr_main(contents: String, config: PDRConfig) -> hopdr::pdr::VerificationResult {
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

    pdr::run(vc, config)
}

fn gen_configuration_from_args(args: &Args) -> hopdr::Configuration {
    hopdr::Configuration::new()
        .inlining(!args.no_inlining)
        .remove_disjunction(args.remove_disjunction)
}

fn main() {
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

    // FIXME: adhoc
    match &args.smt_interpol {
        Some(s) => hopdr::solver::interpolation::set_smt_interpol_path(s.clone()),
        None => (),
    }

    let config = gen_configuration_from_args(&args);

    let contents = if args.no_preprocess {
        fs::read_to_string(&args.input).expect("Something went wrong reading the file")
    } else {
        preprocess::hfl_preprocessor::open_file_with_preprocess(&args.input, &config).unwrap()
    };

    let config = pdr::PDRConfig::new().dump_tex_progress(args.dump_tex_progress);

    // RUST_LOG=info (trace, debug, etc..)

    // executes PDR with timeout
    // following https://gist.github.com/junha1/8ebaf53f46ea6fc14ab6797b9939b0f8

    let r = if args.timeout == 0 {
        util::executes_with_timeout_and_ctrlc(move || pdr_main(contents, config), None)
    } else {
        let timeout = time::Duration::from_secs(args.timeout);
        util::executes_with_timeout_and_ctrlc(move || pdr_main(contents, config), Some(timeout))
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
        Err(util::ExecutionError::Ctrlc) => {
            println!("{}", "Execution terminated".white());
        }
    }
    crate::stat::finalize();

    if args.print_stat {
        crate::stat::dump();
    }
}
