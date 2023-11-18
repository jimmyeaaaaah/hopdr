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
use hopdr::pdr::VerificationResult;
use hopdr::preprocess::Context;
use hopdr::title;
use hopdr::util::Pretty;
use nom::error::VerboseError;

use std::fs;
use std::time;

/// Validity checker for νHFL(Z)
#[derive(Parser, Debug, Clone)]
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
    #[clap(long)]
    detailed_results: bool,
    #[clap(long)]
    debug_wait_every_step: bool,
}

fn report_result(args: &Args, r: VerificationResult, ctx: &Context) {
    match r {
        pdr::VerificationResult::Valid(c) => {
            println!("{}", "Valid".green());
            if args.detailed_results {
                println!("[Type Environment]");
                println!("{}", c.certificate.pretty_display_with_context(ctx));
            }
        }
        pdr::VerificationResult::Invalid => {
            println!("{}", "Invalid".red());
        }
        pdr::VerificationResult::Unknown => {
            println!("{}", "Unknown".red());
        }
    }
}

fn pdr_main(args: Args, contents: String, config: PDRConfig) {
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
    let (vc, ctx) = preprocess::hes::preprocess(f);
    for fml in vc.clauses.iter() {
        debug!("{}", fml);
    }

    report_result(&args, pdr::run(vc, config), &ctx)
}

fn gen_configuration_from_args(args: &Args) -> hopdr::Configuration {
    hopdr::Configuration::new()
        .inlining(!args.no_inlining)
        .remove_disjunction(args.remove_disjunction)
        .wait_every_step(args.debug_wait_every_step)
}

fn main() {
    // setting logs
    env_logger::builder()
        .format_timestamp(None)
        .format_module_path(false)
        .format_level(false)
        .format_indent(None)
        .init();
    // when the output is redirected to somewhere not a terminal, turn off `colored'
    if !atty::is(atty::Stream::Stdout) || !atty::is(atty::Stream::Stderr) {
        colored::control::set_override(false);
        hopdr::util::set_colored(false);
    } else {
        match terminal_size::terminal_size() {
            Some((width, _)) => hopdr::util::set_default_width(width.0 as usize),
            None => (),
        }
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

    let pdr_config = pdr::PDRConfig::new(config).dump_tex_progress(args.dump_tex_progress);

    // RUST_LOG=info (trace, debug, etc..)

    // executes PDR with timeout
    // following https://gist.github.com/junha1/8ebaf53f46ea6fc14ab6797b9939b0f8
    let args_cloned = args.clone(); // FIXME
    let r = if args.timeout == 0 {
        util::executes_with_timeout_and_ctrlc(
            move || pdr_main(args_cloned, contents, pdr_config),
            None,
        )
    } else {
        let timeout = time::Duration::from_secs(args.timeout);
        util::executes_with_timeout_and_ctrlc(
            move || pdr_main(args_cloned, contents, pdr_config),
            Some(timeout),
        )
    };
    match r {
        Ok(()) => (),
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
