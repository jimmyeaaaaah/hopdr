extern crate clap;
extern crate hopdr;
extern crate lazy_static;
#[macro_use]
extern crate log;
extern crate ctrlc;

use hopdr::*;

use clap::Parser;
use hopdr::checker;
use hopdr::title;
use nom::error::VerboseError;

/// Validity checker for νHFL(Z)
#[derive(Parser, Debug, Clone)]
#[clap(author = "Hiroyuki Katsura", version, about, long_about = None)]
struct Args {
    /// Name of the person to greet
    #[clap(short, long)]
    input: String,
    #[clap(long)]
    no_inlining: bool,
    //#[clap(long)]
    //remove_disjunction: bool,
    #[clap(long)]
    chc: bool,
}

fn gen_configuration_from_args(args: &Args) -> hopdr::Configuration {
    hopdr::Configuration::new()
        .inlining(!args.no_inlining)
        //.remove_disjunction(args.remove_disjunction)
        .remove_disjunction(false)
        .wait_every_step(false)
}
fn get_problem(
    filename: &str,
    config: &hopdr::Configuration,
) -> (
    hopdr::formula::hes::Problem<hopdr::formula::Constraint>,
    hopdr::preprocess::Context,
) {
    let contents =
        preprocess::hfl_preprocessor::open_file_with_preprocess(&filename, &config).unwrap();
    debug!("starting Checker...");
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
    (vc, ctx)
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
    let config = gen_configuration_from_args(&args);

    let (vc, ctx) = if args.chc {
        let data = std::fs::read_to_string(&args.input).unwrap();
        let chcs = parse::parse_chc(&data).unwrap();
        println!("CHCs");
        for chc in chcs.iter() {
            println!("{}", chc);
        }
        (
            crate::formula::chc::translate_to_hes(chcs),
            hopdr::preprocess::Context::empty(),
        )
    } else {
        get_problem(&args.input, &config)
    };

    let config = checker::Config::new(&ctx);

    checker::run(vc, config);
}
