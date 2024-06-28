extern crate clap;
extern crate hopdr;
extern crate lazy_static;
#[macro_use]
extern crate log;
extern crate ctrlc;

use crate::formula::hes;
use hopdr::util::Pretty;
use hopdr::*;

use clap::Parser;
use colored::Colorize;
use nom::error::VerboseError;
use std::fs;
use tokio::runtime;
use tokio::task::JoinSet;

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
    #[clap(long)]
    do_format: bool,
    #[clap(long)]
    print_check_log: bool,
    #[clap(long)]
    /// Interpret the input CHC problems is defined by least fixpoint
    chc_least: bool,
    /// Don't use Ultimate as a preprocess
    no_ultimate: bool,
    #[cfg(feature = "stat")]
    #[clap(long)]
    print_stat: bool,

    #[clap(long)]
    /// Enables HoIce's preprocessing after spacer's preprocessing
    do_hoice_preprocess: bool,
    #[clap(long)]
    no_mode_analysis: bool,
    #[clap(long)]
    /// Enables tracing. Note that this option may slow down the procedure.
    trace: bool,
}

fn gen_configuration_from_args(args: &Args) -> hopdr::Configuration {
    let cfg = hopdr::Configuration::new()
        .inlining(!args.no_inlining)
        //.remove_disjunction(args.remove_disjunction)
        .remove_disjunction(false)
        .wait_every_step(false)
        .ultimate(!args.no_ultimate);
    if args.trace {
        cfg.trace(true).inlining(false)
    } else {
        cfg
    }
}

fn get_preprocess_config() -> hopdr::preprocess::hes::Config {
    hopdr::preprocess::hes::Config::checker_default()
}

fn get_tracing_config() -> hopdr::preprocess::hes::Config {
    hopdr::preprocess::hes::Config::checker_with_trace_default()
}

fn generate_context_for_chc(vmap: &crate::util::info::VariableMap) -> hopdr::preprocess::Context {
    let mut ctx = hopdr::preprocess::Context::empty();
    for (k, v) in vmap.iter() {
        ctx.ident_map.insert(v.name.clone(), k.clone());
        ctx.inverse_map.insert(*k, v.name.clone());
    }
    ctx
}

fn get_problem(
    filename: &str,
    config: &hopdr::Configuration,
) -> (
    hopdr::formula::hes::Problem<hopdr::formula::Constraint>,
    hopdr::preprocess::Context,
) {
    let contents = if config.trace {
        fs::read_to_string(filename).expect("input file not found")
    } else {
        preprocess::hfl_preprocessor::open_file_with_preprocess(&filename, &config).unwrap()
    };
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
    let conf = if config.trace {
        get_tracing_config()
    } else {
        get_preprocess_config()
    };
    let (vc, ctx) = preprocess::hes::preprocess(f, &conf);
    for fml in vc.clauses.iter() {
        debug!("{}", fml);
    }
    (vc, ctx)
}

fn report_result(result: checker::ExecResult) {
    print!("Verification Result: ");
    match result {
        checker::ExecResult::Unknown => println!("Unknown"),
        checker::ExecResult::Invalid(s) => {
            println!("Invalid");
            match s {
                Some(s) => println!("Trace: {s}"),
                None => (),
            }
        }
        checker::ExecResult::Fail(s) => println!("Fail\nReason: {s}"),
    }
}

#[cfg(not(feature = "stat"))]
fn run_multiple(
    problems: Vec<(
        hes::Problem<crate::formula::Constraint>,
        crate::preprocess::Context,
    )>,
    print_check_log: bool,
    no_mode_analysis: bool,
    track_trace: bool,
) -> checker::ExecResult {
    info!("run parallel");
    let rt = runtime::Runtime::new().unwrap();
    rt.block_on(async {
        let mut set = JoinSet::new();

        for (problem, ctx) in problems {
            let config = checker::Config::new(&ctx, print_check_log, no_mode_analysis, track_trace);
            let t = checker::run(problem, config.clone());
            set.spawn(t);
        }

        while let Some(res) = set.join_next().await {
            match res {
                Ok(checker::ExecResult::Invalid(s)) => {
                    return checker::ExecResult::Invalid(s);
                }
                Ok(checker::ExecResult::Unknown) => {
                    info!("result: unknown");
                }
                Ok(checker::ExecResult::Fail(s)) => {
                    return checker::ExecResult::Fail(s);
                }
                Err(e) => {
                    warn!("join error: {e}");
                }
            }
        }
        checker::ExecResult::Unknown
    })
}

#[cfg(feature = "stat")]
fn run_multiple(
    problems: Vec<(
        hes::Problem<crate::formula::Constraint>,
        crate::preprocess::Context,
    )>,
    print_check_log: bool,
    no_mode_analysis: bool,
    track_trace: bool,
) -> checker::ExecResult {
    info!("run sequentially");
    let rt = runtime::Runtime::new().unwrap();
    rt.block_on(async {
        for (problem, ctx) in problems {
            let config = checker::Config::new(&ctx, print_check_log, no_mode_analysis, track_trace);
            let t = checker::run(problem, config.clone()).await;
            match t {
                checker::ExecResult::Invalid => {
                    return checker::ExecResult::Invalid;
                }
                checker::ExecResult::Unknown => {
                    info!("result: unknown");
                }
                checker::ExecResult::Fail(s) => {
                    return checker::ExecResult::Fail(s);
                }
            }
        }
        checker::ExecResult::Unknown
    })
}

fn handle_chc_data(
    problems: &mut Vec<(
        hes::Problem<crate::formula::Constraint>,
        crate::preprocess::Context,
    )>,
    data: &str,
    do_hoice_preprocess: bool,
    args: &Args,
) {
    let (chcs, vmap) = match parse::parse_chc(&data, do_hoice_preprocess) {
        Ok(x) => x,
        Err(r) if r.is_unsat() => return report_result(checker::ExecResult::Invalid(None)),
        Err(r) => panic!("parse error: {:?}", r),
    };
    let ctx = generate_context_for_chc(&vmap);
    if args.print_check_log {
        println!("CHCs");
        println!(
            "linearity check {}",
            crate::formula::chc::nonliniality(chcs.iter().map(|echc| &echc.chc))
        );
        for echc in chcs.iter() {
            println!("{}", echc.chc.pretty_display_with_context(&ctx));
        }
    }

    let mut config = get_preprocess_config();

    // currently, the size measure is soooo heuristic.
    let is_huge = data.len() > 100000;

    if is_huge {
        config = config.lightweight_find_ite(true)
    }

    if !args.chc_least && crate::formula::chc::is_linear(chcs.iter().map(|echc| &echc.chc)) {
        stat::preprocess::start_clock("translate_to_hes_linear");
        let greatest = crate::formula::chc::translate_to_hes_linear(chcs.clone());
        stat::preprocess::end_clock("translate_to_hes_linear");

        let greatest = crate::preprocess::hes::preprocess_for_typed_problem(greatest, &config);

        stat::preprocess::start_clock("translate_to_hes");
        let least = crate::formula::chc::translate_to_hes(chcs);
        stat::preprocess::end_clock("translate_to_hes");

        let least = crate::preprocess::hes::preprocess_for_typed_problem(least, &config);

        if args.print_check_log {
            println!("greatest style:\n {}", greatest);
            println!("least style:\n {}", least);
        }

        let lhs = crate::checker::difficulty_score(&greatest);
        let rhs = crate::checker::difficulty_score(&least);
        if args.print_check_log {
            println!("difficulty score: {} vs {}", lhs, rhs);
        }
        if lhs < rhs {
            problems.push((greatest, ctx.clone()));
            problems.push((least, ctx.clone()));
        } else {
            problems.push((least, ctx.clone()));
            problems.push((greatest, ctx.clone()));
        }
    } else {
        stat::preprocess::start_clock("translate_to_hes");
        let problem = crate::formula::chc::translate_to_hes(chcs);
        stat::preprocess::end_clock("translate_to_hes");

        let t = crate::preprocess::hes::preprocess_for_typed_problem(problem, &config);
        problems.push((t, ctx.clone()));
    };
}
fn check_main(args: Args) {
    let config = gen_configuration_from_args(&args);

    let vcs = if args.chc {
        let data = preprocess::chc::open_file_with_preprocess(&args.input).unwrap();
        if args.print_check_log {
            println!("data");
            println!("{data}");
        }
        let mut do_hoice_preprocess_or_not = vec![false];
        if args.do_hoice_preprocess {
            do_hoice_preprocess_or_not.push(true);
        }
        let mut vcs = Vec::new();
        for do_hoice_preprocess in do_hoice_preprocess_or_not {
            handle_chc_data(&mut vcs, &data, do_hoice_preprocess, &args);
        }
        vcs
    } else {
        let (problem, ctx) = get_problem(&args.input, &config);
        vec![(problem, ctx)]
    };

    report_result(run_multiple(
        vcs,
        args.print_check_log,
        args.no_mode_analysis,
        args.trace,
    ))
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
    let args_cloned = args.clone();

    crate::ml::set_format(args.do_format);

    match util::executes_with_timeout_and_ctrlc(move || check_main(args_cloned), None) {
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

    #[cfg(feature = "stat")]
    if args.print_stat {
        crate::stat::dump();
    }
}
