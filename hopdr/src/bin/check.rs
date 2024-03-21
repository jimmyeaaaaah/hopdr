extern crate clap;
extern crate hopdr;
extern crate lazy_static;
#[macro_use]
extern crate log;
extern crate ctrlc;

use hopdr::util::Pretty;
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
    #[clap(long)]
    do_format: bool,
    #[clap(long)]
    print_check_log: bool,
    #[clap(long)]
    /// Interpret the input CHC problems is defined by least fixpoint
    chc_least: bool,
}

fn gen_configuration_from_args(args: &Args) -> hopdr::Configuration {
    hopdr::Configuration::new()
        .inlining(!args.no_inlining)
        //.remove_disjunction(args.remove_disjunction)
        .remove_disjunction(false)
        .wait_every_step(false)
}

fn get_preprocess_config() -> hopdr::preprocess::hes::Config {
    hopdr::preprocess::hes::Config::checker_default()
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
    let (vc, ctx) = preprocess::hes::preprocess(f, &get_preprocess_config());
    for fml in vc.clauses.iter() {
        debug!("{}", fml);
    }
    (vc, ctx)
}

fn report_result(result: checker::ExecResult) {
    print!("Verification Result: ");
    match result {
        checker::ExecResult::Unknown => println!("Unknown"),
        checker::ExecResult::Invalid => println!("Invalid"),
        checker::ExecResult::Fail(s) => println!("Fail\nReason: {s}"),
    }
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

    crate::ml::set_format(args.do_format);

    let config = gen_configuration_from_args(&args);

    let (vc, ctx) = if args.chc {
        let data = std::fs::read_to_string(&args.input).unwrap();
        if args.print_check_log {
            println!("data");
            println!("{data}");
        }
        let (chcs, vmap) = match parse::parse_chc(&data) {
            Ok(x) => x,
            Err(r) if r.is_unsat() => return report_result(checker::ExecResult::Invalid),
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

        //let chcs = crate::formula::chc::expand_ite(chcs);
        //println!("translated:");
        //for chc in chcs.iter() {
        //    println!("{}", chc);
        //}
        let config = get_preprocess_config();
        let problem = if !args.chc_least
            && crate::formula::chc::is_linear(chcs.iter().map(|echc| &echc.chc))
        {
            let greatest = crate::formula::chc::translate_to_hes_linear(chcs.clone());
            let greatest = crate::preprocess::hes::preprocess_for_typed_problem(greatest, &config);

            let least = crate::formula::chc::translate_to_hes(chcs);
            let least = crate::preprocess::hes::preprocess_for_typed_problem(least, &config);

            println!("greatest style:\n {}", greatest);
            println!("least style:\n {}", least);

            let lhs = crate::checker::difficulty_score(&greatest);
            let rhs = crate::checker::difficulty_score(&least);
            if args.print_check_log {
                println!("difficulty score: {} vs {}", lhs, rhs);
            }
            if lhs <= rhs {
                greatest
            } else {
                least
            }
        } else {
            let problem = crate::formula::chc::translate_to_hes(chcs);
            crate::preprocess::hes::preprocess_for_typed_problem(problem, &config)
        };

        (problem, ctx)
    } else {
        get_problem(&args.input, &config)
    };

    let config = checker::Config::new(&ctx, args.print_check_log);

    report_result(checker::run(vc, config))
}
