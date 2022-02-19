use super::fml;
use super::rtype;
use super::rtype::TyEnv;
use super::VerificationResult;
use crate::formula::fofml;
use crate::formula::hes::Problem as ProblemBase;
use crate::formula::{hes, Ident};
use crate::formula::{Constraint, Top};
use crate::solver::smt;
use crate::util::dprintln;
use colored::Colorize;
use std::collections::HashMap;

use std::fmt::Display;
use std::unimplemented;

type Problem = ProblemBase<fofml::Atom>;

pub enum PDRResult {
    Valid,
    Invalid,
}

#[allow(dead_code)]
pub const NOLOG: u64 = 0;
pub const DEBUG: u64 = 1;

type NodeID = usize;

type Candidate = fml::Formula;

pub struct HoPDR {
    models: Vec<Candidate>,
    envs: Vec<TyEnv>,
    problem: Problem,
    loop_cnt: u64,
    verbose: u64,
}

enum RefuteOrCex<A, B> {
    Refutable(A),
    Cex(B),
}

impl TyEnv {
    fn new_top_env(problem: &Problem) -> TyEnv {
        let mut new_env = TyEnv::new();
        for c in problem.clauses.iter() {
            new_env.add_top(c.head.id, &c.head.ty)
        }
        new_env
    }

    fn new_bot_env(problem: &Problem) -> TyEnv {
        let mut new_env = TyEnv::new();
        for c in problem.clauses.iter() {
            new_env.add_bot(c.head.id, &c.head.ty)
        }
        new_env
    }
}

impl HoPDR {
    #[allow(dead_code)]
    fn dump_state(&self) {
        println!("{}", "[PDR STATE]".green().bold());
        println!("- current loop: {}", self.loop_cnt);
        println!("- size of env: {}", self.envs.len());
        //println!("- size of model: {}", self.models.size());
        for (level, e) in self.envs.iter().enumerate() {
            println!("Level {}", level);
            println!("{}", e);
        }
    }
    // generates a candidate
    // Assumption: self.check_valid() == false
    fn is_refutable(&self, candidate_node: &Candidate) -> RefuteOrCex<rtype::Ty, Candidate> {
        debug!("[Candidate] is_refutable");
        // 1. generate constraints: calculate t s.t. c.sty ~ t and check if Env |- formula[c.ident] : t.
        // 2. if not typable, calculate cex
        // 3. if typable, returns the type
        unimplemented!()
        //let candidate = &candidate_node.label;
        //match candidate.sty.is_refutable(
        //    self.get_clause_by_id(&candidate.ident),
        //    &self.envs[candidate_node.level - 1],
        //) {
        //    Ok(t) => RefuteOrCex::Refutable(t),
        //    Err(c) => RefuteOrCex::Cex(c.to_candidates()),
        //}
    }

    fn candidate(&mut self) {
        debug!("{}", "candidate".purple());
        unimplemented!()
    }

    fn get_clause_by_id(&self, id: &Ident) -> &hes::Clause<Constraint> {
        unimplemented!();
        //panic!("no such clause with id = {}", id);
    }

    fn top_env(&self) -> &TyEnv {
        self.envs.last().unwrap()
    }

    fn new(problem: Problem) -> HoPDR {
        let mut hopdr = HoPDR {
            models: Vec::new(),
            envs: Vec::new(),
            problem,
            loop_cnt: 0,
            verbose: 0,
        };
        hopdr.initialize();
        hopdr
    }

    pub fn set_verbosity_level(&mut self, v: u64) {
        self.verbose = v;
    }

    fn check_valid(&mut self) -> bool {
        debug!("check_valid");
        // rtype::type_check_clause(fml, ty.clone(), &mut env);
        // println!("{}:{}\n -> {:?}", fml, ty.clone(), );
        let env = fml::Env::from_type_environment(self.top_env());
        fml::env_models(&env, &self.problem.top)
    }

    fn check_inductive(&self) -> bool {
        unimplemented!()
        //let env = self.top_env();
        //for clause in self.problem.clauses.iter() {
        //    let tys = env.get(&clause.head.id).unwrap();
        //    for ty in tys {
        //        let result = rtype::type_check_clause(clause, ty.clone(), env.into());
        //        if !handle_type_check(result) {
        //            debug!("not inductive");
        //            return false;
        //        }
        //    }
        //}
        //true
    }

    fn initialize(&mut self) {
        println!("{}", "initialize".purple());
        self.envs.push(TyEnv::new_top_env(&self.problem));
    }

    fn unfold(&mut self) {
        println!("{}", "unfold".purple());
        //self.envs.push(TyEnv::new_bot_env(self.problem));
    }

    fn valid(&mut self) -> PDRResult {
        debug!("PDR valid");
        dprintln!(self.verbose, DEBUG, "[PDR]valid");
        PDRResult::Valid
    }

    fn invalid(&mut self) -> PDRResult {
        debug!("PDR invalid");
        dprintln!(self.verbose, DEBUG, "[PDR]invalid");
        unimplemented!();
        PDRResult::Invalid
    }

    fn check_feasible(&mut self) -> bool {
        debug!("[PDR]check feasible");
        unimplemented!()
    }

    fn conflict(&mut self) {
        println!("{}", "conflict".blue());
        //debug!("[PDR]conflict: {} <-> {}", &c.label, &refute_ty);
        unimplemented!()
    }

    fn decide(&mut self) {
        println!("{}", "decide".blue());
        debug!("[PDR]decide");
        unimplemented!()
    }

    fn run(&mut self) -> PDRResult {
        dprintln!(self.verbose, DEBUG, "[PDR] target formula");
        dprintln!(self.verbose, DEBUG, "{}", self.problem);
        loop {
            self.dump_state();
            if !self.check_valid() {
                self.candidate();
                if self.check_feasible() {
                    break self.invalid();
                }
            } else if self.check_inductive() {
                break self.valid();
            } else {
                self.unfold()
            }
            //use std::{thread, time};
            //let asec = time::Duration::from_secs(1);
            //thread::sleep(asec);
        }
    }
}

pub fn infer(problem: ProblemBase<Constraint>) -> VerificationResult {
    let problem = problem.into();
    let mut pdr = HoPDR::new(problem);
    pdr.set_verbosity_level(DEBUG);
    pdr.run();

    unimplemented!()
}
