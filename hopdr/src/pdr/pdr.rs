use super::fml;
use super::rtype;
use super::rtype::Refinement;
use super::rtype::Tau;
use super::rtype::TyEnv;
use super::rtype::TypeEnvironment;
use super::VerificationResult;
use crate::formula::fofml;
use crate::formula::hes::Problem;
use crate::formula::Constraint;
use crate::formula::{hes, Ident};

use crate::util::dprintln;
use colored::Colorize;

use std::unimplemented;

pub enum PDRResult {
    Valid,
    Invalid,
}

#[allow(dead_code)]
pub const NOLOG: u64 = 0;
pub const DEBUG: u64 = 1;

type Candidate = hes::Goal<Constraint>;

#[allow(dead_code)]
pub struct HoPDR {
    models: Vec<Candidate>,
    envs: Vec<TyEnv>,
    problem: Problem<Constraint>,
    problem_atom_cache: Problem<fofml::Atom>,
    loop_cnt: u64,
    verbose: u64,
}

#[allow(dead_code)]
enum RefuteOrCex<A, B> {
    Refutable(A),
    Cex(B),
}

impl<C: Refinement> TypeEnvironment<Tau<C>> {
    fn new_top_env(problem: &Problem<C>) -> TypeEnvironment<Tau<C>> {
        let mut new_env = TypeEnvironment::new();
        for c in problem.clauses.iter() {
            new_env.add_top(c.head.id, &c.head.ty)
        }
        new_env
    }

    #[allow(dead_code)]
    fn new_bot_env(problem: &Problem<C>) -> TypeEnvironment<Tau<C>> {
        let mut new_env = TypeEnvironment::new();
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
    #[allow(dead_code)]
    fn is_refutable(&self, _candidate_node: &Candidate) -> RefuteOrCex<rtype::Ty, Candidate> {
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
        let cnf = self.problem.top.to_cnf();
        let env = fml::Env::from_type_environment(self.top_env());
        for x in cnf {
            if !fml::env_models(&env, &x) {
                debug!("candidate: {}", x);
                self.models.push(x);
            }
        }
        panic!("program error")
    }

    #[allow(dead_code)]
    fn get_clause_by_id(&self, _id: &Ident) -> &hes::Clause<Constraint> {
        unimplemented!();
        //panic!("no such clause with id = {}", id);
    }

    fn top_env(&self) -> &TyEnv {
        self.envs.last().unwrap()
    }

    fn new(problem: Problem<Constraint>) -> HoPDR {
        let problem_atom_cache = problem.clone().into();
        let mut hopdr = HoPDR {
            models: Vec::new(),
            envs: Vec::new(),
            problem_atom_cache,
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
        debug!("check_inductive");
        fml::check_inductive(self.top_env(), &self.problem)
    }

    fn initialize(&mut self) {
        println!("{}", "initialize".purple());
        self.envs.push(TyEnv::new_top_env(&self.problem));
    }

    fn unfold(&mut self) {
        println!("{}", "unfold".purple());
        self.envs.push(TyEnv::new_bot_env(&self.problem));
    }

    fn valid(&mut self) -> PDRResult {
        debug!("PDR valid");
        dprintln!(self.verbose, DEBUG, "[PDR]valid");
        PDRResult::Valid
    }

    fn invalid(&mut self) -> PDRResult {
        debug!("PDR invalid");
        dprintln!(self.verbose, DEBUG, "[PDR]invalid");
        PDRResult::Invalid
    }

    fn check_feasible(&mut self) -> bool {
        debug!("[PDR]check feasible");
        loop {
            if self.models.len() == self.envs.len() {
                // the trace of cex is feasible
                return true;
            }
            let cand = match self.models.last() {
                Some(c) => c.clone(),
                None => {
                    // all the candidates have been refuted
                    return false;
                }
            };
            //
            assert!(self.envs.len() > self.models.len() + 1);
            let level = self.envs.len() - self.models.len() - 1;
            let env_i_ty = &self.envs[level];
            // ⌊Γ⌋
            let env_i = fml::Env::from_type_environment(env_i_ty);
            // ℱ(⌊Γ⌋)
            let f_env_i = self.problem.transform(&env_i);
            if fml::env_models(&f_env_i, &cand) {
                self.conflict();
            } else {
                self.decide();
            }
        }
    }

    #[allow(dead_code)]
    // Assumption: ℱ(⌊Γ⌋) ⊧ ψ
    fn conflict(&mut self) {
        println!("{}", "conflict".blue());
        //debug!("[PDR]conflict: {} <-> {}", &c.label, &refute_ty);
        unimplemented!()
    }

    #[allow(dead_code)]
    // Assumption: ℱ(⌊Γ⌋) not⊧ ψ
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

pub fn infer(problem: Problem<Constraint>) -> VerificationResult {
    let mut pdr = HoPDR::new(problem);
    pdr.set_verbosity_level(DEBUG);
    pdr.run();

    unimplemented!()
}
