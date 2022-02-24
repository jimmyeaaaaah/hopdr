use super::fml;
use super::rtype::{Refinement, Tau, TyEnv, TypeEnvironment};
use super::VerificationResult;
use crate::formula::hes::Problem;
use crate::formula::{fofml, hes, Constraint};
use crate::pdr::infer;

use colored::Colorize;

use std::fmt;
use std::unimplemented;

#[derive(Debug, Copy, Clone)]
pub enum Error {
    TypeInference,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::TypeInference => write!(f, "Type Inference from cex failed"),
        }
    }
}

pub enum PDRResult {
    Valid,
    Invalid,
}

type Candidate = hes::Goal<Constraint>;

#[allow(dead_code)]
pub struct HoPDR {
    models: Vec<Candidate>,
    envs: Vec<TyEnv>,
    problem: Problem<Constraint>,
    problem_atom_cache: Problem<fofml::Atom>,
    loop_cnt: u64,
}

impl<C: Refinement> TypeEnvironment<Tau<C>> {
    fn new_top_env(problem: &Problem<C>) -> TypeEnvironment<Tau<C>> {
        let mut new_env = TypeEnvironment::new();
        for c in problem.clauses.iter() {
            new_env.add_top(c.head.id, &c.head.ty)
        }
        new_env
    }

    fn new_bot_env(problem: &Problem<C>) -> TypeEnvironment<Tau<C>> {
        let mut new_env = TypeEnvironment::new();
        for c in problem.clauses.iter() {
            new_env.add_bot(c.head.id, &c.head.ty)
        }
        new_env
    }
}

impl HoPDR {
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

    fn candidate(&mut self) {
        info!("{}", "candidate".purple());
        let cnf = self.problem.top.to_cnf();
        let env = fml::Env::from_type_environment(self.top_env());
        for x in cnf {
            if !fml::env_models(&env, &x) {
                debug!("candidate: {}", x);
                self.models.push(x);
                return;
            }
        }
        panic!("program error")
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
        };
        hopdr.initialize();
        hopdr
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
        info!("{}", "initialize".purple());
        self.envs.push(TyEnv::new_top_env(&self.problem));
    }

    fn unfold(&mut self) {
        info!("{}", "unfold".purple());
        self.envs.push(TyEnv::new_bot_env(&self.problem));
    }

    fn valid(&mut self) -> PDRResult {
        info!("PDR valid");
        PDRResult::Valid
    }

    fn invalid(&mut self) -> PDRResult {
        debug!("PDR invalid");
        PDRResult::Invalid
    }

    fn get_current_cex_level(&self) -> usize {
        assert!(self.envs.len() >= self.models.len() + 1);
        self.envs.len() - self.models.len() - 1
    }

    fn get_current_target_approx<'a>(&'a self) -> &'a TyEnv {
        let level = self.get_current_cex_level();
        &self.envs[level]
    }

    fn check_feasible(&mut self) -> Result<bool, Error> {
        debug!("[PDR]check feasible");
        loop {
            if self.models.len() == self.envs.len() {
                // the trace of cex is feasible
                return Ok(true);
            }
            let cand = match self.models.last() {
                Some(c) => c.clone(),
                None => {
                    // all the candidates have been refuted
                    return Ok(false);
                }
            };
            let env_i_ty = self.get_current_target_approx();
            // ⌊Γ⌋
            let env_i = fml::Env::from_type_environment(env_i_ty);
            // ℱ(⌊Γ⌋)
            let f_env_i = self.problem.transform(&env_i);
            if fml::env_models(&f_env_i, &cand) {
                self.conflict()?;
            } else {
                self.decide();
            }
        }
    }

    // Assumption 1: self.models.len() > 0
    // Assumption 2: ℱ(⌊Γ⌋) ⊧ ψ
    // Assumption 3: self.get_current_cex_level() < N
    fn conflict(&mut self) -> Result<(), Error> {
        debug!("{}", "conflict".blue());
        //debug!("[PDR]conflict: {} <-> {}", &c.label, &refute_ty);
        let level = self.get_current_cex_level();
        let env_i = (&self.envs[level]).into();
        let env_i1 = (&self.envs[level + 1]).into();
        match infer::infer(
            &self.problem_atom_cache,
            &env_i,
            &env_i1,
            &self.models.last().unwrap().clone().into(),
        ) {
            Some(tyenv_new) => {
                // conjoin
                for i in 0..(self.get_current_cex_level() + 1) {
                    self.envs[i].append(&tyenv_new);
                }
                Ok(())
            }
            None => Err(Error::TypeInference),
        }
    }

    // Assumption: ℱ(⌊Γ⌋) not⊧ ψ
    fn decide(&mut self) {
        debug!("{}", "decide".blue());
        debug!("[PDR]decide");

        unimplemented!()
    }

    fn run(&mut self) -> Result<PDRResult, Error> {
        info!("[PDR] target formula");
        info!("{}", self.problem);
        loop {
            self.dump_state();
            if !self.check_valid() {
                self.candidate();
                if self.check_feasible()? {
                    break Ok(self.invalid());
                }
            } else if self.check_inductive() {
                break Ok(self.valid());
            } else {
                self.unfold()
            }
            //use std::{thread, time};
            //let asec = time::Duration::from_secs(1);
            //thread::sleep(asec);
        }
    }
}

pub fn run(problem: Problem<Constraint>) -> VerificationResult {
    let mut pdr = HoPDR::new(problem);
    match pdr.run() {
        Ok(PDRResult::Valid) => VerificationResult::Valid,
        Ok(PDRResult::Invalid) => VerificationResult::Invalid,
        Err(x) => {
            warn!("{}", "Failed to complete PDR".red());
            warn!("Reason: {}", x);
            VerificationResult::Unknown
        }
    }
}
