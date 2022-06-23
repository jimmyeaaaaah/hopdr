use super::rtype;
use super::rtype::{Refinement, Tau, TyEnv, TypeEnvironment};
use super::VerificationResult;
use crate::formula::hes::Problem;
use crate::formula::{fofml, hes, Constraint, Top};
use crate::pdr::derivation;

use colored::Colorize;

use std::fmt;

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
        debug!("{}", "[PDR STATE]".green().bold());
        debug!("- current loop: {}", self.loop_cnt);
        debug!("- size of env: {}", self.envs.len());
        //println!("- size of model: {}", self.models.size());
        for (level, e) in self.envs.iter().enumerate() {
            debug!("Level {}", level);
            debug!("{}", e);
        }
    }

    fn candidate(&mut self) {
        info!("{}", "candidate".purple());
        let cnf = self.problem.top.to_cnf();
        let tyenv = self.top_env();
        for x in cnf {
            if !rtype::type_check_top(tyenv, &x) {
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
        let tyenv = self.top_env();
        rtype::type_check_top(tyenv, &self.problem.top)
    }

    fn check_inductive(&self) -> bool {
        debug!("check_inductive");
        let tyenv = self.top_env();
        for clause in self.problem.clauses.iter() {
            let tys = tyenv.get(&clause.head.id).unwrap().iter();
            for ty in tys {
                if !rtype::type_check_goal(tyenv, &clause.body, &ty) {
                    return false;
                }
            }
        }
        true
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
            debug!("model size: {}", self.models.len());
            debug!("env size: {}", self.envs.len());
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
            let mut tyenv_i = self.get_current_target_approx().into();
            match derivation::search_for_type(&cand, &self.problem, &mut tyenv_i) {
                Some(tyenv) => self.conflict(tyenv)?,
                None => {
                    self.decide();
                }
            }
            panic!("uo")
        }
    }

    // Assumption 1: self.models.len() > 0
    // Assumption 2: ℱ(⌊Γ⌋) ⊧ ψ
    // Assumption 3: self.get_current_cex_level() < N
    fn conflict(&mut self, tyenv_new: TypeEnvironment<Tau<Constraint>>) -> Result<(), Error> {
        debug!("{}", "conflict".blue());
        debug!("{}", tyenv_new);
        // refute the top model in self.models.
        self.models.pop().unwrap();
        // conjoin
        for i in 0..(self.get_current_cex_level() + 1) {
            self.envs[i].append(&tyenv_new);
        }
        Ok(())
    }

    // Assumption: ℱ(⌊Γ⌋) not⊧ ψ
    fn decide(&mut self) {
        debug!("{}", "decide".blue());
        debug!("[PDR]decide");
        let level = self.get_current_cex_level();
        let gamma_i = &self.envs[level];
        let cex = self.models.last().unwrap().clone();
        let cex_next = self.problem.eval(&cex);
        debug!("cex: {}", cex);
        debug!("cex_next: {}", cex_next);
        let cex_next = cex_next.reduce_goal();
        debug!("cex_next reduced: {}", cex_next);
        let cnf = cex_next.to_cnf();
        debug!("{}", gamma_i);
        let tyenv = gamma_i;
        for x in cnf {
            if !rtype::type_check_top(tyenv, &x) {
                debug!("candidate: {}", x);
                self.models.push(x);
                return;
            }
        }
        panic!("decide: fail. Assumption ℱ(⌊Γ⌋) not⊧ ψ is not satisfied")
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
