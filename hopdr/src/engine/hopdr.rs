use std::{hint::unreachable_unchecked, unimplemented};
use super::{Problem, Clause, Goal, VerificationResult};
use super::rtype::Environment;

struct Candidate {
    env: Environment,
    index: u64,
}
struct HoPDR<'a> {
    models: Vec<Candidate>,
    expand_cnt: u64,
    envs: Vec<Environment>,
    problem: &'a Problem,
}

impl<'a> HoPDR<'a> {
    fn new(problem: &'a Problem) -> HoPDR<'a> {
        PDR{models: Vec::new(), expand_cnt: 0, envs: Vec::new(), problem}
    }

    fn check_valid(&self) -> Option<Candidate> {
        unimplemented!()
    }

    fn check_inductive(&self) -> bool {
        unimplemented!()
    }

    fn unfold(&mut self) {
        unimplemented!()
    }

    fn valid(&mut self) -> PDRResult {
        unimplemented!()
    }

    fn candidate(&mut self, c: Candidate) {

    }

    fn check_feasible(&mut self) -> PDRResult {
        unimplemented!()
    }

    fn conflict(&mut self) {

    }

    fn conflict(&mut self) {

    }
    
    

    fn run(&mut self) -> PDRResult {
        loop {
            match self.check_valid() {
                Some(candidate) => {
                    self.candidate(candidate);
                    self.check_feasible();
                },
                None if self.check_inductive() => {return self.valid()}
                None => self.unfold()
            }
        }
    }
}


fn infer(problem: Problem) -> VerificationResult {
    unimplemented!()
}