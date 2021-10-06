use super::rtype::Environment;
use super::rtype;
use super::VerificationResult;
use crate::formula::hes::Problem;
use std::unimplemented;


enum PDRResult {
    Valid,
    Invalid,
    Unknown,
}

struct Candidate {
    env: Environment,
    index: u64,
}

struct HoPDR<'a> {
    models: Vec<Candidate>,
    envs: Vec<Environment>,
    problem: &'a Problem,
}

enum RefuteOrCex<A, B> {
    Refutable(A),
    Cex(B),
}

fn transformer(env: Environment) -> Environment {
    unimplemented!()
}

impl Environment { 
    fn new_top_env(problem: &Problem) -> Environment {
        let mut new_env = Environment::new();
        for c in problem.clauses.iter() {
            new_env.add_top(c.head.id, &c.head.ty)
        }
        new_env
    }

    fn new_bot_env(problem: &Problem) -> Environment {
        let mut new_env = Environment::new();
        for c in problem.clauses.iter() {
            new_env.add_bot(c.head.id, &c.head.ty)
        }
        new_env
    }
}

impl<'a> HoPDR<'a> {
    fn top_env(&self) -> &Environment {
        &self.envs.last().unwrap()
    }

    fn new(problem: &'a Problem) -> HoPDR<'a> {
        let mut hopdr = HoPDR {
            models: Vec::new(),
            envs: Vec::new(),
            problem,
        };
        hopdr.initialize();
        hopdr
    }

    fn check_valid(&self) -> bool {
        // rtype::type_check_clause(fml, ty.clone(), &mut env);
        // println!("{}:{}\n -> {:?}", fml, ty.clone(), );
        match rtype::type_check_top(&self.problem.top, self.top_env()) {
            Ok(()) => true,
            Err(e) => match e {
                rtype::Error::TypeError => false,
                rtype::Error::SMTTimeout | rtype::Error::SMTUnknown => panic!("smt check fail.."),
            }
        }

    }

    fn check_inductive(&self) -> bool {
        unimplemented!()
    }

    fn initialize(&mut self) {
        self.envs.push(Environment::new_top_env(self.problem));
    }

    fn unfold(&mut self) {
        self.envs.push(Environment::new_bot_env(self.problem));
    }

    fn valid(&mut self) -> PDRResult {
        unimplemented!()
    }

    // generates a candidate 
    // Assumption: self.check_valid() == false
    fn candidate(&mut self) {

    }

    fn is_refutable(&self, _c: &Candidate) -> RefuteOrCex<Environment, Candidate> {
        unimplemented!()
    }

    fn check_feasible(&mut self) -> PDRResult {
        loop {
            match self.models.pop() {
                Some(c) => match self.is_refutable(&c) {
                    RefuteOrCex::Refutable(env) => {
                        self.conflict(c, env);
                    }
                    RefuteOrCex::Cex(c2) => {
                        self.models.push(c);
                        self.decide(c2);
                    }
                },
                None => return PDRResult::Unknown,
            }
        }
    }

    fn conflict(&mut self, _candidate: Candidate, _refute_env: Environment) {}

    fn decide(&mut self, candidate: Candidate) {
        self.models.push(candidate);
    }

    fn run(&mut self) -> PDRResult {
        loop {
            if self.check_valid() {
                self.candidate();
                self.check_feasible();
            } else if self.check_inductive() {
                return self.valid()
            } else {
                self.unfold()
            }
        }
    }
}

pub fn infer(problem: Problem) -> VerificationResult {
    let mut pdr = HoPDR::new(&problem);
    pdr.run();
    unimplemented!()
}
