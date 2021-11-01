use super::candidate::NegEnvironment;
use super::rtype;
use super::rtype::PosEnvironment;
use super::VerificationResult;
use crate::formula::hes::Problem;
use crate::formula::{hes, Ident};
use crate::formula::{Constraint, Top};
use std::collections::HashMap;

use std::unimplemented;

use super::candidate::Sty;
impl NegEnvironment {
    fn to_candidates(self) -> Vec<Candidate> {
        let mut v = Vec::new();
        for (ident, stys) in self.map.into_iter() {
            for sty in stys {
                v.push(Candidate { ident, sty });
            }
        }
        v
    }
}

pub enum PDRResult {
    Valid,
    Invalid,
}

type NodeID = u64;

#[derive(Debug, Clone)]
struct Candidate {
    pub ident: Ident,
    pub sty: Sty,
}

struct CandidateTree {
    root: Option<Vec<NodeID>>,
    labels: HashMap<NodeID, Candidate>,
    levels: HashMap<NodeID, u64>,
    children: HashMap<NodeID, Vec<NodeID>>,
    current_id: u64,
}

impl CandidateTree {
    fn empty() -> CandidateTree {
        CandidateTree {
            current_id: 0,
            root: None,
            labels: HashMap::new(),
            levels: HashMap::new(),
            children: HashMap::new(),
        }
    }

    fn get_new_id(&mut self) -> NodeID {
        let id = self.current_id;
        self.current_id += 1;
        id
    }

    fn is_epsilon(&self) -> bool {
        self.root.is_none()
    }

    fn get_unprocessed_leaf(&self) -> Option<CandidateNode> {
        for (key, _) in self.labels.iter() {
            if !self.children.contains_key(key) {
                let c = self.labels[key].clone();
                let lv = self.levels[key];
                return Some(CandidateNode {
                    id: *key,
                    level: lv,
                    label: c,
                });
            }
        }
        None
    }

    fn add_new_candidate(&mut self, candidate: Candidate) -> NodeID {
        let id = self.get_new_id();
        self.labels.insert(id, candidate);
        id
    }

    pub fn add_root_children(&mut self, candidates: &[Candidate]) {
        assert!(self.is_epsilon());
        let mut v = Vec::new();
        for c in candidates {
            let node_id = self.add_new_candidate(c.clone());
            v.push(node_id);
        }
        self.root = Some(v);
    }

    pub fn add_children(&mut self, node: CandidateNode, candidates: &[Candidate]) {
        self.children.entry(node.id).or_insert_with(Vec::new);
        for c in candidates {
            let node_id = self.add_new_candidate(c.clone());
            self.children.get_mut(&node.id).unwrap().push(node_id);
        }
    }
}

#[derive(Clone, Debug)]
struct CandidateNode {
    level: u64,
    id: u64,
    label: Candidate,
}

struct HoPDR<'a> {
    models: CandidateTree,
    envs: Vec<PosEnvironment>,
    problem: &'a Problem,
}

enum RefuteOrCex<A, B> {
    Refutable(A),
    Cex(B),
}

impl PosEnvironment {
    fn new_top_env(problem: &Problem) -> PosEnvironment {
        let mut new_env = PosEnvironment::new();
        for c in problem.clauses.iter() {
            new_env.add_top(c.head.id, &c.head.ty)
        }
        new_env
    }

    fn new_bot_env(problem: &Problem) -> PosEnvironment {
        let mut new_env = PosEnvironment::new();
        for c in problem.clauses.iter() {
            new_env.add_bot(c.head.id, &c.head.ty)
        }
        new_env
    }
}

fn handle_type_check(result: Result<(), rtype::Error>) -> bool {
    match result {
        Ok(()) => true,
        Err(e) => match e {
            rtype::Error::TypeError => false,
            rtype::Error::SMTTimeout | rtype::Error::SMTUnknown => panic!("smt check fail.."),
        },
    }
}

impl<'a> HoPDR<'a> {
    // generates a candidate
    // Assumption: self.check_valid() == false
    fn is_refutable(&self, candidate: &Candidate) -> RefuteOrCex<rtype::Ty, Vec<Candidate>> {
        // 1. generate constraints: calculate t s.t. c.sty ~ t and check if Env |- formula[c.ident] : t.
        // 2. if not typable, calculate cex
        // 3. if typable, returns the type
        match candidate
            .sty
            .is_refutable(self.get_clause_by_id(&candidate.ident), self.top_env())
        {
            Ok(t) => RefuteOrCex::Refutable(t),
            Err(c) => RefuteOrCex::Cex(c.to_candidates()),
        }
    }

    fn candidate(&mut self) {
        let top_false = Sty::mk_prop_ty(Constraint::mk_true());
        let candidates = match top_false.is_cex_available_top(&self.problem.top, self.top_env()) {
            Some(c) => c.to_candidates(),
            None => panic!("program error"),
        };
        self.models.add_root_children(&candidates);
    }

    fn get_clause_by_id(&'a self, id: &Ident) -> &'a hes::Clause {
        for c in self.problem.clauses.iter() {
            if &c.head.id == id {
                return c;
            }
        }
        panic!("no such clause with id = {}", id);
    }

    fn top_env(&self) -> &PosEnvironment {
        self.envs.last().unwrap()
    }

    fn new(problem: &'a Problem) -> HoPDR<'a> {
        let mut hopdr = HoPDR {
            models: CandidateTree::empty(),
            envs: Vec::new(),
            problem,
        };
        hopdr.initialize();
        hopdr
    }

    fn check_valid(&mut self) -> bool {
        // rtype::type_check_clause(fml, ty.clone(), &mut env);
        // println!("{}:{}\n -> {:?}", fml, ty.clone(), );
        let result = rtype::type_check_top(&self.problem.top, self.top_env().into());
        handle_type_check(result)
    }

    // 1. Γ_i |- Γ_{i-1}
    // 2. Γ_i |- \psi : *<T>
    // Assumption: 2 has been already satisfied
    fn check_inductive(&self) -> bool {
        let env = self.top_env();
        for clause in self.problem.clauses.iter() {
            let tys = env.get(&clause.head.id).unwrap();
            for ty in tys {
                let result = rtype::type_check_clause(clause, ty.clone(), env.into());
                if !handle_type_check(result) {
                    return false;
                }
            }
        }
        true
    }

    fn initialize(&mut self) {
        self.envs.push(PosEnvironment::new_top_env(self.problem));
    }

    fn unfold(&mut self) {
        self.envs.push(PosEnvironment::new_bot_env(self.problem));
    }

    fn valid(&mut self) -> PDRResult {
        dbg!("PDR valid");
        PDRResult::Valid
    }

    fn invalid(&mut self) -> PDRResult {
        dbg!("PDR invalid");
        PDRResult::Invalid
    }

    fn check_feasible(&mut self) -> bool {
        loop {
            match self.models.get_unprocessed_leaf() {
                Some(c) => match self.is_refutable(&c.label) {
                    RefuteOrCex::Refutable(t) => {
                        self.conflict(c, t);
                        if self.models.is_epsilon() {
                            return false;
                        }
                    }
                    RefuteOrCex::Cex(c2) => {
                        self.decide(c, c2);
                    }
                },
                None => return true,
            }
        }
    }

    fn conflict(&mut self, c: CandidateNode, refute_ty: rtype::Ty) {
        for i in 0..c.level {
            self.envs[i as usize].add(c.label.ident, refute_ty.clone());
        }
    }

    fn decide(&mut self, parent: CandidateNode, children: Vec<Candidate>) {
        self.models.add_children(parent, &children);
    }

    fn run(&mut self) -> PDRResult {
        loop {
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
        }
    }
}

pub fn infer(problem: Problem) -> VerificationResult {
    let mut pdr = HoPDR::new(&problem);
    pdr.run();
    unimplemented!()
}
