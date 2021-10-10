use super::rtype;
use super::rtype::TypeEnvironment;
use super::VerificationResult;
use crate::formula::hes::Problem;
use std::collections::HashMap;
use std::unimplemented;

use super::candidate::Sty as Candidate;

enum PDRResult {
    Valid,
    Invalid,
    Unknown,
}

type NodeID = u64;

struct CandidateTree {
    root: Option<Vec<NodeID>>,
    labels: HashMap<NodeID, Candidate>,
    children: HashMap<NodeID, Vec<NodeID>>,
    current_id: u64,
}

impl CandidateTree {
    fn empty() -> CandidateTree {
        CandidateTree {
            current_id: 0,
            root: None,
            labels: HashMap::new(),
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
                return Some(CandidateNode { id: *key, label: c });
            }
        }
        None
    }

    fn add_new_candidate(&mut self, candidate: Candidate) -> NodeID {
        let id = self.get_new_id();
        self.labels.insert(id, candidate);
        id
    }

    fn add_children(&mut self, node: CandidateNode, candidates: &[Candidate]) {
        if !self.children.contains_key(&node.id) {
            self.children.insert(node.id, Vec::new());
        }
        for c in candidates {
            let node_id = self.add_new_candidate(c.clone());
            self.children.get_mut(&node.id).unwrap().push(node_id);
        }
    }
}

#[derive(Clone, Debug)]
struct CandidateNode {
    id: u64,
    label: Candidate,
}

struct HoPDR<'a> {
    models: CandidateTree,
    envs: Vec<TypeEnvironment>,
    problem: &'a Problem,
}

enum RefuteOrCex<A, B> {
    Refutable(A),
    Cex(B),
}

fn transformer(env: TypeEnvironment) -> TypeEnvironment {
    unimplemented!()
}

impl TypeEnvironment {
    fn new_top_env(problem: &Problem) -> TypeEnvironment {
        let mut new_env = TypeEnvironment::new();
        for c in problem.clauses.iter() {
            new_env.add_top(c.head.id, &c.head.ty)
        }
        new_env
    }

    fn new_bot_env(problem: &Problem) -> TypeEnvironment {
        let mut new_env = TypeEnvironment::new();
        for c in problem.clauses.iter() {
            new_env.add_bot(c.head.id, &c.head.ty)
        }
        new_env
    }
}

impl<'a> HoPDR<'a> {
    fn top_env(&mut self) -> &mut TypeEnvironment {
        self.envs.last_mut().unwrap()
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
        match rtype::type_check_top(&self.problem.top, self.top_env()) {
            Ok(()) => true,
            Err(e) => match e {
                rtype::Error::TypeError => false,
                rtype::Error::SMTTimeout | rtype::Error::SMTUnknown => panic!("smt check fail.."),
            },
        }
    }

    fn check_inductive(&self) -> bool {
        unimplemented!()
    }

    fn initialize(&mut self) {
        self.envs.push(TypeEnvironment::new_top_env(self.problem));
    }

    fn unfold(&mut self) {
        self.envs.push(TypeEnvironment::new_bot_env(self.problem));
    }

    fn valid(&mut self) -> PDRResult {
        dbg!("PDR valid");
        PDRResult::Valid
    }

    fn invalid(&mut self) -> PDRResult {
        dbg!("PDR invalid");
        PDRResult::Invalid
    }

    // generates a candidate
    // Assumption: self.check_valid() == false
    fn candidate(&mut self) {}

    fn is_refutable(&self, _c: &Candidate) -> RefuteOrCex<TypeEnvironment, Vec<Candidate>> {
        unimplemented!()
    }

    fn check_feasible(&mut self) -> bool {
        loop {
            match self.models.get_unprocessed_leaf() {
                Some(c) => match self.is_refutable(&c.label) {
                    RefuteOrCex::Refutable(env) => {
                        self.conflict(c, env);
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

    fn conflict(&mut self, _candidate: CandidateNode, _refute_env: TypeEnvironment) {}

    fn decide(&mut self, parent: CandidateNode, children: Vec<Candidate>) {
        self.models.add_children(parent, &children);
    }

    fn run(&mut self) -> PDRResult {
        loop {
            if !self.check_valid() {
                self.candidate();
                if self.check_feasible() {
                    return self.invalid();
                }
            } else if self.check_inductive() {
                return self.valid();
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
