use super::candidate::NegEnvironment;
use super::rtype;
use super::VerificationResult;
use crate::formula::hes::Problem;
use crate::formula::{hes, Ident};
use crate::formula::{Constraint, Top};
use crate::util::dprintln;
use colored::Colorize;
use std::collections::HashMap;

use std::fmt::Display;
use std::unimplemented;

pub enum PDRResult {
    Valid,
    Invalid,
}

#[allow(dead_code)]
pub const NOLOG: u64 = 0;
pub const DEBUG: u64 = 1;

type NodeID = usize;

impl Display for Candidate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", &self.ident, &self.sty)
    }
}

struct CandidateTree {
    root: Option<Vec<NodeID>>,
    labels: HashMap<NodeID, Candidate>,
    levels: HashMap<NodeID, usize>,
    parents: HashMap<NodeID, Option<NodeID>>,
    children: HashMap<NodeID, Vec<NodeID>>,
    current_id: usize,
}

impl CandidateTree {
    fn empty() -> CandidateTree {
        CandidateTree {
            current_id: 0,
            root: None,
            labels: HashMap::new(),
            levels: HashMap::new(),
            children: HashMap::new(),
            parents: HashMap::new(),
        }
    }

    fn size(&self) -> usize {
        self.labels.len()
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
            if !self.children.contains_key(key) && self.levels[key] > 0 {
                let c = self.labels[key].clone();
                let lv = self.levels[key];
                println!("level: {}", lv);
                //println!("label: {}", c);
                return Some(CandidateNode {
                    id: *key,
                    level: lv,
                    label: c,
                });
            }
        }
        None
    }

    fn add_new_candidate(&mut self, candidate: Candidate, level: usize) -> NodeID {
        let id = self.get_new_id();
        self.labels.insert(id, candidate);
        self.levels.insert(id, level);
        id
    }

    pub fn add_root_children(&mut self, candidates: &[Candidate], maximum_level: usize) {
        assert!(self.is_epsilon());
        debug!("add_root_children");
        //for c in candidates {
        //    println!("- {}", c);
        //}
        let mut v = Vec::new();
        for c in candidates {
            let node_id = self.add_new_candidate(c.clone(), maximum_level);
            v.push(node_id);
            self.parents.insert(node_id, None);
        }
        self.root = Some(v);
    }

    pub fn add_children(&mut self, node: CandidateNode, candidates: &[Candidate]) {
        self.children.entry(node.id).or_insert_with(Vec::new);
        for c in candidates {
            let node_id = self.add_new_candidate(c.clone(), node.level - 1);
            self.children.get_mut(&node.id).unwrap().push(node_id);
            self.parents.insert(node_id, Some(node.id));
        }
    }
    pub fn refute(&mut self, node: CandidateNode) {
        let parent = self.parents.get(&node.id).unwrap();
        match parent {
            Some(p) => {
                for child in self.children[p].iter() {
                    self.levels.remove(child);
                    self.labels.remove(child);
                }
            }
            None => {
                *self = Self::empty();
            }
        }
    }
    pub fn show_tree(&self) {
        fn show_tree_inner(tree: &CandidateTree, node_id: &NodeID, level: u64) {
            for _ in 0..level {
                print!("---");
            }
            print!(" ");
            println!("{}", &tree.labels[node_id]);
            match tree.children.get(node_id) {
                Some(children) => {
                    for id in children {
                        show_tree_inner(tree, id, level + 1)
                    }
                }
                None => (),
            }
        }
        let root = match &self.root {
            Some(root) => root,
            None => return (),
        };
        for x in root {
            show_tree_inner(self, x, 0)
        }
    }
}

#[derive(Clone, Debug)]
struct CandidateNode {
    level: usize,
    id: usize,
    label: Candidate,
}

pub struct HoPDR<'a> {
    models: CandidateTree,
    envs: Vec<PosEnvironment>,
    problem: &'a Problem,
    loop_cnt: u64,
    verbose: u64,
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
    #[allow(dead_code)]
    fn dump_state(&self) {
        println!("{}", "[PDR STATE]".green().bold());
        println!("- current loop: {}", self.loop_cnt);
        println!("- size of env: {}", self.envs.len());
        println!("- size of model: {}", self.models.size());
        for (level, e) in self.envs.iter().enumerate() {
            println!("Level {}", level);
            println!("{}", e);
        }
    }
    // generates a candidate
    // Assumption: self.check_valid() == false
    fn is_refutable(
        &self,
        candidate_node: &CandidateNode,
    ) -> RefuteOrCex<rtype::Ty, Vec<Candidate>> {
        debug!("[Candidate] is_refutable");
        // 1. generate constraints: calculate t s.t. c.sty ~ t and check if Env |- formula[c.ident] : t.
        // 2. if not typable, calculate cex
        // 3. if typable, returns the type
        let candidate = &candidate_node.label;
        match candidate.sty.is_refutable(
            self.get_clause_by_id(&candidate.ident),
            &self.envs[candidate_node.level - 1],
        ) {
            Ok(t) => RefuteOrCex::Refutable(t),
            Err(c) => RefuteOrCex::Cex(c.to_candidates()),
        }
    }

    fn candidate(&mut self) {
        debug!("{}", "candidate".purple());
        let top_false = Sty::mk_prop_ty(Constraint::mk_true());
        let candidates = match top_false.is_cex_available_top(&self.problem.top, self.top_env()) {
            Some(c) => c.to_candidates(),
            None => panic!("program error"),
        };
        println!("{}", "candidates".purple());
        println!("toplevel: {}", &self.problem.top);
        for c in candidates.iter() {
            println!("- {}", c);
        }

        self.models
            .add_root_children(&candidates, self.envs.len() - 1);
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
        let result = rtype::type_check_top(&self.problem.top, self.top_env().into());
        debug!("check_valid: {:?}", result);
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
                    debug!("not inductive");
                    return false;
                }
            }
        }
        true
    }

    fn initialize(&mut self) {
        println!("{}", "initialize".purple());
        self.envs.push(PosEnvironment::new_top_env(self.problem));
    }

    fn unfold(&mut self) {
        println!("{}", "unfold".purple());
        self.envs.push(PosEnvironment::new_bot_env(self.problem));
    }

    fn valid(&mut self) -> PDRResult {
        debug!("PDR valid");
        dprintln!(self.verbose, DEBUG, "[PDR]valid");
        PDRResult::Valid
    }

    fn invalid(&mut self) -> PDRResult {
        debug!("PDR invalid");
        dprintln!(self.verbose, DEBUG, "[PDR]invalid");
        self.models.show_tree();
        PDRResult::Invalid
    }

    fn check_feasible(&mut self) -> bool {
        debug!("[PDR]check feasible");
        loop {
            match self.models.get_unprocessed_leaf() {
                Some(c) => match self.is_refutable(&c) {
                    RefuteOrCex::Refutable(t) => {
                        self.conflict(c, t);
                        println!("{}", "conflict".blue());
                        if self.models.is_epsilon() {
                            return false;
                        }
                    }
                    RefuteOrCex::Cex(c2) => {
                        println!("{} {}", "decide".red(), c2.len());
                        println!("envs");
                        println!("{}", &self.envs[c.level - 1]);
                        println!("clause: {}", self.get_clause_by_id(&c.label.ident));
                        println!("stype: {}", &c.label.sty);
                        for c in c2.iter() {
                            println!("- {}", c);
                        }
                        self.decide(c, c2);
                    }
                },
                None => return true,
            }
        }
    }

    fn conflict(&mut self, c: CandidateNode, refute_ty: rtype::Ty) {
        println!("{}", "conflict".blue());
        debug!("[PDR]conflict: {} <-> {}", &c.label, &refute_ty);
        for i in 0..(c.level) {
            self.envs[i as usize].add(c.label.ident, refute_ty.clone());
        }
        self.models.refute(c);
    }

    fn decide(&mut self, parent: CandidateNode, children: Vec<Candidate>) {
        println!("{}", "decide".blue());
        debug!("[PDR]decide");
        self.models.add_children(parent, &children);
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

pub fn infer(problem: Problem) -> VerificationResult {
    let mut pdr = HoPDR::new(&problem);
    pdr.set_verbosity_level(DEBUG);
    pdr.run();

    unimplemented!()
}
