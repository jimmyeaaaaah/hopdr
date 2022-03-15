// Input: non-recursive CHC
// Output: assignments to each predicate
// Algorithm:
//  1. Generates DAG of predicates based on their dependencies
//  2. constructs their least solution
//  3. calculates interpolants using off-the-shelf interpolant solvers
//     in the descending order of the DAG

// Current available interpolant solvers
//   1. Mathsat5

use super::chc::{CHCResult, Model};
use crate::formula::chc;
use crate::formula::pcsp;
use crate::formula::{Bot, Constraint, Ident, Logic, Negation, Top};

use std::collections::{HashMap, HashSet};
type CHC = chc::CHC<pcsp::Atom>;

// topological sort
fn topological_sort(l: &[CHC]) -> Vec<Ident> {
    type Graph = HashMap<Ident, HashSet<Ident>>;
    fn collect_preds(a: &pcsp::Atom, s: &mut HashSet<Ident>) {
        match a.kind() {
            pcsp::AtomKind::True | pcsp::AtomKind::Constraint(_) => (),
            pcsp::AtomKind::Predicate(p, _) => {
                s.insert(*p);
            }
            pcsp::AtomKind::Conj(x, y) | pcsp::AtomKind::Disj(x, y) => {
                collect_preds(x, s);
                collect_preds(y, s);
            }
            pcsp::AtomKind::Quantifier(_, _, x) => {
                collect_preds(x, s);
            }
        }
    }

    fn dfs(graph: &Graph, sorted: &mut Vec<Ident>, unchecked: &mut HashSet<Ident>, cur: Ident) {
        match graph.get(&cur) {
            Some(s) => {
                for i in s.iter() {
                    if unchecked.contains(i) {
                        unchecked.remove(i);
                        dfs(graph, sorted, unchecked, *i);
                    }
                }
            }
            None => panic!("program error"),
        }
        sorted.push(cur);
    }

    fn sort(graph: &Graph) -> Vec<Ident> {
        let mut unchecked = HashSet::new();
        let mut sorted = Vec::new();
        for k in graph.keys() {
            unchecked.insert(*k);
        }
        let cur = graph.keys().nth(0).unwrap();
        dfs(graph, &mut sorted, &mut unchecked, *cur);
        sorted
    }

    let mut graph: Graph = HashMap::new();

    // add predicates that appear in the bodies of the given clauses
    let mut nodes = HashSet::new();
    for c in l {
        collect_preds(&c.body, &mut nodes);
    }
    for node in nodes.into_iter() {
        graph.insert(node, HashSet::new());
    }

    for c in l {
        // generate edge
        match &c.head {
            chc::CHCHead::Constraint(_) => {}
            chc::CHCHead::Predicate(p, _) => match graph.get_mut(p) {
                Some(s) => collect_preds(&c.body, s),
                None => {
                    let mut s = HashSet::new();
                    collect_preds(&c.body, &mut s);
                    graph.insert(*p, s);
                }
            },
        }
    }
    sort(&graph)
}

fn generate_least_solution(chc: &Vec<CHC>) -> CHCResult {
    // solve by hoice
    use super::chc::default_solver;
    let mut solver = default_solver();
    solver.solve(chc)
}

fn check_contains(p: Ident, a: &pcsp::Atom) -> bool {
    match a.kind() {
        pcsp::AtomKind::Predicate(q, _) if q == p => true,
        pcsp::AtomKind::True | pcsp::AtomKind::Constraint(_) | pcsp::AtomKind::Predicate(_, _) => {
            false
        }
        pcsp::AtomKind::Conj(x, y) | pcsp::AtomKind::Disj(x, y) => {
            let x = check_contains(p, x);
            let y = check_contains(p, y);
            if x && y {
                // the clause contains p more than once
                panic!("program error")
            } else {
                x || y
            }
        }
        pcsp::AtomKind::Quantifier(_, _, x) => check_contains(p, x),
    }
}

// replace q by model(q) such that p < q in the topological order
//           by least_model(q) otherwise
// Example:
// [a] p(x, y) /\ q(x, y) /\ x > y => r(x)
// [least_model]
//   - p(x, y) = x = y
//   - q(x, y) = x > y
//   - r(x) = x > y
// [model]
//   - q(x, y) = x >= y
//
// result: p(x, y) => x > y /\ x <= y /\ x >= y
fn remove_pred_except_for(p: Ident, a: pcsp::Atom, least_model: Model, model: Model) -> pcsp::Atom {
    use pcsp::Atom;
    match a.kind() {
        pcsp::AtomKind::True => Atom::mk_false(),
        pcsp::AtomKind::Constraint(c) => Atom::mk_constraint(c.negate().unwrap()),
        pcsp::AtomKind::Predicate(p, l) => Atom::mk_true(),
        pcsp::AtomKind::Conj(_, _) => todo!(),
        pcsp::AtomKind::Disj(_, _) => todo!(),
        pcsp::AtomKind::Quantifier(_, _, _) => todo!(),
    }
}

pub fn solve(chc: &Vec<CHC>) -> CHCResult {
    let least_model = match generate_least_solution(chc) {
        CHCResult::Sat(m) => m,
        x => return x,
    };
    let preds = topological_sort(chc);

    for p in preds {
        let p = Constraint::mk_false();
        for c in chc {
            if check_contains(p, c.body) {}
        }
    }

    unimplemented!()
}
