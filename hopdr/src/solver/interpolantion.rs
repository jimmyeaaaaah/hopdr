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
use crate::formula::Op;
use crate::formula::{Bot, Constraint, Ident, Logic, Negation, Top};
use crate::solver::interpolantion;

use std::collections::{HashMap, HashSet};
type CHC = chc::CHC<Constraint>;
type CHCBody = chc::CHCBody<Constraint>;

// topological sort
fn topological_sort(l: &[CHC]) -> (Vec<Ident>, HashMap<Ident, usize>) {
    type Graph = HashMap<Ident, HashSet<Ident>>;
    fn collect_preds(body: &CHCBody, s: &mut HashSet<Ident>, n_args: &mut HashMap<Ident, usize>) {
        for atom in body.predicates.iter() {
            s.insert(atom.predicate);
            n_args.insert(atom.predicate, atom.args.len());
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
    let mut n_args = HashMap::new();

    // add predicates that appear in the bodies of the given clauses
    let mut nodes = HashSet::new();
    for c in l {
        collect_preds(&c.body, &mut nodes, &mut n_args);
    }
    for node in nodes.into_iter() {
        graph.insert(node, HashSet::new());
    }

    for c in l {
        // generate edge
        match &c.head {
            chc::CHCHead::Constraint(_) => {}
            chc::CHCHead::Predicate(a) => match graph.get_mut(&a.predicate) {
                Some(s) => collect_preds(&c.body, s, &mut n_args),
                None => {
                    let mut s = HashSet::new();
                    collect_preds(&c.body, &mut s, &mut n_args);
                    graph.insert(a.predicate, s);
                }
            },
        }
    }
    (sort(&graph), n_args)
}

fn generate_least_solution(chc: &Vec<CHC>) -> CHCResult {
    // solve by hoice
    use super::chc::default_solver;
    let mut solver = default_solver();
    solver.solve(chc)
}

fn check_contains_head<'a>(p: Ident, head: &'a chc::CHCHead<Constraint>) -> Option<&'a Vec<Op>> {
    match head {
        chc::CHCHead::Predicate(a) if p == a.predicate => Some(&a.args),
        _ => None,
    }
}
fn check_contains_body(p: Ident, body: &chc::CHCBody<Constraint>) -> bool {
    for b in body.predicates.iter() {
        if b.predicate == p {
            return true;
        }
    }
    return false;
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
fn remove_pred_except_for<'a>(
    p: Ident,
    clause: &'a CHC,
    least_model: &Model,
    model: &Model,
) -> (Constraint, Option<&'a Vec<Op>>) {
    let get_constraint = |q: &chc::Atom| -> Constraint {
        let (arg_vars, c) = match model.model.get(&q.predicate) {
            Some((arg_vars, c)) => (arg_vars, c),
            None => {
                let (arg_vars, c) = least_model.model.get(&q.predicate).unwrap();
                (arg_vars, c)
            }
        };
        // replace [q.args/arg_vars]c
        unimplemented!()
    };
    let head = match &clause.head {
        chc::CHCHead::Constraint(c) => c.clone(),
        chc::CHCHead::Predicate(q) => get_constraint(q),
    };

    let mut body_constraint = clause.body.constraint.clone();
    // we assume that clause does not contain two `p`
    // i.e. p(x, y) /\ p(x + 1, y) => C is invalid
    let mut args = None;
    for body in clause.body.predicates.iter() {
        debug_assert!(body.predicate != p || args.is_none());
        if body.predicate == p {
            args = Some(&body.args);
        } else {
            let c = get_constraint(body);
            body_constraint = Constraint::mk_conj(body_constraint, c);
        }
    }
    (
        Constraint::mk_disj(body_constraint.negate().unwrap(), head),
        args,
    )
}

pub fn interpolate(left: &Constraint, right: &Constraint) -> Constraint {
    unimplemented!()
}

pub fn solve(chc: &Vec<CHC>) -> CHCResult {
    let least_model = match generate_least_solution(chc) {
        CHCResult::Sat(m) => m,
        x => return x,
    };
    let (preds, n_args) = topological_sort(chc);

    let mut model = Model::new();
    for p in preds {
        let arg_vars: Vec<Ident> = (0..*n_args.get(&p).unwrap())
            .map(|_| Ident::fresh())
            .collect();
        let mut strongest = Constraint::mk_false();
        let mut weakest = Constraint::mk_true();
        for c in chc {
            if check_contains_body(p, &c.body) {
                let (mut c, args) = remove_pred_except_for(p, c, &least_model, &model);
                let args = args.unwrap();
                assert!(args.len() == arg_vars.len());
                for i in 0..args.len() {
                    let left = Op::mk_var(arg_vars[i]);
                    let right = args[i].clone();
                    let c2 = Constraint::mk_pred(crate::formula::PredKind::Eq, vec![left, right]);
                    c = Constraint::mk_conj(c, c2);
                }
                strongest = Constraint::mk_disj(strongest, c);
            }
            match check_contains_head(p, &c.head) {
                Some(args) => {
                    let (c, args_debug) = remove_pred_except_for(p, c, &least_model, &model);
                    debug_assert!(args_debug.is_none());
                    weakest = Constraint::mk_conj(weakest, c);
                }
                None => (),
            }
        }
        // interpolation:
        let c = interpolate(&weakest, &strongest);
        model.model.insert(p, (arg_vars, c));
    }

    unimplemented!()
}
