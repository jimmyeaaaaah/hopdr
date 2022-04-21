// Input: non-recursive CHC
// Output: assignments to each predicate
// Algorithm:
//  1. Generates DAG of predicates based on their dependencies
//  2. constructs their least solution
//  3. calculates interpolants using off-the-shelf interpolant solvers
//     in the descending order of the DAG

// Current available interpolant solvers
//   1. Mathsat5

use super::chc::{CHCResult};
use crate::formula::chc;
use crate::formula::chc::Model;
use crate::formula::Fv;
use crate::formula::Op;
use crate::formula::Subst;
use crate::formula::{Bot, Constraint, Ident, Logic, Negation, Top};

use crate::solver::smt::ident_2_smt2;
use crate::solver::util;
use crate::solver::{smt, SMT2Style};

use std::collections::{HashMap, HashSet};
use std::time::Duration;
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
        while let Some(cur) = unchecked.iter().next() {
            let cur = *cur;
            unchecked.remove(&cur);
            dfs(graph, &mut sorted, &mut unchecked, cur);
        }
        sorted.reverse();
        sorted
    }

    let mut graph: Graph = HashMap::new();
    let mut n_args = HashMap::new();

    // add predicates that appear in the bodies of the given clauses
    let mut nodes = HashSet::new();
    for c in l {
        collect_preds(&c.body, &mut nodes, &mut n_args);
        match &c.head {
            chc::CHCHead::Constraint(_) => (),
            chc::CHCHead::Predicate(a) => {
                nodes.insert(a.predicate);
                n_args.insert(a.predicate, a.args.len());
            }
        }
    }
    for node in nodes.into_iter() {
        graph.insert(node, HashSet::new());
    }

    for c in l {
        // generate edge P -> Q for clause P(x) /\ .. => Q(x')
        match &c.head {
            chc::CHCHead::Constraint(_) => {}
            chc::CHCHead::Predicate(q) => {
                for p in c.body.predicates.iter() {
                    let s = graph.get_mut(&p.predicate).unwrap();
                    s.insert(q.predicate);
                }
            }
        }
    }
    (sort(&graph), n_args)
}

#[test]
fn test_topological_sort() {
    use crate::formula::chc::Atom;
    use crate::formula::Constraint;
    use chc::CHCHead;
    // Q => false
    // R /\ P => Q
    // true => P
    // true => R

    let pi = Ident::fresh();
    let p = Atom {
        predicate: pi,
        args: Vec::new(),
    };
    let qi = Ident::fresh();
    let q = Atom {
        predicate: qi,
        args: Vec::new(),
    };
    let ri = Ident::fresh();
    let r = Atom {
        predicate: ri,
        args: Vec::new(),
    };

    // graph
    // R -> Q
    // P ---^

    let b1 = CHCBody {
        predicates: vec![q.clone()],
        constraint: Constraint::mk_true(),
    };
    let b2 = CHCBody {
        predicates: vec![r.clone(), p.clone()],
        constraint: Constraint::mk_true(),
    };
    let b3 = CHCBody {
        predicates: vec![],
        constraint: Constraint::mk_true(),
    };
    let b4 = CHCBody {
        predicates: vec![],
        constraint: Constraint::mk_true(),
    };

    let h1 = CHCHead::Constraint(Constraint::mk_false());
    let h2 = CHCHead::Predicate(q.clone());
    let h3 = CHCHead::Predicate(p.clone());
    let h4 = CHCHead::Predicate(r.clone());
    let c1 = CHC { head: h1, body: b1 };
    let c2 = CHC { head: h2, body: b2 };
    let c3 = CHC { head: h3, body: b3 };
    let c4 = CHC { head: h4, body: b4 };

    let clauses = vec![c1, c2, c3, c4];
    let (order, _) = topological_sort(&clauses);
    println!("[clauses]");
    for c in clauses.iter() {
        println!("{}", c);
    }
    println!("[order]");
    for o in order.iter() {
        print!("{} ", o);
    }
    println!("");
    assert!(order.len() == 3);
    // R and P must appear before Q appears
    assert_eq!(order[2], qi);
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
) -> (Constraint, Constraint, Option<&'a Vec<Op>>) {
    let get_constraint = |q: &chc::Atom| -> Constraint {
        let (arg_vars, c) = match model.model.get(&q.predicate) {
            Some((arg_vars, c)) => (arg_vars, c),
            None => {
                let (arg_vars, c) = least_model.model.get(&q.predicate).unwrap();
                (arg_vars, c)
            }
        };
        let mut c = c.clone();
        // replace [q.args/arg_vars]c
        assert_eq!(arg_vars.len(), q.args.len());
        for i in 0..arg_vars.len() {
            c = c.subst(&arg_vars[i], &q.args[i]);
        }
        c
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
    (body_constraint, head, args)
}

fn conjoin_args(arg_vars: &[Ident], args: &[Op], mut body: Constraint) -> Constraint {
    assert!(args.len() == arg_vars.len());
    for i in 0..args.len() {
        let left = Op::mk_var(arg_vars[i]);
        let right = args[i].clone();
        let c2 = Constraint::mk_pred(crate::formula::PredKind::Eq, vec![left, right]);
        body = Constraint::mk_conj(body, c2);
    }
    body
}

fn parse_body(s: &str, fvs: HashSet<Ident>) -> Constraint {
    use crate::solver::chc::parse_body;
    let x = lexpr::from_str(s).unwrap();
    let x = x.as_cons().unwrap().car();
    let idents: HashMap<String, Ident> = fvs.into_iter().map(|x| (ident_2_smt2(&x), x)).collect();
    let mut map = idents.iter().map(|(x, y)| (x.as_str(), *y)).collect();
    debug!("{:?}", x);
    parse_body(x, &mut map).to_constraint().unwrap()
}

pub fn interpolate(left: &Constraint, right: &Constraint) -> Constraint {
    fn smtinterpol_solver(smt_string: String) -> String {
        debug!("smt_string: {}", &smt_string);
        let f = smt::save_smt2(smt_string);
        // TODO: determine the path when it's compiled
        let args = vec!["-jar", "/home/katsura/github.com/moratorium08/hopdr/hopdr/smtinterpol.jar", f.path().to_str().unwrap()];
        debug!("filename: {}", &args[0]);
        let out = util::exec_with_timeout(
            "java",
            //"../../../Hogeyama/hoice/target/debug/hoice",
            &args,
            Duration::from_secs(1),
        );
        String::from_utf8(out).unwrap()
    }

    let generate_smtinterpol = || -> (String, HashSet<Ident>) {
        /*
        (set-option :produce-interpolants true)
        (set-info :status unsat)
        (set-logic QF_UFLIA)
        (declare-fun x_1 () Int)
        (declare-fun xm1 () Int)
        (declare-fun x2 () Int)
        (declare-fun res4 () Int)
        (assert (! (<= x_1 100) :named IP_0))
        (assert (! (and (<= xm1 (+ x_1 11)) (>= xm1 (+ x_1 11))) :named IP_1))
        (assert (! (and (<= x2 xm1) (>= x2 xm1)) :named IP_2))
        (assert (! (> x2 100) :named IP_3))
        (assert (! (and (<= res4 (- x2 10)) (>= res4 (- x2 10))) :named IP_4))
        (assert (! (and (<= x2 101) (or (< res4 91) (> res4 91))) :named IP_5))
        (check-sat)
        (get-interpolants IP_0 IP_1 IP_2 IP_3 IP_4 IP_5)
         */
        let mut fvs = left.fv();
        right.fv_with_vec(&mut fvs);

        let header = "(set-option :produce-interpolants true)\n(set-info :status unsat)\n(set-logic QF_UFLIA)\n";

        let mut result = header.to_string();
        for var in fvs.iter() {
            result += &format!("(declare-fun {} () Int)\n", smt::ident_2_smt2(var));
        }
        let left_s = smt::constraint_to_smt2_inner(left, SMT2Style::Z3);
        result += &format!("(assert (! {} :named IP_0))\n", left_s);
        let right_s = smt::constraint_to_smt2_inner(right, SMT2Style::Z3);
        result += &format!("(assert (! {} :named IP_1))\n", right_s);

        result += "(check-sat)\n(get-interpolants IP_0 IP_1)\n";

        (result, fvs)
    };
    let (s, fvs) = generate_smtinterpol();
    let r = smtinterpol_solver(s);
    let mut lines = r.lines();
    loop {
        let line = lines.next().unwrap();
        if line.starts_with("unsat") {
            let line = lines.next().unwrap();
            debug!("parse_body: {}", line);
            return parse_body(line, fvs);
        } else if line.starts_with("sat") {
            panic!("program error: SMTInterpol concluded the constraint was sat (expected: unsat)\n[result of smtinterpol]\n{}", &r)
        }
    }
}

pub fn solve(chc: &Vec<CHC>) -> CHCResult {
    debug!("[interpolation::solve]");
    for c in chc {
        debug!("- {}", c);
    }
    let least_model = match generate_least_solution(chc) {
        CHCResult::Sat(m) => m,
        x => return x,
    };
    debug_assert!(crate::solver::chc::is_solution_valid(chc, &least_model));
    let chc: Vec<_> = chc.iter().map(|c| c.fresh_variailes()).collect();
    let chc = &chc;
    let (preds, n_args) = topological_sort(chc);

    let mut model = Model::new();
    // interpolate in the decending order of preds
    for p in preds.into_iter().rev() {
        let arg_vars: Vec<Ident> = (0..*n_args.get(&p).unwrap())
            .map(|_| Ident::fresh())
            .collect();
        let mut strongest = Constraint::mk_true();
        let mut weakest = Constraint::mk_false();
        for c in chc {
            // case: p(x) /\ ... => ...
            if check_contains_body(p, &c.body) {
                let (body, head, args) = remove_pred_except_for(p, c, &least_model, &model);
                let args = args.unwrap();
                let body = conjoin_args(&arg_vars, &args, body);
                // Constraint::mk_disj(body_constraint.negate().unwrap(), head),
                let c = Constraint::mk_disj(body.negate().unwrap(), head);
                strongest = Constraint::mk_conj(strongest, c);
            }
            // case: ... => p(x)
            match check_contains_head(p, &c.head) {
                //
                Some(args) => {
                    let (body, _, args_debug) = remove_pred_except_for(p, c, &least_model, &model);
                    debug_assert!(args_debug.is_none());
                    let c = conjoin_args(&arg_vars, &args, body);
                    weakest = Constraint::mk_disj(weakest, c);
                }
                None => (),
            }
        }
        let strongest_tmp = strongest.clone();
        let strongest = strongest.negate().unwrap();
        // translate constraints to prenex normal form
        let strongest = strongest.to_pnf();
        let weakest = weakest.to_pnf();
        // interpolation:
        let c = interpolate(&weakest, &strongest);

        // check weakest => c => strongest
        #[cfg(debug_assertions)]
        {
            let arrow1 = Constraint::mk_arrow(weakest, c.clone());
            let arrow2 = Constraint::mk_arrow(c.clone(), strongest_tmp);
            let check = Constraint::mk_conj(arrow1, arrow2);
            let mut solver = smt::default_solver();
            debug!("check:{}", check);
            let fvs = check.fv();
            match solver.solve(&check, &fvs) {
                crate::solver::SolverResult::Sat => (),
                crate::solver::SolverResult::Unsat |
                crate::solver::SolverResult::Unknown |
                crate::solver::SolverResult::Timeout => panic!("smtinterpol fail")
            }
        }

        debug!("interpolated: {}", c);
        model.model.insert(p, (arg_vars, c));
    }

    CHCResult::Sat(model)
}

#[test]
fn test_interpolation() {
    use crate::formula::chc::Atom;
    use crate::formula::PredKind;
    use chc::CHCHead;
    // P(x, y) => x >= y
    // x = 0 /\ y = 0 => P(x, y)
    let xi = Ident::fresh();
    let yi = Ident::fresh();
    let x = Op::mk_var(xi);
    let y = Op::mk_var(yi);
    let predicate = Ident::fresh();

    let tmp = Constraint::mk_pred(PredKind::Eq, vec![x.clone(), Op::mk_const(0)]);
    let tmp2 = Constraint::mk_pred(PredKind::Eq, vec![y.clone(), Op::mk_const(0)]);
    let c1 = Constraint::mk_pred(PredKind::Geq, vec![x.clone(), y.clone()]);
    let c2 = Constraint::mk_conj(tmp, tmp2);

    let a = Atom {
        predicate,
        args: vec![x.clone(), y.clone()],
    };
    let b1 = CHCBody {
        predicates: vec![a.clone()],
        constraint: Constraint::mk_true(),
    };
    let h1 = CHCHead::Constraint(c1);
    let b2 = CHCBody {
        predicates: Vec::new(),
        constraint: c2,
    };
    let h2 = CHCHead::Predicate(a.clone());
    let clause1 = CHC { head: h1, body: b1 };
    let clause2 = CHC { head: h2, body: b2 };
    debug!("- {}", clause1);
    debug!("- {}", clause2);
    let clauses = vec![clause1, clause2];

    let r = solve(&clauses);

    match r {
        CHCResult::Sat(m) => {
            for (x, (_, z)) in m.model {
                debug!("{} => {}", x, z)
            }
        }
        _ => assert!(false),
    }
}
