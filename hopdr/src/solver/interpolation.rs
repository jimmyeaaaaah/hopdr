// Input: non-recursive CHC
// Output: assignments to each predicate
// Algorithm:
//  1. Generates DAG of predicates based on their dependencies
//  2. constructs their least solution
//  3. calculates interpolants using off-the-shelf interpolant solvers
//     in the descending order of the DAG

// Current available interpolant solvers
//   1. Mathsat5

use crate::formula::chc;
use crate::formula::chc::Model;
use crate::formula::Fv;
use crate::formula::Op;
use crate::formula::Subst;
use crate::formula::{Bot, Constraint, FirstOrderLogic, Ident, Logic, Negation, Top};
use crate::solver;
use crate::solver::interpolation::InterpolationSolver::SMTInterpol;
use crate::solver::smt::ident_2_smt2;
use crate::solver::util;
use crate::solver::{smt, SMTSolverType};

use home::home_dir;

use std::collections::{HashMap, HashSet};
use std::time::Duration;

type CHC = chc::CHC<chc::Atom, Constraint>;
type CHCBody = chc::CHCBody<chc::Atom, Constraint>;

static mut SMTINTERPOL_PATH: Option<String> = None;
pub fn set_smt_interpol_path(path: String) {
    unsafe {
        SMTINTERPOL_PATH = Some(path);
    }
}
fn get_smt_interpol_path() -> String {
    match unsafe { &SMTINTERPOL_PATH } {
        Some(s) => s.clone(),
        None => {
            let mut home = home_dir().unwrap();
            home.push(".local/share/hopdr/smtinterpol.jar");
            home.into_os_string().into_string().unwrap()
        }
    }
}
pub enum InterpolationSolver {
    SMTInterpol,
    Csisat,
}

// topological sort
fn topological_sort(l: &[CHC]) -> Option<(Vec<Ident>, HashMap<Ident, usize>)> {
    type Graph = HashMap<Ident, HashSet<Ident>>;
    fn collect_preds(body: &CHCBody, s: &mut HashSet<Ident>, n_args: &mut HashMap<Ident, usize>) {
        for atom in body.predicates.iter() {
            s.insert(atom.predicate);
            n_args.insert(atom.predicate, atom.args.len());
        }
    }

    fn dfs(
        graph: &Graph,
        sorted: &mut Vec<Ident>,
        unchecked: &mut HashSet<Ident>,
        is_temporary: &mut HashSet<Ident>,
        cur: Ident,
    ) -> Result<(), ()> {
        match graph.get(&cur) {
            Some(s) => {
                for i in s.iter() {
                    if unchecked.contains(i) {
                        unchecked.remove(i);
                        is_temporary.insert(*i);
                        dfs(graph, sorted, unchecked, is_temporary, *i)?;
                        is_temporary.remove(i);
                    } else if is_temporary.contains(i) {
                        // a cycle has been found.
                        return Err(());
                    }
                }
            }
            None => panic!("program error"),
        }
        sorted.push(cur);
        Ok(())
    }

    fn sort(graph: &Graph) -> Option<Vec<Ident>> {
        let mut unchecked = HashSet::new();
        let mut is_temporary = HashSet::new();
        let mut sorted = Vec::new();
        for k in graph.keys() {
            unchecked.insert(*k);
        }
        while let Some(cur) = unchecked.iter().next() {
            let cur = *cur;
            unchecked.remove(&cur);
            is_temporary.insert(cur);
            match dfs(graph, &mut sorted, &mut unchecked, &mut is_temporary, cur) {
                Ok(()) => (),
                Err(()) => return None,
            }
            is_temporary.remove(&cur);
        }
        sorted.reverse();
        Some(sorted)
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
    sort(&graph).map(|order| (order, n_args))
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

    let mut clauses = vec![c1, c2, c3, c4];
    let (order, _) = topological_sort(&clauses).unwrap();
    println!("[clauses]");
    for c in clauses.iter() {
        println!("{}", c);
    }
    println!("[order]");
    for o in order.iter() {
        print!("{} ", o);
    }
    println!();
    assert!(order.len() == 3);
    // R and P must appear before Q appears
    assert_eq!(order[2], qi);

    debug!("next we check the case where the constraints contain a cycle");

    // check detection of a cycle
    // Graph:
    //  P => P
    //   + the above
    let b = CHCBody {
        predicates: vec![p.clone()],
        constraint: Constraint::mk_true(),
    };
    let h = CHCHead::Predicate(p.clone());
    let c = CHC { head: h, body: b };
    clauses.push(c);

    println!("[clauses]");
    for c in clauses.iter() {
        println!("{}", c);
    }
    assert!(topological_sort(&clauses).is_none());
}

fn check_contains_head(p: Ident, head: &chc::CHCHead<chc::Atom, Constraint>) -> Option<&Vec<Op>> {
    match head {
        chc::CHCHead::Predicate(a) if p == a.predicate => Some(&a.args),
        _ => None,
    }
}
fn check_contains_body(p: Ident, body: &chc::CHCBody<chc::Atom, Constraint>) -> bool {
    for b in body.predicates.iter() {
        if b.predicate == p {
            return true;
        }
    }
    false
}

// replace q by model(q) if q in model
//           by least_model(q), otherwise
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
    debug!("{}", clause);
    debug!("{}", p);
    let get_constraint = |q: &chc::Atom| -> Constraint {
        debug!("get_constraint q: {}", q);
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
        for (i, item) in arg_vars.iter().enumerate() {
            c = c.subst(item, &q.args[i]);
        }
        debug!("model[{}] = {}", q.predicate, c);
        debug!("args:");
        for arg in q.args.iter() {
            debug!("- {}", arg);
        }
        c
    };
    let (head, head_contains_p) = match &clause.head {
        chc::CHCHead::Constraint(c) => (c.clone(), false),
        chc::CHCHead::Predicate(q) if q.predicate != p => (get_constraint(q), false),
        _ => (Constraint::mk_true(), true),
    };

    let mut body_constraint = clause.body.constraint.clone();
    // we assume that `clause' does not contain two `p`
    // i.e. p(x, y) /\ p(x + 1, y) => C is invalid
    let mut args = None;
    for body in clause.body.predicates.iter() {
        debug_assert!(body.predicate != p || (args.is_none() && !head_contains_p));
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
    parse_body(x, &mut map).to_constraint().unwrap()
}

/// helper macro for measuring total time for execution
macro_rules! interp_execution {
    ( $b:block ) => {{
        #[cfg(not(debug_assertions))]
        {
            crate::stat::interpolation::count();

            crate::stat::interpolation::start_clock();
        }

        let out = $b;

        #[cfg(not(debug_assertions))]
        {
            crate::stat::interpolation::end_clock();
        }
        out
    }};
}

struct SMTInterpolSolver {}
struct CsisatSolver {}
impl InterpolationSolver {
    pub fn get_solver(sol: InterpolationSolver) -> Box<dyn Interpolation> {
        match sol {
            InterpolationSolver::SMTInterpol => Box::new(SMTInterpolSolver {}),
            InterpolationSolver::Csisat => Box::new(CsisatSolver {}),
        }
    }
    pub fn default_solver() -> Box<dyn Interpolation> {
        Self::get_solver(SMTInterpol)
    }
}

#[derive(Debug)]
enum InterpolationError {
    ParseError(String),
    Satisfiable(String),
}

impl SMTInterpolSolver {
    fn generate_smt_string(
        &mut self,
        left: &Constraint,
        right: &Constraint,
    ) -> (String, HashSet<Ident>) {
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
        let left_s = smt::constraint_to_smt2_inner(left, SMTSolverType::Z3);
        result += &format!("(assert (! {} :named IP_0))\n", left_s);
        let right_s = smt::constraint_to_smt2_inner(right, SMTSolverType::Z3);
        result += &format!("(assert (! {} :named IP_1))\n", right_s);

        result += "(check-sat)\n(get-interpolants IP_0 IP_1)\n";

        (result, fvs)
    }
    fn execute_solver(&mut self, smt_string: String) -> String {
        debug!("smt_string: {}", &smt_string);
        let f = smt::save_smt2(smt_string);
        // TODO: determine the path when it's compiled
        let s = get_smt_interpol_path();
        let args = vec!["-jar", &s, f.path().to_str().unwrap()];
        debug!("filename: {}", &args[0]);
        let out = interp_execution!({
            util::exec_with_timeout(
                "java",
                //"../../../Hogeyama/hoice/target/debug/hoice",
                &args,
                Duration::from_secs(1),
            )
        });
        String::from_utf8(out).unwrap()
    }
    fn parse_result(
        &mut self,
        result: String,
        fvs: HashSet<Ident>,
    ) -> Result<Constraint, InterpolationError> {
        crate::title!("smt_interpol");
        debug!("{}", result);
        let mut lines = result.lines();
        loop {
            let line = match lines.next() {
                Some(line) => line,
                None => return Err(InterpolationError::ParseError(result.clone())),
            };
            if line.starts_with("unsat") {
                let line = lines.next().unwrap();
                let parsed = parse_body(line, fvs);
                debug!("parsed: {}", parsed);
                return Ok(parsed);
            } else if line.starts_with("sat") {
                return Err(InterpolationError::Satisfiable(result.clone()));
                //panic!("program error: SMTInterpol concluded the constraint was sat (expected: unsat)\n[result of smtinterpol]\n{}", &r)
            }
        }
    }
}
impl Interpolation for SMTInterpolSolver {
    fn interpolate(&mut self, left: &Constraint, right: &Constraint) -> Constraint {
        let (s, fvs) = self.generate_smt_string(left, right);
        let r = self.execute_solver(s);
        self.parse_result(r, fvs).unwrap()
    }
}

impl CsisatSolver {
    fn generate_constraint_string(&mut self, c: &Constraint) -> String {
        format!("%HES\nM =v {}.", c.to_hes_format())
    }
    fn execute_solver(&mut self, smt_string1: String, smt_string2: String) -> String {
        let f1 = smt::save_smt2(smt_string1);
        let f2 = smt::save_smt2(smt_string2);
        // TODO: determine the path when it's compiled
        let arg = format!(
            "{},{}",
            f1.path().to_str().unwrap(),
            f2.path().to_str().unwrap()
        );
        let args = vec![arg.as_str()];
        let out = interp_execution!({
            util::exec_with_timeout("fpat_interp", &args, Duration::from_secs(1))
        });
        String::from_utf8(out).unwrap()
    }
    fn parse_result(
        &mut self,
        result: String,
        _fvs: HashSet<Ident>,
    ) -> Result<Constraint, InterpolationError> {
        use crate::parse;
        use nom::error::VerboseError;
        let e = parse::parse_expr::<VerboseError<&str>>(&result).unwrap().1;
        let c = Constraint::from(e);
        Ok(c)
    }
}

impl Interpolation for CsisatSolver {
    fn interpolate(&mut self, left: &Constraint, right: &Constraint) -> Constraint {
        let mut fvs = HashSet::new();
        left.fv_with_vec(&mut fvs);
        right.fv_with_vec(&mut fvs);

        let left_s = self.generate_constraint_string(left);
        let right_s = self.generate_constraint_string(right);
        debug!("{}", &left_s);
        debug!("{}", &right_s);

        let s = self.execute_solver(left_s, right_s);
        debug!("result: {}", s);
        self.parse_result(s, fvs).unwrap()
    }
}

pub trait Interpolation {
    /// calculates psi where left => psi and psi => right where fv(psi) ⊂ fv(left) ∪ fv(right)
    fn interpolate(&mut self, left: &Constraint, right: &Constraint) -> Constraint;
}

fn generate_least_solution(
    chc: &Vec<CHC>,
    sorted_preds: &[Ident],
    n_args: &HashMap<Ident, usize>,
) -> Model {
    let mut model = Model::new();
    for p in sorted_preds.iter() {
        // assume p(arg_vars..) := ?
        // and calculate ? by Terauchi (2010)
        let arg_vars: Vec<Ident> = (0..*n_args.get(p).unwrap())
            .map(|_| Ident::fresh())
            .collect();
        let mut constraint = Constraint::mk_false();

        for clause in chc {
            // case: ... => p(x)
            if let Some(args) = check_contains_head(*p, &clause.head) {
                debug!("contains_head: {}", clause);
                // here we reuse `remove_pred_except_for'.
                // this function first try to substitute pred with the def
                // in `model', and then substitute it with def in `least_model'.
                // However, since we are calculating least_model in the ascending order
                // of DAG of preds, all the predicates that appear in the body
                // of `clause' must have been in `model'.
                // Therefore, we pass Model::new() (empty model) as least_model,
                // and this never fails.
                let (body, _, args_debug) =
                    remove_pred_except_for(*p, clause, &Model::new(), &model);
                debug_assert!(args_debug.is_none());
                let c = conjoin_args(&arg_vars, args, body);
                debug!("{}", c);
                constraint = Constraint::mk_disj(constraint, c);
            }
        }
        // quantify free variables.
        let fvs = constraint.fv();
        let arg_vars_set: HashSet<Ident> = arg_vars.iter().cloned().collect();
        for fv in fvs {
            if !arg_vars_set.contains(&fv) {
                constraint = Constraint::mk_quantifier_int(
                    crate::formula::QuantifierKind::Existential,
                    fv,
                    constraint,
                );
            }
        }
        model.model.insert(*p, (arg_vars, constraint));
    }
    model
}

fn interpolate_preds(
    chc: &Vec<CHC>,
    sorted_preds: &[Ident],
    n_args: &HashMap<Ident, usize>,
    least_model: &Model,
    mut solver: Box<dyn Interpolation>,
) -> Model {
    debug_assert!(crate::solver::chc::is_solution_valid(chc, least_model));
    let mut model = Model::new();
    // interpolate in the decending order of preds
    for p in sorted_preds.iter().rev() {
        let arg_vars: Vec<Ident> = (0..*n_args.get(p).unwrap())
            .map(|_| Ident::fresh())
            .collect();
        let mut strongest = Constraint::mk_true();
        let mut weakest = Constraint::mk_false();
        for clause in chc {
            // case: p(x) /\ ... => ...
            if check_contains_body(*p, &clause.body) {
                debug!("contains_body: {}", clause);
                let (body, head, args) = remove_pred_except_for(*p, clause, least_model, &model);
                let args = args.unwrap();
                let body = conjoin_args(&arg_vars, args, body);
                // Constraint::mk_disj(body_constraint.negate().unwrap(), head),
                let c = Constraint::mk_disj(body.negate().unwrap(), head);
                #[cfg(debug_assertions)]
                {
                    use crate::formula::Rename;
                    let mut solver = smt::default_solver();
                    debug!("{}", c);
                    let (args, mut c2) = least_model.model.get(p).unwrap().clone();
                    for (id, replaced) in args.iter().zip(arg_vars.iter()) {
                        c2 = c2.rename(id, replaced);
                    }
                    let check = Constraint::mk_implies(c2, c.clone());
                    if !solver.solve_with_universal_quantifiers(&check).is_sat() {
                        use colored::Colorize;
                        warn!("{}", "fail!".red());
                        let mut merged = Model::new();
                        // merge least_model & model
                        for (k, v) in least_model.model.iter() {
                            match model.model.get(k) {
                                Some(v) => merged.model.insert(*k, v.clone()),
                                None => merged.model.insert(*k, v.clone()),
                            };
                        }
                        debug!(
                            "merged: {}",
                            solver
                                .solve_with_universal_quantifiers(
                                    &clause.replace_with_model(&merged),
                                )
                                .is_sat()
                        );

                        debug!(
                            "{}",
                            solver
                                .solve_with_universal_quantifiers(
                                    &clause.replace_with_model(least_model),
                                )
                                .is_sat()
                        );
                        panic!("fail!")
                    }
                }
                strongest = Constraint::mk_conj(strongest, c);
            }
            // case: ... => p(x)
            if let Some(args) = check_contains_head(*p, &clause.head) {
                debug!("contains_head: {}", clause);
                let (body, _, args_debug) = remove_pred_except_for(*p, clause, least_model, &model);
                debug_assert!(args_debug.is_none());
                let c = conjoin_args(&arg_vars, args, body);
                debug!("{}", c);
                weakest = Constraint::mk_disj(weakest, c);
            }
        }

        // to get ψ s.t. "weakest" => ψ => "strongest",
        // calculate SMTInterpol("weakest", not "strongest")
        let strongest_tmp = strongest.clone();
        let strongest = strongest.negate().unwrap();
        // translate constraints to prenex normal form
        let strongest = strongest.to_pnf();
        let weakest = weakest.to_pnf();
        #[cfg(debug_assertions)]
        {
            let mut solver = smt::default_solver();
            crate::title!("strongest");
            // adhoc: to print the formula
            solver.solve(&strongest_tmp, &HashSet::new());
            crate::title!("weakest");
            solver.solve(&weakest, &HashSet::new());
            // check weakest => c => strongest
            let arrow3 = Constraint::mk_implies(weakest.clone(), strongest_tmp.clone());
            assert!(solver.solve_with_universal_quantifiers(&arrow3).is_sat());
        }
        // interpolation:
        crate::title!("trying to interpolate...");
        let c = solver.interpolate(&weakest, &strongest);

        #[cfg(debug_assertions)]
        {
            let mut solver = smt::default_solver();
            crate::title!("trying to check if the result is correct");
            // check if weakest => strongest
            let arrow1 = Constraint::mk_implies(weakest, c.clone());
            let arrow2 = Constraint::mk_implies(c.clone(), strongest_tmp);
            assert!(solver.solve(&arrow1, &HashSet::new()).is_sat());
            assert!(solver.solve(&arrow2, &HashSet::new()).is_sat());
        }

        debug!("interpolated: {}", c);
        model.model.insert(*p, (arg_vars, c));
    }
    model
}

pub struct InterpolationConfig {
    use_chc_if_requied: bool,
}

impl InterpolationConfig {
    pub fn new() -> Self {
        InterpolationConfig {
            use_chc_if_requied: false,
        }
    }
    pub fn use_chc_if_requied(mut self) -> Self {
        self.use_chc_if_requied = true;
        self
    }
}

impl Default for InterpolationConfig {
    fn default() -> Self {
        Self::new()
    }
}

/// interpolate predicates under the given CHC constraints.
///
/// Assumption: `chc' is satisfiable.
pub fn solve(chc: &Vec<CHC>, config: &InterpolationConfig) -> Model {
    debug!("[interpolation::solve]");
    for c in chc {
        debug!("- {}", c);
    }
    let chc: Vec<_> = chc.iter().map(|c| c.fresh_variables()).collect();
    let chc = &chc;
    match topological_sort(chc) {
        Some((preds, n_args)) => {
            let least_model = generate_least_solution(chc, &preds, &n_args);

            interpolate_preds(
                chc,
                &preds,
                &n_args,
                &least_model,
                InterpolationSolver::default_solver(),
            )
        }
        None if config.use_chc_if_requied => {
            debug!("using chc solver since the constraints contain a loop");
            let mut solver = solver::chc::interpolating_solver();
            match solver.solve(chc) {
                solver::chc::CHCResult::Sat(mut m) => {
                    let qe_solver = solver::qe::QESolver::default_solver();
                    qe_solver.model_quantifer_elimination(&mut m);
                    m
                }
                solver::chc::CHCResult::Unsat
                | solver::chc::CHCResult::Unknown
                | solver::chc::CHCResult::Timeout => panic!("program error"),
            }
        }
        None => panic!("constraints contain a cycle"),
    }
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

    let config = InterpolationConfig::new().use_chc_if_requied();
    let m = solve(&clauses, &config);

    for (x, (_, z)) in m.model {
        debug!("{} => {}", x, z)
    }
}
