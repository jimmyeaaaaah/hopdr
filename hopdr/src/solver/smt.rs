use tempfile::NamedTempFile;

use std::collections::{HashMap, HashSet};
use std::time::Duration;

use super::util;
use super::{Model, SMTSolverType, SolverResult};
use crate::formula::{
    Constraint, ConstraintExpr, FirstOrderLogic, Fv, Ident, Logic, Op, OpExpr, OpKind, PredKind,
    QuantifierKind, Subst, Top,
};
use lexpr;
use lexpr::Value;

fn encode_ident(x: &Ident) -> String {
    format!("x{}", x)
}

fn parse_variable(v: &str) -> Ident {
    assert!(v.starts_with('x'));
    Ident::from_str(&v[1..]).unwrap_or_else(|| panic!("parse fail"))
}

fn parse_declare_fun(v: lexpr::Value) -> (Ident, i64) {
    // parse fail
    const ERRMSG: &str = "smt model parse fail";
    fn cons_value_to_iter<'a>(v: &'a lexpr::Value) -> impl Iterator<Item = &'a lexpr::Value> {
        v.as_cons()
            .unwrap_or_else(|| panic!("{}({})", ERRMSG, v))
            .iter()
            .map(|x| x.car())
    }
    let mut itr = cons_value_to_iter(&v);
    let _ = itr.next().unwrap_or_else(|| panic!("{}", ERRMSG));
    //assert_eq!(v.as_symbol().unwrap(), "define-fun");

    let x = itr.next().unwrap_or_else(|| panic!("{}", ERRMSG));
    let v = x.as_symbol().unwrap_or_else(|| panic!("{}", ERRMSG));
    let ident = parse_variable(v);

    let _ = itr.next().unwrap_or_else(|| panic!("{}", ERRMSG)); // null
    let _ = itr.next().unwrap_or_else(|| panic!("{}", ERRMSG)); // int
    let x = itr.next().unwrap_or_else(|| panic!("{}", ERRMSG)); // integer or (- 1)
    let v = match x.as_i64() {
        Some(v) => v,
        None => {
            let mut itr = cons_value_to_iter(x);
            let x = itr.next().unwrap_or_else(|| panic!("{}", ERRMSG));
            assert_eq!(x.as_symbol().unwrap_or_else(|| panic!("{}", ERRMSG)), "-");
            let x = itr.next().unwrap_or_else(|| panic!("{}", ERRMSG));
            -x.as_i64().unwrap_or_else(|| panic!("{}", ERRMSG))
        }
    };

    (ident, v)
}

impl Model {
    fn from_z3_model_str(s: &str) -> Result<Model, lexpr::parse::Error> {
        let x = lexpr::from_str(s)?;
        let model: HashMap<Ident, i64> = match x {
            Value::Cons(x) => x
                .into_iter()
                .skip(1)
                .map(|(v, _)| parse_declare_fun(v))
                .collect(),
            _ => panic!("parse error: smt2 model: {}", s),
        };
        Ok(Model { model })
    }

    pub fn get(&self, x: &Ident) -> Option<i64> {
        self.model.get(x).cloned()
    }
}

#[test]
fn z3_parse_model() {
    let model = "(model
        (define-fun x_x1 () Int
        (- 1))
        (define-fun x_x2 () Int
          1)
      )";
    match Model::from_z3_model_str(model) {
        Ok(m) => {
            let x1 = m.get(&1.into()).unwrap();
            let x2 = m.get(&2.into()).unwrap();
            assert_eq!(x1, -1);
            assert_eq!(x2, 1);
        }
        Err(_) => panic!("model is broken"),
    }
}

pub trait SMTSolver {
    /// Given a constraint, the solver executes an SMT solver to check whether
    /// it is satisfiable or not
    ///
    /// - constraint: The constraint to be checked by SMT solver
    /// - vars: variables to be bound by universal quantifiers.
    fn solve(&mut self, constraint: &Constraint, vars: &HashSet<Ident>) -> SolverResult;
    /// Given a constraint, the solver executes an SMT solver to check whether
    /// it is satisfiable or not, and returns the model for `fvs`.
    ///
    /// - constraint: The constraint to be checked by SMT solver
    /// - vars: variables to be bound by universal quantifiers.
    /// - fvs: variables to be bound by existential quantifier
    fn solve_with_model(
        &mut self,
        constraint: &Constraint,
        vars: &HashSet<Ident>,
        fvs: &HashSet<Ident>,
    ) -> Result<Model, SolverResult>;
    /// check left <=> right
    ///
    /// all free variables are to be universally quantified
    fn check_equivalent(&mut self, left: &Constraint, right: &Constraint) -> SolverResult {
        let rightarrow = Constraint::mk_implies(left.clone(), right.clone());
        let leftarrow = Constraint::mk_implies(right.clone(), left.clone());
        let equivalent = Constraint::mk_conj(rightarrow, leftarrow);

        self.solve_with_universal_quantifiers(&equivalent)
    }
    /// check if the constraint is satisfiable where all free variables are quantified by universal
    /// quantifiers
    fn solve_with_universal_quantifiers(&mut self, constraint: &Constraint) -> SolverResult {
        let fvs = constraint.fv();
        self.solve(constraint, &fvs)
    }
}

fn pred_to_smt2(p: &PredKind, args: &[String]) -> String {
    let args = args.join(" ");
    match p {
        PredKind::Eq => format!("(= {})", args),
        PredKind::Neq => format!("(not (= {}))", args),
        PredKind::Lt => format!("(< {})", args),
        PredKind::Leq => format!("(<= {})", args),
        PredKind::Gt => format!("(> {})", args),
        PredKind::Geq => format!("(>= {})", args),
    }
}

fn opkind_2_smt2(o: &OpKind) -> &'static str {
    match o {
        OpKind::Add => "+",
        OpKind::Sub => "-",
        OpKind::Mul => "*",
        OpKind::Div => "/",
        OpKind::Mod => "%",
    }
}

pub(super) fn ident_2_smt2(ident: &Ident) -> String {
    encode_ident(ident)
}

pub(super) fn op_to_smt2(op: &Op) -> String {
    match op.kind() {
        OpExpr::Op(opkind, o1, o2) => {
            let o1 = op_to_smt2(o1);
            let o2 = op_to_smt2(o2);
            let k = opkind_2_smt2(opkind);
            format!("({} {} {})", k, o1, o2)
        }
        OpExpr::Var(x) => ident_2_smt2(x),
        OpExpr::Const(c) if *c >= 0 => format!("{}", c),
        OpExpr::Const(c) => format!("(- {})", -c),
        OpExpr::Ptr(_, o) => op_to_smt2(o),
    }
}

pub(super) fn quantifier_to_smt2(q: &QuantifierKind) -> &'static str {
    match q {
        QuantifierKind::Existential => "exists",
        QuantifierKind::Universal => "forall",
    }
}

pub(super) fn constraint_to_smt2_inner(c: &Constraint, style: SMTSolverType) -> String {
    let f = constraint_to_smt2_inner;
    match c.kind() {
        ConstraintExpr::True => "true".to_string(),
        ConstraintExpr::False => "false".to_string(),
        ConstraintExpr::Pred(p, l) => {
            let args = l.iter().map(|op| op_to_smt2(op)).collect::<Vec<_>>();
            pred_to_smt2(p, &args)
        }
        ConstraintExpr::Conj(c1, c2) => format!("(and {} {})", f(c1, style), f(c2, style)),
        ConstraintExpr::Disj(c1, c2) => format!("(or {} {})", f(c1, style), f(c2, style)),
        ConstraintExpr::Quantifier(q, x, c) => format!(
            "({} (({} Int)) {})",
            quantifier_to_smt2(q),
            ident_2_smt2(&x.id),
            f(c, style)
        ),
    }
}

fn constraint_to_smt2(
    c: &Constraint,
    style: SMTSolverType,
    vars: &HashSet<Ident>,
    fvs: Option<&HashSet<Ident>>,
) -> String {
    let c_s = constraint_to_smt2_inner(c, style);
    let c_s = if !vars.is_empty() {
        // (forall ((%s Int)) %s)
        let decls = vars
            .iter()
            .map(|ident| format!("({} Int)", ident_2_smt2(ident)))
            .collect::<Vec<_>>()
            .join("");
        format!("(forall ({}) {})", decls, c_s)
    } else {
        c_s
    };

    let decls = match fvs {
        Some(fvs) => fvs
            .iter()
            .map(|ident| format!("(declare-const {} Int)", encode_ident(ident)))
            .collect::<Vec<_>>()
            .join("\n"),
        None => format!(""),
    };
    let model = match fvs {
        Some(_) => "(get-model)".to_string(),
        None => format!(""),
    };
    format!("{}\n(assert {})\n(check-sat)\n{}\n", decls, c_s, model)
}

pub(super) fn save_smt2(smt_string: String) -> NamedTempFile {
    util::save_to_file(smt_string)
}

struct Z3Solver {}

struct AutoSolver {}

impl AutoSolver {
    fn new() -> AutoSolver {
        AutoSolver {}
    }
}

pub fn smt_solver(s: SMTSolverType) -> Box<dyn SMTSolver> {
    match s {
        SMTSolverType::Z3 => Box::new(Z3Solver {}),
        SMTSolverType::Auto => Box::new(AutoSolver::new()),
        SMTSolverType::CVC => panic!("not supported"),
    }
}

pub fn default_solver() -> Box<dyn SMTSolver> {
    smt_solver(SMTSolverType::Z3)
}

fn z3_solver(smt_string: String) -> String {
    let f = save_smt2(smt_string);
    let args = vec![f.path().to_str().unwrap()];
    // debug
    debug!("filename: {}", &args[0]);

    #[cfg(not(debug_assertions))]
    {
        crate::stat::smt::smt_count();
        crate::stat::smt::start_clock();
    }

    let out = util::exec_with_timeout("z3", &args, Duration::from_secs(1));

    #[cfg(not(debug_assertions))]
    {
        crate::stat::smt::end_clock();
    }

    String::from_utf8(out).unwrap()
}

impl AutoSolver {
    /// Check if satisfiable up to over AutoSolver::MAX_BIT_SIZE bit integers
    const MIN_INT: i64 = -8;
    const MAX_INT: i64 = 8;
    const BIT_SIZE: u32 = 8;

    fn farkas_transform(&self, c: &Constraint, vars: &HashSet<Ident>) -> Constraint {
        use crate::formula::farkas;

        let mut constraint = c.simplify_trivial();
        for var in vars {
            constraint = Constraint::mk_univ_int(*var, constraint);
        }
        debug!("smt::auto_solver quantified: {constraint}");

        // farkas transform
        farkas::farkas_transform(&constraint)
    }

    /// check if the given model is actually a valid model for constraint
    /// by using SMT solver (Model is assumed to be given by SAT solver)
    fn validate(&self, constraint: &Constraint, model: &Model) -> bool {
        let mut constraint = constraint.clone();
        for (var, val) in model.model.iter() {
            constraint = constraint.subst(var, &Op::mk_const(*val));
        }
        let mut sat_solver = smt_solver(SMTSolverType::Z3);
        for fv in constraint.fv() {
            // there is no constraint on fv, so any number is ok to substitute.
            constraint = constraint.subst(&fv, &Op::mk_const(0));
        }
        sat_solver
            .solve_with_model(&constraint, &HashSet::new(), &HashSet::new())
            .is_ok()
    }

    fn add_range_to_fv(constraint: &Constraint, min: i64, max: i64) -> Constraint {
        let fvs = constraint.fv();
        let mut range_constr = Constraint::mk_true();
        let max = Op::mk_const(max);
        let min = Op::mk_const(min);
        for fv in fvs {
            let x = Op::mk_var(fv);
            let c1 = Constraint::mk_geq(max.clone(), x.clone());
            let c2 = Constraint::mk_geq(x.clone(), min.clone());
            let c = Constraint::mk_conj(c1, c2);
            range_constr = Constraint::mk_conj(range_constr, c);
        }
        Constraint::mk_conj(constraint.clone(), range_constr)
    }

    fn solve_by_smt(&self, constraint: &Constraint) -> Result<Model, SolverResult> {
        let c = Self::add_range_to_fv(constraint, -256, 256);
        let mut sat_solver = smt_solver(SMTSolverType::Z3);
        sat_solver.solve_with_model(&c, &HashSet::new(), &c.fv())
    }

    fn solve_inner(&self, constraint: &Constraint) -> Result<Model, SolverResult> {
        debug!("check if {constraint} is sat");
        let mut sat_solver =
            super::sat::SATSolver::default_solver(Self::MIN_INT, Self::MAX_INT, Self::BIT_SIZE);
        let m = sat_solver.solve(&constraint)?;

        if !self.validate(constraint, &m) {
            warn!("failed to solve by sat since bit size is too small");
            let m = self.solve_by_smt(constraint);
            warn!("but smt could make it");
            m
        } else {
            Ok(m)
        }
    }
}

impl SMTSolver for AutoSolver {
    fn solve(&mut self, c: &Constraint, vars: &HashSet<Ident>) -> SolverResult {
        let constraint = self.farkas_transform(c, vars);

        match self.solve_inner(&constraint) {
            Ok(_) => SolverResult::Sat,
            Err(r) => r,
        }
    }
    fn solve_with_model(
        &mut self,
        c: &Constraint,
        vars: &HashSet<Ident>,
        fvs: &HashSet<Ident>,
    ) -> Result<Model, SolverResult> {
        debug!("smt::auto_solver: {c}");
        if c.fv().difference(&vars).next().is_none() {
            let mut sat_solver = smt_solver(SMTSolverType::Z3);
            sat_solver.solve_with_model(c, vars, fvs)
        } else {
            let constraint = self.farkas_transform(c, vars);
            self.solve_inner(&constraint)
        }
    }
}

#[test]
fn test_auto_solver_bug() {
    // ∀x_198: i.∀x_15: i.∀x_14: i.((x_14 != x_15) ∨ ((x_14 + 1) = ((x_195 + (x_196 * x_14)) + (x_197 * x_15)))) ∧ ((x_198 != ((x_195 + (x_196 * x_14)) + (x_197 * x_15))) ∨ (x_198 = x_15))
    use crate::formula::Logic;
    let x_198 = Ident::fresh();
    let x_15 = Ident::fresh();
    let x_14 = Ident::fresh();

    let x_195 = Ident::fresh();
    let x_196 = Ident::fresh();
    let x_197 = Ident::fresh();

    let fvs = vec![x_195, x_196, x_197];

    fn o(x: Ident) -> Op {
        Op::mk_var(x)
    }

    let x_14_neq_x_15 = Constraint::mk_neq(o(x_14), o(x_15));
    let z = Op::mk_add(
        o(x_195),
        Op::mk_add(Op::mk_mul(o(x_196), o(x_14)), Op::mk_mul(o(x_197), o(x_15))),
    );

    let x14p1eqz = Constraint::mk_eq(Op::mk_add(o(x_14), Op::mk_const(1)), z.clone());
    let x198_neq_z = Constraint::mk_neq(o(x_198), z.clone());
    let x198_eq_x15 = Constraint::mk_eq(o(x_198), o(x_15));

    let c1 = Constraint::mk_disj(x_14_neq_x_15, x14p1eqz);
    let c2 = Constraint::mk_disj(x198_neq_z, x198_eq_x15);
    let c = Constraint::mk_conj(c1, c2);

    let c = Constraint::mk_univ_int(x_14, c);
    let c = Constraint::mk_univ_int(x_15, c);
    let c = Constraint::mk_univ_int(x_198, c);

    println!("constraint: {c}");

    let fvs = fvs.into_iter().collect();
    let mut solver = smt_solver(SMTSolverType::Auto);
    match solver.solve_with_model(&c, &HashSet::new(), &fvs) {
        Ok(model) => {
            panic!("test failed. model: \n{}", model)
        }
        Err(_) => (),
    }
}

#[test]
fn test_auto_solver_bug2() {
    // ∀x: i.∀y: i.∀z: i.(y = ((c + (b * y)) + (a * x))) ∧ ((z != ((c + (b * y)) + (a * x))) ∨ (z = y))
    use crate::formula::Logic;
    let x = Ident::fresh();
    let y = Ident::fresh();
    let z = Ident::fresh();
    let a = Ident::fresh();
    let b = Ident::fresh();
    let c = Ident::fresh();
    let vars = [x, y, z].iter().cloned().collect();
    fn o(x: Ident) -> Op {
        Op::mk_var(x)
    }

    let w = Op::mk_add(
        o(c),
        Op::mk_add(Op::mk_mul(o(a), o(x)), Op::mk_mul(o(b), o(y))),
    );

    let c1 = Constraint::mk_eq(w.clone(), o(y));
    let c2 = Constraint::mk_neq(o(z), w.clone());
    let c3 = Constraint::mk_eq(o(z), o(y));
    let c4 = Constraint::mk_disj(c2, c3);
    let c5 = Constraint::mk_conj(c1, c4);
    let mut solver = smt_solver(SMTSolverType::Auto);
    let fvs = [a, b, c].iter().cloned().collect();
    println!("{c5}");
    match solver.solve_with_model(&c5, &vars, &fvs) {
        Ok(_) => (),
        Err(_) => panic!("program error"),
    }
}

impl SMTSolver for Z3Solver {
    fn solve(&mut self, c: &Constraint, vars: &HashSet<Ident>) -> SolverResult {
        debug!("smt_solve: {}", c);
        let fvs = c.fv();
        let fvs = &fvs - vars;
        let smt2 = constraint_to_smt2(c, SMTSolverType::Z3, vars, Some(&fvs));
        debug!("smt2: {}", &smt2);
        let s = z3_solver(smt2);
        debug!("smt_solve result: {:?}", &s);
        if s.starts_with("sat") {
            SolverResult::Sat
        } else if s.starts_with("unsat") {
            SolverResult::Unsat
        } else {
            SolverResult::Unknown
        }
    }
    fn solve_with_model(
        &mut self,
        c: &Constraint,
        vars: &HashSet<Ident>,
        fvs: &HashSet<Ident>,
    ) -> Result<Model, SolverResult> {
        debug!("smt_solve_with_model: {} fvs.len(): {}", c, fvs.len());
        let smt2 = constraint_to_smt2(c, SMTSolverType::Z3, vars, Some(fvs));
        debug!("smt2: {}", &smt2);
        let s = z3_solver(smt2);
        debug!("smt_solve result: {:?}", &s);
        if s.starts_with("sat") {
            let pos = s.find('\n').unwrap();
            Ok(Model::from_z3_model_str(&s[pos..]).unwrap())
        } else if s.starts_with("unsat") {
            Err(SolverResult::Unsat)
        } else {
            Err(SolverResult::Unknown)
        }
    }
}

#[test]
fn z3_sat_model() {
    let s = "(declare-const x_x1 Int)
    (declare-const x_x2 Int)
    (assert (>= x_x1 189))
    (assert (<= (+ x_x1 x_x2) 290))
    (check-sat)
    (get-model)"
        .to_string();
    let r = z3_solver(s);
    debug!("{}", r);
    assert!(r.starts_with("sat"));
    let pos = r.find('\n').unwrap();
    assert!(Model::from_z3_model_str(&r[pos..]).is_ok())
}

#[test]
fn z3_sat_model_from_constraint() {
    use crate::formula::{Logic, PredKind};
    let i1 = Ident::fresh();
    let i2 = Ident::fresh();
    let fvs = HashSet::from([i1, i2]);
    let x1 = Op::mk_var(i1);
    let x2 = Op::mk_var(i2);
    // x1 > x2 /\ x2 = 0
    let c = Constraint::mk_conj(
        Constraint::mk_pred(PredKind::Gt, vec![x1, x2.clone()]),
        Constraint::mk_pred(PredKind::Eq, vec![x2, Op::mk_const(0)]),
    );
    let mut solver = smt_solver(SMTSolverType::Z3);
    match solver.solve_with_model(&c, &HashSet::new(), &fvs) {
        Ok(model) => {
            assert_eq!(model.get(&i2).unwrap(), 0)
        }
        Err(_) => panic!("test failed"),
    }
}
