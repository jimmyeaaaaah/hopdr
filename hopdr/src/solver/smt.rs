use tempfile::NamedTempFile;

use std::collections::{HashMap, HashSet};
use std::time::Duration;

use super::util;
use crate::formula::{
    Constraint, ConstraintExpr, Ident, Op, OpExpr, OpKind, PredKind, QuantifierKind,
};
use lexpr;
use lexpr::Value;

#[derive(Debug)]
pub enum SMTResult {
    Sat,
    Unsat,
    Unknown,
    Timeout,
}

#[derive(Debug)]
pub struct Model {
    model: HashMap<Ident, i64>,
}

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

#[derive(Copy, Clone)]
pub enum SMT2Style {
    Z3,
}

pub trait SMTSolver {
    fn solve(&mut self, c: &Constraint, vars: &HashSet<Ident>) -> SMTResult;
    fn solve_with_model(
        &mut self,
        c: &Constraint,
        vars: &HashSet<Ident>,
        fvs: &HashSet<Ident>,
    ) -> Result<Model, SMTResult>;
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

fn ident_2_smt2(ident: &Ident) -> String {
    encode_ident(ident)
}

fn op_to_smt2(op: &Op) -> String {
    match op.kind() {
        OpExpr::Op(opkind, o1, o2) => {
            let o1 = op_to_smt2(o1);
            let o2 = op_to_smt2(o2);
            let k = opkind_2_smt2(opkind);
            format!("({} {} {})", k, o1, o2)
        }
        OpExpr::Var(x) => ident_2_smt2(x),
        OpExpr::Const(c) => format!("{}", c),
    }
}

fn quantifier_to_smt2(q: &QuantifierKind) -> &'static str {
    match q {
        QuantifierKind::Existential => "exists",
        QuantifierKind::Universal => "forall",
    }
}

fn constraint_to_smt2_inner(c: &Constraint, style: SMT2Style) -> String {
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
    style: SMT2Style,
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

fn save_smt2(smt_string: String) -> NamedTempFile {
    util::save_to_file(smt_string)
}

struct Z3Solver {}

pub fn smt_solver(s: SMT2Style) -> Box<dyn SMTSolver> {
    match s {
        SMT2Style::Z3 => Box::new(Z3Solver {}),
    }
}

pub fn default_solver() -> Box<dyn SMTSolver> {
    smt_solver(SMT2Style::Z3)
}

fn z3_solver(smt_string: String) -> String {
    let f = save_smt2(smt_string);
    let args = vec![f.path().to_str().unwrap()];
    // debug
    debug!("filename: {}", &args[0]);
    let out = util::exec_with_timeout("z3", &args, Duration::from_secs(1));
    String::from_utf8(out).unwrap()
}

impl SMTSolver for Z3Solver {
    fn solve(&mut self, c: &Constraint, vars: &HashSet<Ident>) -> SMTResult {
        debug!("smt_solve: {}", c);
        let smt2 = constraint_to_smt2(c, SMT2Style::Z3, vars, None);
        debug!("smt2: {}", &smt2);
        let s = z3_solver(smt2);
        debug!("smt_solve result: {:?}", &s);
        if s.starts_with("sat") {
            SMTResult::Sat
        } else if s.starts_with("unsat") {
            SMTResult::Unsat
        } else {
            SMTResult::Unknown
        }
    }
    fn solve_with_model(
        &mut self,
        c: &Constraint,
        vars: &HashSet<Ident>,
        fvs: &HashSet<Ident>,
    ) -> Result<Model, SMTResult> {
        debug!("smt_solve_with_model: {} {}", c, fvs.len());
        let smt2 = constraint_to_smt2(c, SMT2Style::Z3, vars, Some(fvs));
        debug!("smt2: {}", &smt2);
        let s = z3_solver(smt2);
        debug!("smt_solve result: {:?}", &s);
        if s.starts_with("sat") {
            let pos = s.find('\n').unwrap();
            Ok(Model::from_z3_model_str(&s[pos..]).unwrap())
        } else if s.starts_with("unsat") {
            Err(SMTResult::Unsat)
        } else {
            Err(SMTResult::Unknown)
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
    let mut solver = smt_solver(SMT2Style::Z3);
    match solver.solve_with_model(&c, &HashSet::new(), &fvs) {
        Ok(model) => {
            assert_eq!(model.get(&i2).unwrap(), 0)
        }
        Err(_) => panic!("test failed"),
    }
}
