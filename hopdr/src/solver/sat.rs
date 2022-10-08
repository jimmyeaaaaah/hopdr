use std::collections::{HashMap, HashSet};
use std::time::Duration;

use super::smt::{ident_2_smt2, save_smt2};
use super::util;
use super::{Model, SolverResult};
use crate::formula::{Constraint, ConstraintExpr, Ident, Op, OpExpr, OpKind, PredKind};
use lexpr;
use lexpr::Value;

fn parse_variable(v: &str) -> Ident {
    assert!(v.starts_with('x'));
    Ident::from_str(&v[1..]).unwrap_or_else(|| panic!("parse fail"))
}

fn parse_declare_fun(v: lexpr::Value, bit_size: u32) -> (Ident, i64) {
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

    let x = x.as_u64().unwrap();
    let v = if x >= 2u64.pow(bit_size - 1) {
        let c = 64 - bit_size;
        let x = !x << c;
        let x = x >> c;
        -(x as i64) - 1
    } else {
        x as i64
    };
    (ident, v)
}

impl Model {
    fn from_z3_sat_model_str(s: &str, bit_size: u32) -> Result<Model, lexpr::parse::Error> {
        let x = lexpr::from_str(s)?;
        let model: HashMap<Ident, i64> = match x {
            Value::Cons(x) => x
                .into_iter()
                .skip(1)
                .map(|(v, _)| parse_declare_fun(v, bit_size))
                .collect(),
            _ => panic!("parse error: smt2 model: {}", s),
        };
        Ok(Model { model })
    }
}

#[test]
fn z3_parse_model() {
    let model = "(model
        (define-fun x_x1 () (_ BitVec 32)
        #xffffffff)
        (define-fun x_x2 () (_ BitVec 32)
        #x00000001)
    )";
    match Model::from_z3_sat_model_str(model, 32) {
        Ok(m) => {
            let x1 = m.get(&1.into()).unwrap();
            let x2 = m.get(&2.into()).unwrap();
            assert_eq!(x1, -1);
            assert_eq!(x2, 1);
        }
        Err(_) => panic!("model is broken"),
    }
}

#[derive(Clone, Copy)]
pub enum Solver {
    Z3,
}
pub struct SATSolver {
    bit_size: u32,
    solver: Solver,
    integer_min: i64,
    integer_max: i64,
}

impl SATSolver {
    pub fn default_solver(integer_min: i64, integer_max: i64, bit_size: u32) -> Self {
        Self {
            bit_size,
            integer_min,
            integer_max,
            solver: Solver::Z3,
        }
    }
    fn z3_solver(&mut self, smt_string: String) -> String {
        let f = save_smt2(smt_string);
        let args = vec![f.path().to_str().unwrap()];
        // debug
        debug!("filename: {}", &args[0]);

        crate::stat::smt::smt_count();
        crate::stat::smt::start_clock();

        let out = util::exec_with_timeout("z3", &args, Duration::from_secs(1));

        crate::stat::smt::end_clock();

        String::from_utf8(out).unwrap()
    }
    /// Given a constraint, the solver executes an SMT solver to check whether
    /// it is satisfiable or not.
    ///
    /// - constraint: The constraint to be checked by SMT solver
    /// - vars: variables to be bound by universal quantifiers.
    pub fn solve(&mut self, c: &Constraint) -> Result<Model, SolverResult> {
        use crate::formula::Fv;
        debug!("smt_solve: {}", c);
        let fvs = c.fv();
        let smt2 = self.constraint_to_smt2(c, &fvs);
        debug!("smt2: {}", &smt2);
        let s = match self.solver {
            Solver::Z3 => self.z3_solver(smt2),
        };
        debug!("smt_solve result: {:?}", &s);
        if s.starts_with("sat") {
            let pos = s.find('\n').unwrap();
            Ok(Model::from_z3_sat_model_str(&s[pos..], self.bit_size).unwrap())
        } else if s.starts_with("unsat") {
            Err(SolverResult::Unsat)
        } else {
            Err(SolverResult::Unknown)
        }
    }
    fn decl_range(&mut self, decl_vars: &HashSet<Ident>) -> String {
        let c_s = decl_vars
            .iter()
            .map(|x| {
                let x = &ident_2_smt2(x);
                let min = self.int_2_smt2(self.integer_min);
                let max = self.int_2_smt2(self.integer_max);
                format!("(bvsle {min} {x}) (bvsle {x} {max})")
            })
            .collect::<Vec<_>>()
            .join("");
        format!("(and {c_s})")
    }
    fn constraint_to_smt2(&mut self, c: &Constraint, fvs: &HashSet<Ident>) -> String {
        let c_s = self.constraint_to_smt2_inner(c);

        let decls = fvs
            .iter()
            .map(|ident| {
                format!(
                    "(declare-const {} (_ BitVec {}))",
                    ident_2_smt2(ident),
                    self.bit_size
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        let decl_range = self.decl_range(fvs);

        format!(
            "(set-logic QF_BV)\n{decls}\n(assert {decl_range}) (assert {c_s})\n(check-sat)\n(get-model)\n"
        )
    }
    fn constraint_to_smt2_inner(&mut self, c: &Constraint) -> String {
        match c.kind() {
            ConstraintExpr::True => "true".to_string(),
            ConstraintExpr::False => "false".to_string(),
            ConstraintExpr::Pred(p, l) => {
                let args = l.iter().map(|op| self.op_to_smt2(op)).collect::<Vec<_>>();
                self.pred_to_smt2(p, &args)
            }
            ConstraintExpr::Conj(c1, c2) => format!(
                "(and {} {})",
                self.constraint_to_smt2_inner(c1),
                self.constraint_to_smt2_inner(c2)
            ),
            ConstraintExpr::Disj(c1, c2) => format!(
                "(or {} {})",
                self.constraint_to_smt2_inner(c1),
                self.constraint_to_smt2_inner(c2)
            ),
            ConstraintExpr::Quantifier(_, _, _) => {
                panic!("quantifier is not supported for SAT(QF_BV)")
            }
        }
    }
    fn int_2_smt2(&mut self, v: i64) -> String {
        if v >= 0 {
            format!("(_ bv{} {})", v, self.bit_size)
        } else {
            format!("(bvneg (_ bv{} {}))", -v, self.bit_size)
        }
    }

    fn op_to_smt2(&mut self, op: &Op) -> String {
        match op.kind() {
            OpExpr::Op(opkind, o1, o2) => {
                let o1 = self.op_to_smt2(o1);
                let o2 = self.op_to_smt2(o2);
                let k = self.opkind_2_smt2(opkind);
                format!("({} {} {})", k, o1, o2)
            }
            OpExpr::Var(x) => ident_2_smt2(x),
            OpExpr::Const(c) => format!("{}", self.int_2_smt2(*c)),
            OpExpr::Ptr(_, o) => self.op_to_smt2(o),
        }
    }

    fn pred_to_smt2(&mut self, p: &PredKind, args: &[String]) -> String {
        let args = args.join(" ");
        match p {
            PredKind::Eq => format!("(= {})", args),
            PredKind::Neq => format!("(not (= {}))", args),
            PredKind::Lt => format!("(bvslt {})", args),
            PredKind::Leq => format!("(bvsle {})", args),
            PredKind::Gt => format!("(bvsgt {})", args),
            PredKind::Geq => format!("(bvsge {})", args),
        }
    }

    fn opkind_2_smt2(&mut self, o: &OpKind) -> &'static str {
        match o {
            OpKind::Add => "bvadd",
            OpKind::Sub => "bvsub",
            OpKind::Mul => "bvmul",
            OpKind::Div => "bvsdiv",
            OpKind::Mod => "bvsrem",
        }
    }
}

#[test]
fn z3_sat_model() {
    let bit_size = 32;
    let s = "
    (declare-const x_x1 (_ BitVec 32))
    (declare-const x_x2 (_ BitVec 32))

    (assert (and (= (bvadd x_x1 x_x2) (_ bv0 32)) (not (= x_x1 (_ bv0 32)))))
    (check-sat)
    (get-model)"
        .to_string();
    let mut sol = SATSolver::default_solver(-256, 256, bit_size);
    let r = sol.z3_solver(s);
    debug!("{}", r);
    assert!(r.starts_with("sat"));
    let pos = r.find('\n').unwrap();
    assert!(Model::from_z3_sat_model_str(&r[pos..], bit_size).is_ok())
}

#[test]
fn z3_sat_model_from_constraint() {
    use crate::formula::{Logic, PredKind};

    let bit_size = 32;

    let i1 = Ident::fresh();
    let i2 = Ident::fresh();
    let x1 = Op::mk_var(i1);
    let x2 = Op::mk_var(i2);
    // x1 > x2 /\ x2 = 0
    let c = Constraint::mk_conj(
        Constraint::mk_pred(PredKind::Gt, vec![x1, x2.clone()]),
        Constraint::mk_pred(PredKind::Eq, vec![x2, Op::mk_const(0)]),
    );
    let mut solver = SATSolver::default_solver(-256, 256, bit_size);
    match solver.solve(&c) {
        Ok(model) => {
            assert_eq!(model.get(&i2).unwrap(), 0)
        }
        Err(_) => panic!("test failed"),
    }
}
