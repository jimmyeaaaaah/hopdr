use super::smt;
use super::smt::constraint_to_smt2_inner;
use super::smt::ident_2_smt2;
use super::util;
use super::SMT2Style;
use crate::formula::chc;
use crate::formula::fofml;
use crate::formula::pcsp;
use crate::formula::OpKind;
use crate::formula::QuantifierKind;
use crate::formula::Subst;
use crate::formula::{Constraint, Fv, Ident, Logic, Op, PredKind, Top};

use lexpr;
use lexpr::Value;

use std::collections::HashMap;
use std::fmt;
use std::time::Duration;

#[derive(Copy, Clone)]
pub enum CHCStyle {
    Hoice,
    Spacer,
}

pub enum CHCResult {
    Sat(Model),
    Unsat,
    Unknown,
    Timeout,
}

impl CHCResult {
    pub fn is_sat(&self) -> bool {
        match self {
            CHCResult::Sat(_) => true,
            _ => false,
        }
    }
}

type CHC = chc::CHC<Constraint>;

//const PROLOGUE: &'static str =
//   "(set-option :no-simplify-clauses true)\n(set-option :no-inlining true)\n(set-logic HORN)\n";
const PROLOGUE: &'static str = "(set-logic HORN)\n";

fn get_epilogue(style: CHCStyle) -> &'static str {
    match style {
        CHCStyle::Hoice => "(check-sat)\n(get-model)\n",
        CHCStyle::Spacer => {
            "(check-sat-using (then propagate-values qe-light horn))\n(get-model)\n"
        }
    }
}

fn predicate_to_smt2(p: &Ident, args: &[Op]) -> String {
    let mut r = format!("({}", smt::ident_2_smt2(p));
    for arg in args {
        r += " ";
        r += &smt::op_to_smt2(arg);
    }
    r += ")";
    r
}

fn atom_to_smt2(p: &pcsp::Atom) -> String {
    const STYLE: SMT2Style = SMT2Style::Z3;
    match p.kind() {
        pcsp::AtomKind::True => "true".to_string(),
        pcsp::AtomKind::Constraint(c) => constraint_to_smt2_inner(c, STYLE),
        pcsp::AtomKind::Predicate(p, args) => predicate_to_smt2(p, args),
        pcsp::AtomKind::Conj(c1, c2) => format!("(and {} {})", atom_to_smt2(c1), atom_to_smt2(c2)),
        pcsp::AtomKind::Disj(c1, c2) => format!("(or {} {})", atom_to_smt2(c1), atom_to_smt2(c2)),
        pcsp::AtomKind::Quantifier(q, x, c) => format!(
            "({} (({} Int)) {})",
            smt::quantifier_to_smt2(q),
            ident_2_smt2(x),
            atom_to_smt2(c)
        ),
    }
}

fn body_to_smt2(body: &chc::CHCBody<Constraint>) -> String {
    let a = body.clone().into();
    atom_to_smt2(&a)
}

fn chc_to_smt2(chc: &CHC, style: CHCStyle) -> String {
    let mut fvs = chc.body.fv();
    let head_smt2 = match &chc.head {
        chc::CHCHead::Constraint(c) => {
            c.fv_with_vec(&mut fvs);
            smt::constraint_to_smt2_inner(c, SMT2Style::Z3)
        }
        chc::CHCHead::Predicate(a) => {
            for i in a.args.iter() {
                i.fv_with_vec(&mut fvs);
            }
            predicate_to_smt2(&a.predicate, &a.args)
        }
    };
    let body_smt2 = body_to_smt2(&chc.body);

    match style {
        CHCStyle::Hoice => {
            let foralls = fvs
                .iter()
                .map(|x| format!("({} Int)", smt::ident_2_smt2(x)))
                .collect::<Vec<_>>()
                .join(" ");
            format!(
                "(assert (forall ({}) (=> {} {})))",
                foralls, body_smt2, head_smt2
            )
        }
        CHCStyle::Spacer => format!("(assert (=> {} {}))", body_smt2, head_smt2),
    }
}

fn gen_def(id: &Ident, nargs: usize) -> String {
    let arg = if nargs < 1 {
        "".to_string()
    } else if nargs == 1 {
        "Int".to_string()
    } else {
        let mut arg = "Int".to_string();
        for _ in 1..nargs {
            arg += " Int";
        }
        arg
    };
    format!("(declare-fun {} ({}) Bool)", ident_2_smt2(id), arg)
}

fn chcs_to_smt2(chcs: &[CHC], style: CHCStyle) -> String {
    let mut preds = HashMap::new();
    for c in chcs {
        c.collect_predicates(&mut preds);
    }
    let defs = preds
        .into_iter()
        .map(|(id, narg)| gen_def(&id, narg))
        .collect::<Vec<_>>()
        .join("\n");
    let body = chcs
        .iter()
        .map(|c| chc_to_smt2(c, style))
        .collect::<Vec<_>>()
        .join("\n");
    format!("{}{}\n{}\n{}", PROLOGUE, defs, body, get_epilogue(style))
}

pub trait CHCSolver {
    fn solve(&mut self, clauses: &Vec<CHC>) -> CHCResult;
}
struct HoiceSolver {}

pub fn smt_solver(s: CHCStyle) -> Box<dyn CHCSolver> {
    match s {
        CHCStyle::Hoice => Box::new(HoiceSolver {}),
        CHCStyle::Spacer => todo!(),
    }
}

pub fn default_solver() -> Box<dyn CHCSolver> {
    smt_solver(CHCStyle::Hoice)
}

fn hoice_solver(smt_string: String) -> String {
    debug!("hoice_solver: {}", smt_string);
    let f = smt::save_smt2(smt_string);
    let args = vec![f.path().to_str().unwrap()];
    debug!("filename: {}", &args[0]);
    let out = util::exec_with_timeout(
        "../../../hopv/hoice/target/release/hoice",
        //"../../../Hogeyama/hoice/target/debug/hoice",
        &args,
        Duration::from_secs(1),
    );
    String::from_utf8(out).unwrap()
}

pub struct Model {
    pub model: HashMap<Ident, (Vec<Ident>, Constraint)>,
}

impl fmt::Display for Model {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (key, (args, assign)) in self.model.iter() {
            write!(f, "{}(", key)?;
            let mut first = true;
            for arg in args.iter() {
                if first {
                    first = false
                } else {
                    write!(f, ", ")?;
                }
                write!(f, "{}", arg)?;
            }
            write!(f, ") => {}\n", assign)?;
        }
        Ok(())
    }
}

impl Model {
    pub fn new() -> Model {
        Model {
            model: HashMap::new(),
        }
    }
}

fn parse_predicate_variable(v: &str) -> Ident {
    assert!(v.starts_with('x'));
    Ident::from_str(&v[1..]).unwrap_or_else(|| panic!("parse fail"))
}

/*
(define-fun xx_43
    ( (v_0 Int) ) Bool
    true
  )
*/
const ERRMSG: &str = "smt model parse fail";

fn cons_value_to_iter<'a>(v: &'a lexpr::Value) -> impl Iterator<Item = &'a lexpr::Value> {
    v.as_cons()
        .unwrap_or_else(|| panic!("{}({})", ERRMSG, v))
        .iter()
        .map(|x| x.car())
}
fn parse_arg<'a>(v: &'a lexpr::Value) -> &'a str {
    let mut itr = cons_value_to_iter(v);
    let v = itr.next().unwrap_or_else(|| panic!("{}", ERRMSG));
    v.as_symbol().unwrap()
}

fn parse_args<'a>(v: &'a lexpr::Value) -> (Vec<Ident>, HashMap<&'a str, Ident>) {
    if v.is_null() {
        return (Vec::new(), HashMap::new());
    }
    let itr = cons_value_to_iter(v);
    let mut env = HashMap::new();
    let mut args = Vec::new();
    for v in itr {
        let val_name = parse_arg(v);
        let ident = Ident::fresh();
        env.insert(val_name, ident);
        args.push(ident);
    }
    (args, env)
}
fn parse_op_cons(
    v: &lexpr::Cons,
    env: &HashMap<&str, Ident>,
    letenv: &HashMap<&str, &lexpr::Value>,
) -> Op {
    let mut itr = v.iter().map(|x| x.car());
    let p = itr.next().unwrap().as_symbol().unwrap();
    let kind = match p {
        "+" => OpKind::Add,
        "-" => OpKind::Sub,
        "*" => OpKind::Mul,
        "/" => OpKind::Div,
        "%" => OpKind::Mod,
        _ => panic!("failed to handle: {}", p),
    };
    let v: Vec<Op> = itr.map(|x| parse_op(x, env, letenv)).collect();

    if kind == OpKind::Sub && v.len() == 1 {
        match v[0].kind() {
            crate::formula::OpExpr::Const(c) => Op::mk_const(-c),
            crate::formula::OpExpr::Var(_) | crate::formula::OpExpr::Op(_, _, _) => {
                panic!("program error")
            }
        }
    } else {
        debug_assert!(v.len() > 1);
        let mut result = v[0].clone();
        for o in &v[1..] {
            result = Op::mk_bin_op(kind, result, o.clone());
        }
        result
    }
}
fn parse_op(
    v: &lexpr::Value,
    env: &HashMap<&str, Ident>,
    letenv: &HashMap<&str, &lexpr::Value>,
) -> Op {
    match v {
        Value::Cons(x) => parse_op_cons(x, env, letenv),
        Value::Number(n) => Op::mk_const(n.as_i64().unwrap()),
        Value::Symbol(x) => match env.get(x.as_ref()) {
            Some(i) => Op::mk_var(*i),
            None => match letenv.get(x.as_ref()) {
                Some(v) => parse_op(v, env, letenv),
                None => panic!("program error: unknown symbol {}", x),
            },
        },
        Value::Bool(_)
        | Value::Nil
        | Value::Null
        | Value::String(_)
        | Value::Char(_)
        | Value::Keyword(_)
        | Value::Bytes(_)
        | Value::Vector(_) => panic!("program error"),
    }
}
fn parse_let_args<'a>(
    v: &'a lexpr::Value,
    env: &HashMap<&'a str, Ident>,
    letenv: &mut HashMap<&'a str, &'a lexpr::Value>,
) {
    fn parse_let_arg<'a>(
        v: &'a lexpr::Value,
        env: &HashMap<&'a str, Ident>,
        letenv: &mut HashMap<&'a str, &'a lexpr::Value>,
    ) {
        // (.cse0 (+ xx_193 xx_193))
        let mut itr = cons_value_to_iter(&v);
        let var = itr.next().unwrap().as_symbol().unwrap();
        // we assume that variable shadowing does not occur.
        assert!(!(env.contains_key(var) || letenv.contains_key(var)));
        let v = itr.next().unwrap();
        letenv.insert(var, v);
    }
    // ((.cse0 (+ xx_193 xx_193)))
    let itr = cons_value_to_iter(&v);
    for v in itr {
        parse_let_arg(v, env, letenv);
    }
}
fn parse_body_cons<'a>(
    v: &'a lexpr::Cons,
    env: &mut HashMap<&'a str, Ident>,
    letenv: &mut HashMap<&'a str, &'a lexpr::Value>,
) -> fofml::Atom {
    enum Tag {
        Pred(PredKind),
        And,
        Or,
        RightArrow,
        Not,
        Var(Ident),
        Quantifier(QuantifierKind),
        Let,
    }

    let mut itr = v.iter().map(|x| x.car());
    let p = itr.next().unwrap().as_symbol().unwrap();
    let t = match p {
        "<" => Tag::Pred(PredKind::Lt),
        "<=" => Tag::Pred(PredKind::Leq),
        ">" => Tag::Pred(PredKind::Gt),
        ">=" => Tag::Pred(PredKind::Geq),
        "=" => Tag::Pred(PredKind::Eq),
        "!=" => Tag::Pred(PredKind::Neq),
        "=>" => Tag::RightArrow,
        "and" => Tag::And,
        "or" => Tag::Or,
        "not" => Tag::Not,
        "exists" => Tag::Quantifier(QuantifierKind::Existential),
        "forall" => Tag::Quantifier(QuantifierKind::Universal),
        "let" => Tag::Let,
        x => match env.get(x) {
            Some(id) => Tag::Var(*id),
            None => {
                // x_nn can happen since hoice sometimes abbreviate it
                Tag::Var(parse_predicate_variable(x))
            }
        },
    };
    match t {
        Tag::Pred(p) => {
            let v: Vec<Op> = itr.map(|x| parse_op(x, env, letenv)).collect();
            debug_assert!(v.len() == 2); // maybe?
            let c = Constraint::mk_pred(p, v);
            fofml::Atom::mk_constraint(c)
        }
        Tag::And => {
            let mut r = fofml::Atom::mk_true();
            for a in itr.map(|x| parse_body_inner(x, env, letenv)) {
                r = fofml::Atom::mk_conj(r, a);
            }
            r
        }
        Tag::Or => {
            let mut r = fofml::Atom::mk_false();
            for a in itr.map(|x| parse_body_inner(x, env, letenv)) {
                r = fofml::Atom::mk_disj(r, a);
            }
            r
        }
        Tag::RightArrow => {
            let r: Vec<fofml::Atom> = itr.map(|x| parse_body_inner(x, env, letenv)).collect();
            debug_assert!(r.len() == 2);
            let a = r[0].clone();
            let b = r[1].clone();
            fofml::Atom::mk_disj(fofml::Atom::mk_not(a), b)
        }
        Tag::Not => {
            let r: Vec<fofml::Atom> = itr.map(|x| parse_body_inner(x, env, letenv)).collect();
            debug_assert!(r.len() == 1);
            let a = r[0].clone();
            fofml::Atom::mk_not(a)
        }
        Tag::Var(p) => {
            let l: Vec<Op> = itr.map(|x| parse_op(x, env, letenv)).collect();
            fofml::Atom::mk_pred(p, l)
        }
        Tag::Quantifier(q) => {
            //  (exists ( (v_1 Int) ) (xx_255 v_1 v_0 v_1))
            let args = itr.next().unwrap();
            let (args, env2) = parse_args(args);
            for (k, i) in env2.iter() {
                let r = env.insert(k, *i);
                debug_assert!(r.is_none());
            }

            let r: Vec<fofml::Atom> = itr.map(|x| parse_body_inner(x, env, letenv)).collect();
            debug_assert!(r.len() == 1);

            for (k, _) in env2.iter() {
                let r = env.remove(k);
                debug_assert!(r.is_some());
            }
            let mut a = r[0].clone();
            for p in args {
                a = fofml::Atom::mk_quantifier(q, p, a);
            }
            a
        }
        Tag::Let => {
            // (let ((.cse0 (+ xx_193 xx_193))) (and (>= .cse0 0) (>= 0 .cse0)))
            let args = itr.next().unwrap();
            parse_let_args(args, env, letenv);
            let r: Vec<fofml::Atom> = itr.map(|x| parse_body_inner(x, env, letenv)).collect();
            debug_assert!(r.len() == 1);
            r[0].clone()
        }
    }
}

/* Cons((Symbol("let") . Cons((Cons((Cons((Symbol(".cse0") . Cons((Cons((Symbol("and") . Cons((Cons((Symbol("<=") . Cons((Symbol("xx_113") . Cons((Symbol("xx_113") . Null)))))) . Cons((Cons((Symbol("or") . Cons((Cons((Symbol("<") . Cons((Symbol("xx_113") . Cons((Symbol("xx_113") . Null)))))) . Cons((Cons((Symbol("=") . Cons((Symbol("xx_113") . Cons((Symbol("xx_112") . Null)))))) . Null)))))) . Null)))))) . Null)))) . Null)) . Cons((Cons((Symbol("and") . Cons((Cons((Symbol("or") . Cons((Cons((Symbol("<=") . Cons((Symbol("xx_113") . Cons((Number(PosInt(0)) . Null)))))) . Cons((Symbol(".cse0") . Null)))))) . Cons((Cons((Symbol("or") . Cons((Cons((Symbol("<=") . Cons((Number(PosInt(0)) . Cons((Symbol("xx_113") . Null)))))) . Cons((Symbol(".cse0") . Null)))))) . Cons((Cons((Symbol("or") . Cons((Cons((Symbol("=") . Cons((Number(PosInt(0)) . Cons((Symbol("xx_112") . Null)))))) . Cons((Symbol(".cse0") . Null)))))) . Null)))))))) . Null)))))) */
// parse
fn parse_body_inner<'a>(
    v: &'a lexpr::Value,
    env: &mut HashMap<&'a str, Ident>,
    letenv: &mut HashMap<&'a str, &'a lexpr::Value>,
) -> fofml::Atom {
    debug!("parse_body: {}", v);
    match v {
        Value::Bool(t) if *t => fofml::Atom::mk_true(),
        Value::Bool(_) => fofml::Atom::mk_false(),
        Value::Cons(v) => parse_body_cons(v, env, letenv),
        // Value::Symbol(x) => {
        //     match env.get(x) {
        //         Some(ident) => pcsp::Atom::mk_
        //     }
        // },
        Value::Symbol(s) => {
            if s.as_ref() == "true" {
                fofml::Atom::mk_true()
            } else if s.as_ref() == "false" {
                fofml::Atom::mk_false()
            } else {
                match letenv.get(s.as_ref()) {
                    Some(v) => parse_body_inner(v, env, letenv),
                    None => panic!("program error: unknown variable {}", s),
                }
            }
        }
        // this also should not happen in parsing constraint
        Value::Number(_) => panic!("program error"),
        Value::Nil
        | Value::Null
        | Value::String(_)
        | Value::Char(_)
        | Value::Keyword(_)
        | Value::Bytes(_)
        | Value::Vector(_) => panic!("program error"),
    }
}
pub fn parse_body<'a>(v: &'a lexpr::Value, env: &mut HashMap<&'a str, Ident>) -> fofml::Atom {
    let mut letenv = HashMap::new();
    parse_body_inner(v, env, &mut letenv)
}

#[test]
fn test_parse_body_let() {
    use fofml::Atom;
    let s = "(let ((.cse0 (+ xx_193 xx_193))) (and (>= .cse0 0) (>= 0 .cse0)))";
    let x = lexpr::from_str(s).unwrap();
    let mut env = HashMap::new();
    let i = Ident::fresh();
    env.insert("xx_193", i);
    let a = parse_body(&x, &mut env);
    let o = Op::mk_bin_op(OpKind::Add, Op::mk_var(i), Op::mk_var(i));
    let c1 = Atom::mk_constraint(Constraint::mk_geq(o.clone(), Op::mk_const(0)));
    let c2 = Atom::mk_constraint(Constraint::mk_geq(Op::mk_const(0), o.clone()));
    let b = Atom::mk_conj(c1, c2);
    assert_eq!(a, b);

    let s = "(let ((.cse0 (= xx_193 0))) (and .cse0 (>= 0 xx_193)))";
    let x = lexpr::from_str(s).unwrap();
    let a = parse_body(&x, &mut env);
    let o = Op::mk_var(i);
    let c1 = Atom::mk_constraint(Constraint::mk_eq(o.clone(), Op::mk_const(0)));
    let c2 = Atom::mk_constraint(Constraint::mk_geq(Op::mk_const(0), o.clone()));
    let b = Atom::mk_conj(c1, c2);
    assert_eq!(a, b);

    let s = "(let ((.cse1 (= x 0))) (let ((.cse0 (let ((.cse2 (= (+ x (- 1)) 0)) (.cse3 (+ x 1))) (and (=> .cse2 (=> (not (= x 0)) (and (<= .cse3 .cse3) (or (< .cse3 .cse3) (= x (+ x 2)))))) (=> (not .cse2) (and (<= x x) (or (< x x) (= x .cse3)))) (not .cse1))))) (and (or (= x x) .cse0) (or .cse1 .cse0))))";
    env.insert("x", i);
    let x = lexpr::from_str(s).unwrap();
    parse_body(&x, &mut env);
}

pub fn parse_define_fun(v: lexpr::Value) -> (Ident, (Vec<Ident>, fofml::Atom)) {
    let mut itr = cons_value_to_iter(&v);
    let v = itr.next().unwrap_or_else(|| panic!("{}", ERRMSG));
    debug_assert_eq!(v.as_symbol().unwrap(), "define-fun");

    let x = itr.next().unwrap_or_else(|| panic!("{}", ERRMSG));
    let v = x.as_symbol().unwrap_or_else(|| panic!("{}", ERRMSG));
    let ident = parse_predicate_variable(v);

    // args
    let v = itr.next().unwrap_or_else(|| panic!("{}", ERRMSG));
    let (args, mut env) = parse_args(v);

    // Bool
    let v = itr.next().unwrap_or_else(|| panic!("{}", ERRMSG));
    debug_assert_eq!(v.as_symbol().unwrap(), "Bool");

    // body of the predicate
    let v = itr.next().unwrap_or_else(|| panic!("{}", ERRMSG));
    let body = parse_body(v, &mut env);

    // ident(args) = body
    (ident, (args, body))
}
fn reduce_application(
    mut model: HashMap<Ident, (Vec<Ident>, fofml::Atom)>,
) -> HashMap<Ident, (Vec<Ident>, Constraint)> {
    type E = HashMap<Ident, (Vec<Ident>, fofml::Atom)>;
    use fofml::{Atom, AtomKind};
    fn reduce(a: &Atom, env: &E) -> (bool, Atom) {
        match a.kind() {
            AtomKind::Predicate(p, l) => match env.get(p) {
                Some((args, a)) => {
                    let a = a.subst_multi(args.iter().zip(l.iter()).map(|(x, y)| (*x, y.clone())));
                    (true, a)
                }
                None => panic!("failed to handle the model from hoice"),
            },
            AtomKind::Conj(a1, a2) => {
                let (flag1, a1) = reduce(a1, env);
                let (flag2, a2) = reduce(a2, env);
                (flag1 || flag2, Atom::mk_conj(a1, a2))
            }
            AtomKind::Disj(a1, a2) => {
                let (flag1, a1) = reduce(a1, env);
                let (flag2, a2) = reduce(a2, env);
                (flag1 || flag2, Atom::mk_disj(a1, a2))
            }
            AtomKind::Not(a) => {
                let (flag, a) = reduce(a, env);
                (flag, Atom::mk_not(a))
            }
            AtomKind::Quantifier(q, x, a) => {
                let (flag, a) = reduce(a, env);
                (flag, Atom::mk_quantifier(*q, *x, a))
            }
            AtomKind::True | AtomKind::Constraint(_) => (false, a.clone()),
        }
    }
    let mut continue_flag = true;
    while continue_flag {
        continue_flag = false;
        let mut new_model = HashMap::new();
        for (k, (l, a)) in model.iter() {
            debug!("old: {} ", a);
            let (flag, a) = reduce(a, &model);
            debug!("new: {} ", a);
            continue_flag |= flag;
            new_model.insert(*k, (l.clone(), a));
        }
        model = new_model;
    }
    // Now models do not contain any predicate, so we can translate them to
    // Constraint
    model
        .into_iter()
        .map(|(k, (l, a))| (k, (l, a.into())))
        .collect()
}
impl Model {
    fn parse_hoice_model(model_str: &str) -> Result<Model, lexpr::parse::Error> {
        debug!("{}", model_str);
        let x = lexpr::from_str(model_str)?;
        let model: HashMap<Ident, (Vec<Ident>, fofml::Atom)> = match x {
            Value::Cons(x) => x
                .into_iter()
                .skip(1)
                .map(|(v, _)| parse_define_fun(v))
                .collect(),
            _ => panic!("parse error: smt2 model: {}", model_str),
        };
        let model = reduce_application(model);

        Ok(Model { model })
    }
}
#[test]
fn test_parse_model() {
    let model = "(model
        (define-fun xx_43
          ( (v_0 Int) ) Bool
          true
        )
        (define-fun xx_42
          ( (v_0 Int) (v_1 Int) ) Bool
          (and (= (+ (* (- 1) v_0) v_1) 0) (>= (* (- 1) v_1) 0))
        )
      )";
    match Model::parse_hoice_model(model) {
        Ok(m) => {
            assert!(m.model.len() == 2);
        }
        Err(_) => panic!("model is broken"),
    }
}

impl CHCSolver for HoiceSolver {
    fn solve(&mut self, clauses: &Vec<CHC>) -> CHCResult {
        let smt2 = chcs_to_smt2(clauses, CHCStyle::Hoice);
        debug!("smt2: {}", &smt2);
        let s = hoice_solver(smt2);
        debug!("smt_solve result: {:?}", &s);
        if s.starts_with("sat") {
            let m = Model::parse_hoice_model(&s[4..]).unwrap();
            CHCResult::Sat(m)
        } else if s.starts_with("unsat") {
            CHCResult::Unsat
        } else {
            CHCResult::Unknown
        }
    }
}
