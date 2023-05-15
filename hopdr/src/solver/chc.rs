use super::smt;
use super::smt::constraint_to_smt2_inner;
use super::smt::ident_2_smt2;
use super::util;
use super::SMTSolverType;
use crate::formula::chc;
use crate::formula::chc::Model;
use crate::formula::fofml;
use crate::formula::pcsp;
use crate::formula::OpKind;
use crate::formula::QuantifierKind;
use crate::formula::Subst;
use crate::formula::{Constraint, Fv, Ident, Logic, Op, PredKind, Top};

use lexpr;
use lexpr::Value;
use rpds::Stack;

use std::collections::HashMap;
use std::time::Duration;

#[derive(Copy, Clone)]
pub enum CHCStyle {
    Hoice,
    HoiceNoSimplify,
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
        matches!(self, CHCResult::Sat(_))
    }
}

type CHC = chc::CHC<chc::Atom, Constraint>;

const PROLOGUE: &str = "(set-logic HORN)\n";
const PROLOGUE_FOR_NO_SIMPLIFY: &str = "(set-option :no-inlining true)\n";

fn get_prologue(style: CHCStyle) -> String {
    match style {
        CHCStyle::Hoice | CHCStyle::Spacer => PROLOGUE.to_string(),
        CHCStyle::HoiceNoSimplify => format!("{}{}", PROLOGUE, PROLOGUE_FOR_NO_SIMPLIFY),
    }
}

fn get_epilogue(style: CHCStyle) -> &'static str {
    match style {
        CHCStyle::Hoice | CHCStyle::HoiceNoSimplify => "(check-sat)\n(get-model)\n",
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
    const STYLE: SMTSolverType = SMTSolverType::Z3;
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

fn body_to_smt2(body: &chc::CHCBody<chc::Atom, Constraint>) -> String {
    let a = body.clone().into();
    atom_to_smt2(&a)
}

fn chc_to_smt2(chc: &CHC, style: CHCStyle) -> String {
    let mut fvs = chc.body.fv();
    let head_smt2 = match &chc.head {
        chc::CHCHead::Constraint(c) => {
            c.fv_with_vec(&mut fvs);
            smt::constraint_to_smt2_inner(c, SMTSolverType::Z3)
        }
        chc::CHCHead::Predicate(a) => {
            for i in a.args.iter() {
                i.fv_with_vec(&mut fvs);
            }
            predicate_to_smt2(&a.predicate, &a.args)
        }
    };
    let body_smt2 = body_to_smt2(&chc.body);

    let foralls = fvs
        .iter()
        .map(|x| format!("({} Int)", smt::ident_2_smt2(x)))
        .collect::<Vec<_>>();
    match style {
        CHCStyle::Spacer if foralls.len() == 0 => {
            format!("(assert (=> {} {}))", body_smt2, head_smt2)
        }
        CHCStyle::Hoice | CHCStyle::HoiceNoSimplify | CHCStyle::Spacer => {
            let foralls = foralls.join(" ");
            format!(
                "(assert (forall ({}) (=> {} {})))",
                foralls, body_smt2, head_smt2
            )
        }
    }
}

fn gen_def(id: &Ident, nargs: usize) -> String {
    let arg = match nargs.cmp(&1) {
        std::cmp::Ordering::Less => "".to_string(),
        std::cmp::Ordering::Equal => "Int".to_string(),
        std::cmp::Ordering::Greater => {
            let mut arg = "Int".to_string();
            for _ in 1..nargs {
                arg += " Int";
            }
            arg
        }
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
    format!(
        "{}{}\n{}\n{}",
        get_prologue(style),
        defs,
        body,
        get_epilogue(style)
    )
}

pub trait CHCSolver {
    fn solve(&mut self, clauses: &[CHC]) -> CHCResult;
}
struct HoiceSolver {
    style: CHCStyle,
}

pub struct SpacerSolver {
    style: CHCStyle,
    interpolation: bool,
}

impl SpacerSolver {
    pub fn new() -> SpacerSolver {
        SpacerSolver {
            style: CHCStyle::Spacer,
            interpolation: false,
        }
    }
    pub fn interpolation(mut self, flag: bool) -> SpacerSolver {
        self.interpolation = flag;
        self
    }
}

pub fn chc_solver(style: CHCStyle) -> Box<dyn CHCSolver> {
    match style {
        CHCStyle::Hoice => Box::new(HoiceSolver { style }),
        CHCStyle::HoiceNoSimplify => Box::new(HoiceSolver { style }),
        CHCStyle::Spacer => Box::new(SpacerSolver::new()),
    }
}

pub fn default_solver() -> Box<dyn CHCSolver> {
    chc_solver(CHCStyle::Hoice)
}

pub fn interpolating_solver() -> Box<dyn CHCSolver> {
    chc_solver(CHCStyle::Spacer)
}

macro_rules! chc_execution {
    ( $b:block ) => {{
        crate::stat::chc::count();
        use std::time::Instant;
        let now = Instant::now();

        let out = $b;

        let duration = now.elapsed();
        crate::stat::chc::total_time(duration);
        out
    }};
}

fn hoice_solver(smt_string: String) -> String {
    debug!("hoice_solver: {}", smt_string);
    let f = smt::save_smt2(smt_string);
    let args = vec![f.path().to_str().unwrap()];
    debug!("filename: {}", &args[0]);
    // TODO: determine the path when it's compiled
    let out = chc_execution!({ util::exec_with_timeout("hoice", &args, Duration::from_secs(1),) });
    String::from_utf8(out).unwrap()
}

#[derive(Clone, Debug)]
struct LetEntry<'a> {
    id: &'a str,
    env: LetEnv<'a>,
    expr: &'a lexpr::Value,
}

#[derive(Clone, Debug)]
struct LetEnv<'a> {
    entries: Stack<LetEntry<'a>>,
}

impl<'a> LetEnv<'a> {
    fn new() -> LetEnv<'a> {
        LetEnv {
            entries: Stack::new(),
        }
    }
    fn add(&self, id: &'a str, env: LetEnv<'a>, expr: &'a lexpr::Value) -> LetEnv<'a> {
        let entry = LetEntry { id, env, expr };
        LetEnv {
            entries: self.entries.push(entry),
        }
    }
    fn search(self, id: &str) -> Option<(LetEnv<'a>, &'a lexpr::Value)> {
        for v in self.entries.iter() {
            if v.id == id {
                return Some((v.env.clone(), v.expr));
            }
        }
        None
    }
}

fn parse_predicate_variable(v: &str) -> Ident {
    assert!(v.starts_with('x'));
    Ident::parse_ident(&v[1..]).unwrap_or_else(|| panic!("parse fail"))
}

/*
(define-fun xx_43
    ( (v_0 Int) ) Bool
    true
  )
*/
const ERRMSG: &str = "smt model parse fail";

fn cons_value_to_iter(v: &lexpr::Value) -> impl Iterator<Item = &lexpr::Value> {
    v.as_cons()
        .unwrap_or_else(|| panic!("{}({})", ERRMSG, v))
        .iter()
        .map(|x| x.car())
}
fn parse_arg(v: &lexpr::Value) -> &str {
    let mut itr = cons_value_to_iter(v);
    let v = itr.next().unwrap_or_else(|| panic!("{}", ERRMSG));
    v.as_symbol().unwrap()
}

fn parse_args(v: &lexpr::Value) -> (Vec<Ident>, HashMap<&str, Ident>) {
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
fn parse_op_cons(v: &lexpr::Cons, env: &HashMap<&str, Ident>, letenv: LetEnv) -> Op {
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
    let v: Vec<Op> = itr.map(|x| parse_op(x, env, letenv.clone())).collect();

    if kind == OpKind::Sub && v.len() == 1 {
        match v[0].kind() {
            crate::formula::OpExpr::Const(c) => Op::mk_const(-c),
            crate::formula::OpExpr::Var(_)
            | crate::formula::OpExpr::Op(_, _, _)
            | crate::formula::OpExpr::Ptr(_, _) => {
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
fn parse_op(v: &lexpr::Value, env: &HashMap<&str, Ident>, letenv: LetEnv) -> Op {
    match v {
        Value::Cons(x) => parse_op_cons(x, env, letenv),
        Value::Number(n) => Op::mk_const(n.as_i64().unwrap()),
        Value::Symbol(x) => match env.get(x.as_ref()) {
            Some(i) => Op::mk_var(*i),
            None => match letenv.search(x.as_ref()) {
                Some((letenv, v)) => parse_op(v, env, letenv.clone()),
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
    mut letenv: LetEnv<'a>,
) -> LetEnv<'a> {
    fn parse_let_arg<'a>(
        v: &'a lexpr::Value,
        env: &HashMap<&'a str, Ident>,
        letenv: LetEnv<'a>,
    ) -> LetEnv<'a> {
        // (.cse0 (+ xx_193 xx_193))
        let mut itr = cons_value_to_iter(v);
        let var = itr.next().unwrap().as_symbol().unwrap();
        // we assume that variable shadowing does not occur.
        assert!(!(env.contains_key(var)));
        let v = itr.next().unwrap();
        letenv.add(var, letenv.clone(), v)
    }
    // ((.cse0 (+ xx_193 xx_193)))
    let itr = cons_value_to_iter(v);
    for v in itr {
        letenv = parse_let_arg(v, env, letenv);
    }
    letenv
}
fn parse_body_cons<'a>(
    v: &'a lexpr::Cons,
    env: &mut HashMap<&'a str, Ident>,
    letenv: LetEnv<'a>,
) -> fofml::Atom {
    enum Tag {
        Pred(PredKind),
        And,
        Or,
        RightArrow,
        Not,
        ITE, // if-then-else
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
        "ite" => Tag::ITE,
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
            let v: Vec<Op> = itr.map(|x| parse_op(x, env, letenv.clone())).collect();
            debug_assert!(v.len() == 2); // maybe?
            let c = Constraint::mk_bin_pred(p, v[0].clone(), v[1].clone());
            fofml::Atom::mk_constraint(c)
        }
        Tag::And => {
            let mut r = fofml::Atom::mk_true();
            for a in itr.map(|x| parse_body_inner(x, env, letenv.clone())) {
                r = fofml::Atom::mk_conj(r, a);
            }
            r
        }
        Tag::Or => {
            let mut r = fofml::Atom::mk_false();
            for a in itr.map(|x| parse_body_inner(x, env, letenv.clone())) {
                r = fofml::Atom::mk_disj(r, a);
            }
            r
        }
        Tag::RightArrow => {
            let r: Vec<fofml::Atom> = itr
                .map(|x| parse_body_inner(x, env, letenv.clone()))
                .collect();
            debug_assert!(r.len() == 2);
            let a = r[0].clone();
            let b = r[1].clone();
            fofml::Atom::mk_disj(fofml::Atom::mk_not(a), b)
        }
        Tag::Not => {
            let r: Vec<fofml::Atom> = itr
                .map(|x| parse_body_inner(x, env, letenv.clone()))
                .collect();
            debug_assert!(r.len() == 1);
            let a = r[0].clone();
            fofml::Atom::mk_not(a)
        }
        Tag::Var(p) => {
            let l: Vec<Op> = itr.map(|x| parse_op(x, env, letenv.clone())).collect();
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

            let r: Vec<fofml::Atom> = itr
                .map(|x| parse_body_inner(x, env, letenv.clone()))
                .collect();
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
            let letenv = parse_let_args(args, env, letenv);
            let r: Vec<fofml::Atom> = itr
                .map(|x| parse_body_inner(x, env, letenv.clone()))
                .collect();
            debug_assert!(r.len() == 1);
            r[0].clone()
        }
        Tag::ITE => {
            // if-then-else
            let r: Vec<fofml::Atom> = itr
                .map(|x| parse_body_inner(x, env, letenv.clone()))
                .collect();
            assert!(r.len() == 3);
            let conj = r[0].clone();
            let ifbr = r[1].clone();
            let elsebr = r[2].clone();
            let ifb = fofml::Atom::mk_disj(fofml::Atom::mk_not(conj.clone()), ifbr);
            let elseb = fofml::Atom::mk_disj(conj, elsebr);
            fofml::Atom::mk_conj(ifb, elseb)
        }
    }
}

/* Cons((Symbol("let") . Cons((Cons((Cons((Symbol(".cse0") . Cons((Cons((Symbol("and") . Cons((Cons((Symbol("<=") . Cons((Symbol("xx_113") . Cons((Symbol("xx_113") . Null)))))) . Cons((Cons((Symbol("or") . Cons((Cons((Symbol("<") . Cons((Symbol("xx_113") . Cons((Symbol("xx_113") . Null)))))) . Cons((Cons((Symbol("=") . Cons((Symbol("xx_113") . Cons((Symbol("xx_112") . Null)))))) . Null)))))) . Null)))))) . Null)))) . Null)) . Cons((Cons((Symbol("and") . Cons((Cons((Symbol("or") . Cons((Cons((Symbol("<=") . Cons((Symbol("xx_113") . Cons((Number(PosInt(0)) . Null)))))) . Cons((Symbol(".cse0") . Null)))))) . Cons((Cons((Symbol("or") . Cons((Cons((Symbol("<=") . Cons((Number(PosInt(0)) . Cons((Symbol("xx_113") . Null)))))) . Cons((Symbol(".cse0") . Null)))))) . Cons((Cons((Symbol("or") . Cons((Cons((Symbol("=") . Cons((Number(PosInt(0)) . Cons((Symbol("xx_112") . Null)))))) . Cons((Symbol(".cse0") . Null)))))) . Null)))))))) . Null)))))) */
// parse
fn parse_body_inner<'a>(
    v: &'a lexpr::Value,
    env: &mut HashMap<&'a str, Ident>,
    letenv: LetEnv<'a>,
) -> fofml::Atom {
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
                match letenv.search(s.as_ref()) {
                    Some((w, v)) => parse_body_inner(v, env, w.clone()),
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
    let letenv = LetEnv::new();
    parse_body_inner(v, env, letenv)
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

    let s = "(ite (= x 0) (=> (not (= (+ x (- 1)) 0)) (=> (not (= (+ x (- 2)) 0)) (and (<= x x) (or (< x x) (= x (+ x 1)))))) (let ((.cse2 (+ x x))) (and (<= .cse2 .cse2) (or (< .cse2 .cse2) (= x (+ x x 1))))))";
    let x = lexpr::from_str(s).unwrap();
    parse_body(&x, &mut env);

    fn fresh_env<'a>(v: &'a [&'a str]) -> HashMap<&'a str, Ident> {
        let mut env = HashMap::new();
        for id in v {
            env.insert(*id, Ident::fresh());
        }
        env
    }
    let s = "(let ((.cse0 (= xx_408 0))) (let ((.cse1 (and (let ((.cse2 (+ xx_407 1))) (ite (= xx_377 0) (and (<= xx_407 xx_407) (or (< xx_407 xx_407) (= xx_409 .cse2))) (and (<= .cse2 .cse2) (or (< .cse2 .cse2) (= xx_409 (+ xx_407 2)))))) (not .cse0)))) (and (or .cse0 .cse1) (or (= xx_409 xx_407) .cse1))))";
    let v = ["xx_377", "xx_407", "xx_408", "xx_409"];
    let mut env = fresh_env(&v);
    let x = lexpr::from_str(s).unwrap();
    let result = parse_body(&x, &mut env).to_constraint().unwrap();
    println!("result: {}", result);

    // calculated by hand: (xx408 = 0 \/     (xx408 != 0 /\ (x377 != 0 \/ xx409 = xx407 + 1) /\ (x377 = 0 \/ xx409 = xx407 + 2)))
    //                  /\ (xx409 = xx407 \/ (xx408 != 0 /\ (x377 != 0 \/ xx409 = xx407 + 1) /\ (x377 = 0 \/ xx409 = xx407 + 2)))
    let x377 = *env.get("xx_377").unwrap();
    let x407 = *env.get("xx_407").unwrap();
    let x408 = *env.get("xx_408").unwrap();
    let x409 = *env.get("xx_409").unwrap();

    let x377neq0 = Constraint::mk_neq(Op::mk_var(x377), Op::mk_const(0));
    let x377eq0 = Constraint::mk_eq(Op::mk_var(x377), Op::mk_const(0));
    let cse1 = Constraint::mk_conj(
        Constraint::mk_neq(Op::mk_var(x408), Op::mk_const(0)),
        Constraint::mk_conj(
            Constraint::mk_disj(
                x377neq0.clone(),
                Constraint::mk_eq(
                    Op::mk_var(x409),
                    Op::mk_add(Op::mk_var(x407), Op::mk_const(1)),
                ),
            ),
            Constraint::mk_disj(
                x377eq0.clone(),
                Constraint::mk_eq(
                    Op::mk_var(x409),
                    Op::mk_add(Op::mk_var(x407), Op::mk_const(2)),
                ),
            ),
        ),
    );
    let left = Constraint::mk_disj(
        Constraint::mk_eq(Op::mk_var(x408), Op::mk_const(0)),
        cse1.clone(),
    );
    let right = Constraint::mk_disj(
        Constraint::mk_eq(Op::mk_var(x409), Op::mk_var(x407)),
        cse1.clone(),
    );
    let answer = Constraint::mk_conj(left, right);
    println!("{}", answer);

    let mut solver = crate::solver::smt::default_solver();
    assert!(solver.check_equivalent(&result, &answer).is_sat());
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
                    let v: Vec<_> = args
                        .iter()
                        .zip(l.iter())
                        .map(|(x, y)| (*x, y.clone()))
                        .collect();
                    let a = a.subst_multi(&v);
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
    fn parse_spacer_model(model_str: &str) -> Result<Model, lexpr::parse::Error> {
        debug!("{}", model_str);
        let x = lexpr::from_str(model_str)?;
        let model: HashMap<Ident, (Vec<Ident>, fofml::Atom)> = match x {
            Value::Cons(x) => x
                .into_iter()
                .filter(|(x, _)| !x.is_symbol())
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
    let model = "(model
  (define-fun xx_2
    ( (v_0 Int) ) Bool
    true
  )
  (define-fun xx_3
    ( (v_0 Int) (v_1 Int) ) Bool
    (or (and (= (+ v_0 (* (- 1) v_1) 10) 0) (or (= (+ v_0 (- 91)) 0) (>= v_1 102))) (and (>= (* (- 1) v_1) (- 101)) (or (= (+ v_0 (- 91)) 0) (>= v_1 102)) (not (= (+ v_0 (* (- 1) v_1) 10) 0))))
  )
  (define-fun xx_4
    ( (v_0 Int) (v_1 Int) ) Bool
    (and (xx_2 v_1) (xx_3 v_0 v_1))
  ))";
    let m = match Model::parse_hoice_model(model) {
        Ok(m) => {
            assert!(m.model.len() == 3);
            m
        }
        Err(_) => panic!("model is broken"),
    };
    for (id, (args, c)) in m.model.iter() {
        print!("{id}(");
        for arg in args.iter() {
            print!("{arg},");
        }
        println!(") = {c}");
    }
}

#[test]
fn test_parse_spacer_model() {
    let s = "(
  (define-fun xx_2 ((x!0 Int)) Bool
    (or (= x!0 (- 1)) (= x!0 0)))
)";
    match Model::parse_spacer_model(s) {
        Ok(m) => {
            println!("{m}");
            assert!(m.model.len() == 1);
        }
        Err(_) => panic!("model is broken"),
    }
    let s = "(model
  (define-fun xx_341 ((x!0 Int) (x!1 Int)) Bool
    (>= (+ x!0 (* (- 1) x!1)) 0))
  (define-fun xx_324 ((x!0 Int) (x!1 Int)) Bool
    (<= (+ x!0 (* (- 1) x!1)) 0))
  (define-fun xx_327 ((x!0 Int) (x!1 Int) (x!2 Int)) Bool
    true)
)";
    match Model::parse_spacer_model(s) {
        Ok(m) => {
            println!("{m}");
            assert!(m.model.len() == 3);
        }
        Err(_) => panic!("model is broken"),
    }
}

pub fn is_solution_valid(clauses: &[CHC], model: &Model) -> bool {
    crate::title!("is_solution_valid");
    let mut c = Constraint::mk_true();
    for clause in clauses.iter() {
        let c2 = clause.replace_with_model(model);
        c = Constraint::mk_conj(c, c2);
    }
    debug!("{}", c);
    let mut solver = smt::default_solver();
    let fvs = c.fv();
    match solver.solve(&c, &fvs) {
        super::SolverResult::Sat => true,
        super::SolverResult::Unsat => false,
        super::SolverResult::Unknown => panic!("failed to verify"),
        super::SolverResult::Timeout => panic!("smt timeout"),
    }
}

#[test]
fn test_is_solution_valid() {
    let (chc, mut model, vars) = chc::gen_clause_pqp();
    let clauses = vec![chc];
    assert!(is_solution_valid(&clauses, &model));
    let x = vars[0];
    let y = vars[1];
    let p = vars[2];
    let q = vars[3];
    let sol_for_p = model.model.remove(&p).unwrap();
    let sol_for_q = model.model.remove(&q).unwrap();
    let new_sol_c = Constraint::mk_eq(Op::mk_var(x), Op::mk_var(y));
    model.model.insert(p, (sol_for_p.0, new_sol_c));
    model.model.insert(q, (sol_for_q.0, Constraint::mk_true()));

    assert!(!is_solution_valid(&clauses, &model));
}

impl CHCSolver for HoiceSolver {
    fn solve(&mut self, clauses: &[CHC]) -> CHCResult {
        let smt2 = chcs_to_smt2(clauses, self.style);
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

fn spacer_solver(smt_string: String, interpolation: bool) -> String {
    debug!("spacer_solver: {}", smt_string);
    let f = smt::save_smt2(smt_string);
    let mut args = vec!["fp.engine=spacer"];
    if interpolation {
        args.push("fp.xform.inline_eager=false");
        args.push("fp.xform.inline_linear=false");
        args.push("fp.xform.slice=false");
    }
    args.push(f.path().to_str().unwrap());
    debug!("filename: {}", &args[1]);
    let out = chc_execution!({ util::exec_with_timeout("z3", &args, Duration::from_secs(1),) });
    String::from_utf8(out).unwrap()
}

impl CHCSolver for SpacerSolver {
    fn solve(&mut self, clauses: &[CHC]) -> CHCResult {
        let smt2 = chcs_to_smt2(clauses, self.style);
        debug!("smt2: {}", &smt2);
        let s = spacer_solver(smt2, self.interpolation);
        debug!("smt_solve result: {:?}", &s);
        if s.starts_with("sat") {
            let m = Model::parse_spacer_model(&s[4..]).unwrap();
            CHCResult::Sat(m)
        } else if s.starts_with("unsat") {
            CHCResult::Unsat
        } else {
            CHCResult::Unknown
        }
    }
}
