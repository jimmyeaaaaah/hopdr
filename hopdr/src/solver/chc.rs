use super::smt;
use super::smt::constraint_to_smt2_inner;
use super::smt::ident_2_smt2;
use super::{SMT2Style, SolverResult};
use crate::formula::chc;
use crate::formula::pcsp;
use crate::formula::{Fv, Ident, Op};

use std::collections::HashMap;

#[derive(Copy, Clone)]
pub enum CHCStyle {
    Hoice,
    Spacer,
}

type CHC = chc::CHC<pcsp::Atom>;

const PROLOGUE: &'static str = "(set-logic HORN)\n";

pub trait SMTSolver {
    fn solve(&mut self, clauses: &Vec<CHC>) -> SolverResult;
}

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

fn chc_to_smt2(chc: &CHC, style: CHCStyle) -> String {
    let mut fvs = chc.body.fv();
    let head_smt2 = match &chc.head {
        chc::CHCHead::Constraint(c) => {
            c.fv_with_vec(&mut fvs);
            smt::constraint_to_smt2_inner(c, SMT2Style::Z3)
        }
        chc::CHCHead::Predicate(p, l) => {
            for i in l {
                i.fv_with_vec(&mut fvs);
            }
            predicate_to_smt2(p, l)
        }
    };
    let body_smt2 = atom_to_smt2(&chc.body);

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

pub fn chcs_to_smt2(chcs: &[CHC], style: CHCStyle) -> String {
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
    format!("{}{}{}{}", PROLOGUE, defs, body, get_epilogue(style))
}
