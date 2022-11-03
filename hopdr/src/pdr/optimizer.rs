// derivation scheduling and optimizer

use super::derivation;
use crate::formula::{Ident, Variable};

use std::collections::HashSet;

pub struct InferenceResult {
    #[allow(dead_code)]
    succeeded: bool,
}

impl InferenceResult {
    pub fn new(succeeded: bool) -> Self {
        Self { succeeded }
    }
}

pub struct VariableInfo<'a> {
    pub reduction_id: usize,
    pub variable: Variable,
    pub idents: &'a HashSet<Ident>,
}
pub fn variable_info<'a>(
    reduction_id: usize,
    variable: Variable,
    idents: &'a HashSet<Ident>,
) -> VariableInfo<'a> {
    VariableInfo {
        reduction_id,
        variable,
        idents,
    }
}
pub trait Optimizer {
    fn continuable(&self) -> bool;
    fn report_inference_result(&mut self, result: InferenceResult);
    fn gen_type(&mut self, info: &VariableInfo) -> Option<Vec<derivation::Ty>>;
}

// first attempt: always introduce a common type
// second attempt: always do not introduce a common type
pub struct NaiveOptimizer {
    already_attempted_once: bool,
    fail: bool,
}
impl NaiveOptimizer {
    #[allow(dead_code)]
    pub fn new() -> Self {
        NaiveOptimizer {
            already_attempted_once: false,
            fail: false,
        }
    }
}

impl Optimizer for NaiveOptimizer {
    fn continuable(&self) -> bool {
        !self.fail
    }

    fn report_inference_result(&mut self, _result: InferenceResult) {
        if !self.already_attempted_once {
            self.already_attempted_once = true;
        } else {
            self.fail = true;
        }
    }

    fn gen_type(&mut self, info: &VariableInfo) -> Option<Vec<derivation::Ty>> {
        match &info.variable.ty.kind() {
            crate::formula::TypeKind::Proposition | crate::formula::TypeKind::Integer => {
                return None
            }
            crate::formula::TypeKind::Arrow(_, _) => (),
        };
        // always do not generate a common type when
        if self.already_attempted_once {
            return None;
        }

        // singleton template
        Some(vec![derivation::Ty::from_sty(
            &info.variable.ty,
            &info.idents,
        )])
    }
}

#[test]
fn test_naive_optimizer() {
    use crate::formula::Type;
    let mut o = NaiveOptimizer::new();
    let st = Type::mk_type_arrow(Type::mk_type_int(), Type::mk_type_prop());
    assert!(o.continuable());
    let mut vars = HashSet::new();
    vars.insert(Ident::fresh());
    let vi = VariableInfo {
        reduction_id: 0,
        variable: Variable::fresh(st.clone()),
        idents: &vars,
    };
    let ts = o.gen_type(&vi).unwrap();
    assert_eq!(ts.len(), 1);
    let t = &ts[0];
    assert!(t.to_sty() == st);
    let c = t.rty_no_exists();
    match c.kind() {
        crate::formula::fofml::AtomKind::Predicate(_, l) if l.len() == 2 => (),
        _ => panic!("fail"),
    }

    // tick
    o.report_inference_result(InferenceResult { succeeded: false });
    assert!(o.continuable());
    assert_eq!(o.gen_type(&vi), None);

    // tick
    o.report_inference_result(InferenceResult { succeeded: false });
    assert!(!o.continuable());

    // tick
    o.report_inference_result(InferenceResult { succeeded: false });
    assert!(!o.continuable());
}

/// VoidOptimizer: does not optimize anything.
pub struct VoidOptimizer {
    fail: bool,
}

impl VoidOptimizer {
    #[allow(dead_code)]
    pub fn new() -> Self {
        Self { fail: false }
    }
}

impl Optimizer for VoidOptimizer {
    fn continuable(&self) -> bool {
        !self.fail
    }

    fn report_inference_result(&mut self, _result: InferenceResult) {
        self.fail = true;
    }

    fn gen_type(&mut self, _info: &VariableInfo) -> Option<Vec<derivation::Ty>> {
        None
    }
}
