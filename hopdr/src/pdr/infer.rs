use super::rtype::TyEnv;
#[allow(unused_imports)]
use super::{fml, rtype};
#[allow(unused_imports)]
use crate::formula::hes::{Goal, Problem};
#[allow(unused_imports)]
use crate::formula::{fofml, hes, Constraint};

pub(super) fn infer(_env: &rtype::TyEnv, _cex: &Goal<Constraint>) -> Option<TyEnv> {
    // 1. prepare unwound formulas
    // 2. prepare template
    // 3. calculate constraints
    // 4. solve constraints by CHC (or a template-based method)
    // 5. return type environment
    None
}
