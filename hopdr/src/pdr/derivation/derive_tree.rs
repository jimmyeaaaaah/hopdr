use super::tree::*;
use super::{Ty, G};
use crate::util::P;

enum DeriveNodeKind {
    Conj(P<DeriveNode>, P<DeriveNode>),
    Disj(P<DeriveNode>, P<DeriveNode>),
    Abs(P<DeriveNode>),
    App(P<DeriveNode>, P<DeriveNode>),
    Forall(P<DeriveNode>),
    Atom(P<DeriveNode>),
}

struct DeriveNode {
    rule: DeriveNodeKind,
    expr: G,
    ty: Ty,
}
