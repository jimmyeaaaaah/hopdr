use super::tree::*;
use super::{Ty, G};
use crate::formula::Ident;
use rpds::Stack;

type ITy = Stack<Ty>;

fn to_ity(ty: Ty) -> ITy {
    ITy::new().push(ty)
}

#[derive(Clone)]
pub(super) struct DeriveNode {
    // Γ ⊢ ψ : τ
    // Γ is omitted
    expr: G,
    ty: ITy,
}

#[derive(Clone)]
pub(super) struct Derivation {
    tree: Tree<DeriveNode>,
}

impl Derivation {
    pub fn get_types_by_id<'a>(&'a self, id: &'a Ident) -> impl Iterator<Item = Ty> + 'a {
        self.tree
            .filter(move |n| n.expr.aux.id == *id)
            .map(|n| n.item.ty.iter().cloned())
            .flatten()
    }
    pub fn get_types_by_level<'a>(&'a self, level: &'a usize) -> impl Iterator<Item = Ty> + 'a {
        self.tree
            .filter(move |n| n.expr.aux.level_arg.iter().any(|arg| arg == level))
            .map(|n| n.item.ty.iter().cloned())
            .flatten()
    }
}

fn rule_base(expr: G, ty: ITy) -> Derivation {
    let node = DeriveNode { expr, ty };
    Derivation {
        tree: Tree::singleton(node),
    }
}

fn rule_one_arg(expr: G, ty: ITy, d: Derivation) -> Derivation {
    let node = DeriveNode { expr, ty };
    Derivation {
        tree: Tree::tree_with_child(node, d.tree),
    }
}

fn rule_two_args(expr: G, ty: ITy, d1: Derivation, d2: Derivation) -> Derivation {
    let node = DeriveNode { expr, ty };
    Derivation {
        tree: Tree::tree_with_two_children(node, d1.tree, d2.tree),
    }
}

fn rule_multiples<I>(expr: G, ty: ITy, derivations: I) -> Derivation
where
    I: Iterator<Item = Derivation>,
{
    let node = DeriveNode { expr, ty };
    Derivation {
        tree: Tree::tree_from_children(node, derivations.map(|d| d.tree)),
    }
}
