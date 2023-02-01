use super::tree::*;
use super::{Ty, G};
use rpds::Stack;

pub(super) enum TypingRule {
    Conj,
    Disj,
    Abs,
    App,
    Forall,
    Atom,
    Intersection,
    Var,
}

type ITy = Stack<Ty>;

fn to_ity(ty: Ty) -> ITy {
    ITy::new().push(ty)
}

pub(super) struct DeriveNode {
    rule: TypingRule,
    // Γ ⊢ ψ : τ
    // Γ is omitted
    expr: G,
    ty: ITy,
}

pub(super) struct Derivation {
    tree: Tree<DeriveNode>,
}

fn rule_base(rule: TypingRule, expr: G, ty: ITy) -> Derivation {
    let node = DeriveNode { rule, expr, ty };
    Derivation {
        tree: Tree::singleton(node),
    }
}

fn rule_one_arg(rule: TypingRule, expr: G, ty: ITy, d: Derivation) -> Derivation {
    let node = DeriveNode { rule, expr, ty };
    Derivation {
        tree: Tree::tree_with_child(node, d.tree),
    }
}

fn rule_two_args(rule: TypingRule, expr: G, ty: ITy, d1: Derivation, d2: Derivation) -> Derivation {
    let node = DeriveNode { rule, expr, ty };
    Derivation {
        tree: Tree::tree_with_two_children(node, d1.tree, d2.tree),
    }
}

fn rule_multiples<I>(rule: TypingRule, expr: G, ty: ITy, derivations: I) -> Derivation
where
    I: Iterator<Item = Derivation>,
{
    let node = DeriveNode { rule, expr, ty };
    Derivation {
        tree: Tree::tree_from_children(node, derivations.map(|d| d.tree)),
    }
}

fn rule_conj(expr: G, ty: Ty, d1: Derivation, d2: Derivation) -> Derivation {
    rule_two_args(TypingRule::Conj, expr, to_ity(ty), d1, d2)
}

fn rule_disj(expr: G, ty: Ty, d1: Derivation, d2: Derivation) -> Derivation {
    rule_two_args(TypingRule::Disj, expr, to_ity(ty), d1, d2)
}

fn rule_abs(expr: G, ty: Ty, d1: Derivation) -> Derivation {
    rule_one_arg(TypingRule::Abs, expr, to_ity(ty), d1)
}

fn rule_app(expr: G, ty: Ty, d1: Derivation, d2: Derivation) -> Derivation {
    rule_two_args(TypingRule::App, expr, to_ity(ty), d1, d2)
}

fn rule_forall(expr: G, ty: Ty, d1: Derivation) -> Derivation {
    rule_one_arg(TypingRule::Forall, expr, to_ity(ty), d1)
}

fn rule_intersection<I>(expr: G, tys: ITy, derivations: I) -> Derivation
where
    I: Iterator<Item = Derivation>,
{
    rule_multiples(TypingRule::Intersection, expr, tys, derivations)
}

fn rule_var(expr: G, ty: Ty, derivation: Derivation) -> Derivation {
    rule_one_arg(TypingRule::Var, expr, to_ity(ty), derivation)
}
