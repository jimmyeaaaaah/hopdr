use super::tree::*;
use super::{Ty, G};
use crate::formula::Ident;
use rpds::Stack;

type ITy = Stack<Ty>;

fn to_ity(ty: Ty) -> ITy {
    ITy::new().push(ty)
}

#[derive(Clone, Debug)]
pub(super) struct DeriveNode {
    // Γ ⊢ ψ : τ
    // Γ is omitted
    expr: G,
    ty: ITy,
}

#[derive(Clone)]
pub(super) struct Derivation<C> {
    tree: Tree<DeriveNode>,
    coefficients: Stack<Ident>,
    constraints: Stack<C>,
}

impl From<Ty> for ITy {
    fn from(t: Ty) -> Self {
        Stack::new().push(t)
    }
}

fn concat_stacks<'a, T, I>(stacks: I) -> Stack<T>
where
    I: Iterator<Item = &'a Stack<T>>,
{
    stacks
        .fold(std::iter::empty(), |i, stack| i.chain(stack.into_iter()))
        .cloned()
        .collect()
}

impl<C> Derivation<C> {
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

    pub fn rule_base<T>(expr: G, ty: T) -> Self
    where
        T: Into<ITy>,
    {
        let ty = ty.into();
        let node = DeriveNode { expr, ty };
        Self {
            tree: Tree::singleton(node),
            constraints: Stack::new(),
            coefficients: Stack::new(),
        }
    }

    pub fn rule_var<T>(expr: G, ty: T, coefficients: Stack<Ident>) -> Self
    where
        T: Into<ITy>,
    {
        let ty = ty.into();
        let node = DeriveNode { expr, ty };
        Self {
            tree: Tree::singleton(node),
            constraints: Stack::new(),
            coefficients,
        }
    }

    pub fn rule_one_arg<T>(expr: G, ty: T, d: Self) -> Self
    where
        T: Into<ITy>,
    {
        let ty = ty.into();
        let node = DeriveNode { expr, ty };
        Self {
            tree: Tree::tree_with_child(node, d.tree),
            ..d
        }
    }

    pub fn rule_two_args<T>(expr: G, ty: T, d1: Self, d2: Self) -> Self
    where
        T: Into<ITy>,
    {
        let ty = ty.into();
        let node = DeriveNode { expr, ty };
        Self {
            tree: Tree::tree_with_two_children(node, d1.tree, d2.tree),
            constraints: concat_stacks(&[&d1.constraints, &d2.constraints]),
            coefficients: concat_stacks(&[&d1.coefficients, &d2.coefficients]),
        }
    }

    pub fn rule_multiples<I, T>(expr: G, ty: T, derivations: I) -> Self
    where
        T: Into<ITy>,
        I: Iterator<Item = Self>,
    {
        let ty = ty.into();
        let node = DeriveNode { expr, ty };
        let mut tree = Tree::singleton(node);
        let (_, constraints, coefficients) = derivations.fold(
            (&mut tree, Stack::new(), Stack::new()),
            |(t, constrs, coefs), (child, constraint, coef)| {
                t.append_children(child);
                (t, constrs.push(constraint), coefs.push(coef))
            },
        );
        Self {
            tree,
            constraints,
            coefficients,
        }
    }
    pub fn rule_conjoin<T>(expr: G, ty: T, d1: Self, d2: Self) -> Self
    where
        T: Into<ITy>,
    {
        let ty = ty.into();
        let node = DeriveNode { expr, ty };
        Self {
            tree: Tree::tree_with_two_children(node, d1.tree, d2.tree),
            constraints: concat_stacks(&[&d1.constraints, &d2.constraints]),
            coefficients: concat_stacks(&[&d1.coefficients, &d2.coefficients]),
        }
    }
}
