use super::tree::*;
use super::{Atom, Ty, G};
use crate::formula::*;
use crate::pdr::rtype::TauKind;
use crate::solver;

use rpds::Stack;

#[derive(Clone, Debug)]
pub(super) struct DeriveNode {
    // Γ ⊢ ψ : τ
    // Γ is omitted
    pub rule: Rule,
    pub expr: G,
    pub ty: Ty,
}

#[derive(Clone, Debug)]
pub enum Rule {
    Conjoin,
    Disjoin,
    Var,
    Univ(Ident),
    IAbs(Ident),
    Abs,
    IApp(Op),
    App,
    Subsumption,
    Atom,
}

impl DeriveNode {
    fn conjoin(expr: G, left: &Self, right: &Self) -> Self {
        let rule = Rule::Conjoin;
        let ty = match (left.ty.kind(), right.ty.kind()) {
            (TauKind::Proposition(c1), TauKind::Proposition(c2)) => {
                Ty::mk_prop_ty(Atom::mk_conj(c1.clone(), c2.clone()))
            }
            (_, _) => panic!("fatal: self.ty={} and c.ty={}", left.ty, right.ty),
        };
        DeriveNode { rule, expr, ty }
    }
    fn disjoin(expr: G, left: &Self, right: &Self) -> Self {
        let rule = Rule::Disjoin;
        let ty = match (left.ty.kind(), right.ty.kind()) {
            (TauKind::Proposition(c1), TauKind::Proposition(c2)) => {
                Ty::mk_prop_ty(Atom::mk_disj(c1.clone(), c2.clone()))
            }
            (_, _) => panic!("fatal: self.ty={} and c.ty={}", left.ty, right.ty),
        };
        DeriveNode { rule, expr, ty }
    }
    fn quantify(expr: G, node: &Self, ident: &Ident) -> Self {
        let rule = Rule::Univ(*ident);
        let ty = match node.ty.kind() {
            TauKind::Proposition(c1) => Ty::mk_prop_ty(Atom::mk_quantifier_int(
                crate::formula::QuantifierKind::Universal,
                *ident,
                c1.clone(),
            )),
            TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => panic!("fatal"),
        };
        DeriveNode { rule, expr, ty }
    }
    fn iarrow(expr: G, node: &Self, ident: &Ident) -> Self {
        let rule = Rule::IAbs(*ident);
        let ty = Ty::mk_iarrow(*ident, node.ty.clone());
        DeriveNode { rule, expr, ty }
    }
    fn arrow(expr: G, node: &Self, ts: Vec<Ty>) -> Self {
        let rule = Rule::Abs;
        let ty = Ty::mk_arrow(ts, node.ty.clone());
        DeriveNode { rule, expr, ty }
    }
    fn iapp(expr: G, node: &Self, op: &Op) -> Self {
        let rule = Rule::IApp(op.clone());
        let ty = match node.ty.kind() {
            TauKind::IArrow(x, t2) => t2.subst(x, op),
            _ => panic!("fatal"),
        };
        DeriveNode { rule, expr, ty }
    }
    fn subsumption(node: &Self, ty: Ty) -> Self {
        let rule = Rule::Subsumption;
        let expr = node.expr.clone();
        DeriveNode { rule, expr, ty }
    }
    fn app(expr: G, pred_node: &Self) -> Self {
        let rule = Rule::App;
        let ty = match pred_node.ty.kind() {
            TauKind::Arrow(_, rt) => rt.clone(),
            TauKind::Proposition(_) | TauKind::IArrow(_, _) => {
                panic!("app rule is used for a wrong derivation")
            }
        };
        DeriveNode { rule, expr, ty }
    }
}

#[derive(Clone)]
pub(super) struct Derivation<C> {
    tree: Tree<DeriveNode>,
    pub coefficients: Stack<Ident>,
    pub constraints: Stack<C>,
}

fn concat_stacks<'a, T: 'a + Clone, I>(stacks: I) -> Stack<T>
where
    I: Iterator<Item = &'a Stack<T>>,
{
    let mut s = Stack::new();
    for stack in stacks {
        for x in stack.iter() {
            s.push_mut(x.clone());
        }
    }
    s
}

impl Derivation<Atom> {
    pub fn get_nodes_by_id<'a>(
        &'a self,
        id: &'a Ident,
    ) -> impl Iterator<Item = Node<'a, DeriveNode>> + 'a {
        self.tree.filter(move |n| n.expr.aux.id == *id)
    }
    pub fn get_types_by_id<'a>(&'a self, id: &'a Ident) -> impl Iterator<Item = Ty> + 'a {
        self.tree
            .filter(move |n| n.expr.aux.id == *id)
            .map(|n| n.item.ty.clone())
    }
    pub fn get_types_by_level<'a>(
        &'a self,
        node_id: ID,
        level: &'a usize,
    ) -> impl Iterator<Item = Ty> + 'a {
        let node = self.tree.get_node_by_id(node_id);
        self.tree
            .filter_children(node, move |n| {
                n.expr.aux.level_arg.iter().any(|arg| arg == level)
            })
            .map(|n| n.item.ty.clone())
    }

    pub fn rule_atom(expr: G, ty: Ty) -> Self {
        let rule = Rule::Atom;
        let node = DeriveNode { rule, expr, ty };
        Self {
            tree: Tree::singleton(node),
            constraints: Stack::new(),
            coefficients: Stack::new(),
        }
    }

    pub fn rule_var(expr: G, ty: Ty, coefficients: Stack<Ident>) -> Self {
        let rule = Rule::Var;
        let node = DeriveNode { rule, expr, ty };
        Self {
            tree: Tree::singleton(node),
            constraints: Stack::new(),
            coefficients,
        }
    }

    fn rule_one_arg_inner(node: DeriveNode, d: Self) -> Self {
        Self {
            tree: Tree::tree_with_child(node, d.tree),
            ..d
        }
    }

    fn rule_two_arg_inner(node: DeriveNode, d1: Self, d2: Self) -> Self {
        Self {
            tree: Tree::tree_with_two_children(node, d1.tree, d2.tree),
            constraints: concat_stacks([d1.constraints, d2.constraints].iter()),
            coefficients: concat_stacks([d1.coefficients, d2.coefficients].iter()),
        }
    }

    fn rule_multiples<I>(node: DeriveNode, derivations: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        let mut tree = Tree::singleton(node);
        let (_, constraints, coefficients) = derivations.fold(
            (&mut tree, Stack::new(), Stack::new()),
            |(t, constrs, coefs), d| {
                t.append_children(d.tree);
                let constraints = concat_stacks([constrs, d.constraints].iter());
                let coefficients = concat_stacks([coefs, d.coefficients].iter());
                (t, constraints, coefficients)
            },
        );
        Self {
            tree,
            constraints,
            coefficients,
        }
    }
    pub fn rule_conjoin(expr: G, d1: Self, d2: Self) -> Self {
        let root = DeriveNode::conjoin(expr, d1.tree.root().item, d2.tree.root().item);
        Self::rule_two_arg_inner(root, d1, d2)
    }
    pub fn rule_disjoin(expr: G, d1: Self, d2: Self) -> Self {
        let root = DeriveNode::disjoin(expr, d1.tree.root().item, d2.tree.root().item);
        Self::rule_two_arg_inner(root, d1, d2)
    }
    pub fn rule_quantifier(expr: G, d: Self, x: &Ident) -> Self {
        let root = DeriveNode::quantify(expr, d.tree.root().item, x);
        Self::rule_one_arg_inner(root, d)
    }
    pub fn rule_iarrow(expr: G, d: Self, x: &Ident) -> Self {
        let root = DeriveNode::iarrow(expr, d.tree.root().item, x);
        Self::rule_one_arg_inner(root, d)
    }
    pub fn rule_arrow(expr: G, d: Self, tys: Vec<Ty>) -> Self {
        let root = DeriveNode::arrow(expr, d.tree.root().item, tys);
        Self::rule_one_arg_inner(root, d)
    }
    pub fn rule_iapp(expr: G, d: Self, o: &Op) -> Self {
        let root = DeriveNode::iapp(expr, d.tree.root().item, o);
        Self::rule_one_arg_inner(root, d)
    }
    pub fn rule_subsumption(d: Self, ty: Ty) -> Self {
        let child = d.tree.root();
        let s = child.item.ty.clone();
        let constraint = Ty::check_subtype(&Atom::mk_true(), &s, &ty);
        let root = DeriveNode::subsumption(child.item, ty);
        let mut d = Self::rule_one_arg_inner(root, d);
        d.constraints.push_mut(constraint);
        d
    }
    pub fn rule_app<I>(expr: G, d1: Self, args: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        let root = DeriveNode::app(expr, &d1.tree.root().item);
        Self::rule_multiples(root, std::iter::once(d1).chain(args))
    }
    pub fn update_with_model(&mut self, m: &solver::Model) {
        self.tree.iter_mut(|item| {
            let mut ty = item.ty.clone();
            for (var, val) in m.model.iter() {
                ty = ty.subst(var, &Op::mk_const(*val));
            }
            item.ty = ty;
        });
    }
    pub fn get_context_ty(&self, node: Node<DeriveNode>) -> Ty {
        // うそかも
        // subsumptionに到達するというよりも、subject expansionのタイミングで
        // Derivationの木を全体的に構成し直す。
        // でもそれは、Disjoinでsubsumption入れれば同じことでは
        // Conjoinの間は問題がない
        // Disjoin後にsubsumptionを入れるようにする。
        let parent = self
            .tree
            .traverse_parent_until(node, |node| {
                debug_assert!(matches!(node.rule, Rule::Disjoin));
                matches!(node.rule, Rule::Subsumption)
            })
            .expect("unstructured derivation");
        parent.item.ty.clone()
    }
    pub fn root_ty(&self) -> &Ty {
        &self.tree.root().item.ty
    }
    pub fn node_id_to_ty<'a>(&'a self, id: &'a ID) -> &'a Ty {
        &id.to_item(&self.tree).ty
    }
}
