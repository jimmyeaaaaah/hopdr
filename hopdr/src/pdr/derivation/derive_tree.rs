use std::collections::{HashMap, HashSet};
use std::ops::Sub;

use super::tree::*;
use super::{Atom, Ty, G};
use crate::pdebug;
use crate::pdr::rtype::{Instantiation, TBot, Tau, TauKind};
use crate::solver;
use crate::util::Pretty;
use crate::{formula::*, highlight};

use rpds::{HashTrieMap, Stack};

const PRINT_ASSUMPTION: bool = true;
const OMIT_EXPR: bool = false;

#[derive(Clone, Debug)]
pub(super) struct DeriveNode {
    // Γ; C ⊢ ψ : τ
    // Γ is omitted
    pub context: Stack<Atom>, // C equals the conjoin of them
    pub rule: Rule,
    pub expr: G,
    pub ty: Ty,
}

#[derive(Clone, Debug)]
pub enum Rule {
    Conjoin,
    Disjoin,
    // Ty: original ty
    // Stack<Instantiation>: seq of instantiations
    // the ty in the derivation is expected to be the instantiated type
    // of ty with the instantiations
    Var(Stack<Instantiation>, Ty),
    Univ,
    IAbs,
    Abs(Vec<Ty>),
    IApp(Op),
    App,
    Subsumption, // Atom: rty
    Equivalence(Stack<Atom>),
    Atom,
    Poly(Ident),
}

impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Rule::Conjoin => "Conj",
            Rule::Disjoin => "Disj",
            Rule::Var(_, _) => "Var",
            Rule::Univ => "Univ",
            Rule::IAbs => "IAbs",
            Rule::Abs(_) => "Abs",
            Rule::IApp(_) => "IApp",
            Rule::App => "App",
            Rule::Subsumption => "Sub",
            Rule::Equivalence(_) => "Equi",
            Rule::Atom => "Atom",
            Rule::Poly(_) => "Poly",
        };
        write!(f, "{}", s)
    }
}

impl Subst for Rule {
    type Item = Op;
    type Id = Ident;
    fn subst(&self, x: &Self::Id, v: &Self::Item) -> Self {
        match self {
            Rule::Conjoin
            | Rule::Disjoin
            | Rule::Univ
            | Rule::IAbs
            | Rule::Subsumption
            | Rule::App
            | Rule::IApp(_)
            | Rule::Poly(_)
            | Rule::Atom => self.clone(),
            Rule::Equivalence(c) => {
                let c = c.iter().map(|c| c.subst(x, v)).collect();
                Rule::Equivalence(c)
            }
            Rule::Var(instantiation, ty) => {
                let ty = ty.subst(x, v);
                Rule::Var(instantiation.clone(), ty)
            }
            Rule::Abs(tys) => {
                let tys = tys.iter().map(|ty| ty.subst(x, v)).collect();
                Rule::Abs(tys)
            }
        }
    }
}

impl DeriveNode {
    fn pretty_helper<'b, D, A, F, G, H>(
        &'b self,
        al: &'b D,
        config: &mut crate::util::printer::Config,
        // printer for types.
        f: &F,
        // printer for rules
        g: &G,
        // printer for assumptions
        h: &H,
    ) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
        F: Fn(&'b D, &mut crate::util::printer::Config, &'b Ty) -> pretty::DocBuilder<'b, D, A>,
        G: Fn(&'b D, &mut crate::util::printer::Config, &'b Rule) -> pretty::DocBuilder<'b, D, A>,
        H: Fn(pretty::DocBuilder<'b, D, A>) -> pretty::DocBuilder<'b, D, A>,
    {
        let body = match &self.rule {
            Rule::Var(_, original_ty) => self
                .expr
                .pretty(al, config)
                .append(al.line())
                .append(":")
                .append(al.line())
                .append(f(al, config, &self.ty))
                .append(al.line())
                .append("{{")
                .append(original_ty.pretty(al, config))
                .append("}}")
                .hang(2)
                .group(),
            _ => if OMIT_EXPR {
                al.text("e")
            } else {
                self.expr.pretty(al, config)
            }
            .append(al.space())
            .append(":")
            .append(al.line())
            .append(f(al, config, &self.ty))
            .hang(2)
            .group(),
        };
        let doc = al
            .text("(")
            .append(g(al, config, &self.rule))
            .append(")")
            .append(al.space());
        if PRINT_ASSUMPTION {
            let x = al.intersperse(self.context.iter().map(|x| x.pretty(al, config)), " ∧ ");
            doc.append(h(x))
        } else {
            doc
        }
        .append(al.space())
        .append("|-")
        .append(al.line())
        .append(body)
        .group()
    }
}

impl crate::util::printer::Pretty for DeriveNode {
    fn pretty<'b, D, A>(
        &'b self,
        al: &'b D,
        config: &mut crate::util::printer::Config,
    ) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        self.pretty_helper(
            al,
            config,
            &|al, config, ty| ty.pretty(al, config),
            &|al, _config, rule| al.text(rule.to_string()),
            &|x| x,
        )
    }

    fn pretty_color<'b, D>(
        &'b self,
        al: &'b D,
        config: &mut crate::util::printer::Config,
    ) -> pretty::DocBuilder<'b, D, pretty::termcolor::ColorSpec>
    where
        D: pretty::DocAllocator<'b, pretty::termcolor::ColorSpec>,
        D::Doc: Clone,
    {
        self.pretty_helper(
            al,
            config,
            &|al, config, ty| {
                let mut cs = pretty::termcolor::ColorSpec::new();
                cs.set_fg(Some(pretty::termcolor::Color::Green));
                ty.pretty(al, config).annotate(cs)
            },
            &|al, _config, rule| {
                let mut cs = pretty::termcolor::ColorSpec::new();
                cs.set_fg(Some(pretty::termcolor::Color::Blue));
                al.text(rule.to_string()).annotate(cs)
            },
            &|x| {
                let mut cs = pretty::termcolor::ColorSpec::new();
                cs.set_fg(Some(pretty::termcolor::Color::Red));
                x.annotate(cs)
            },
        )
    }
}

fn reset_expr_for_subsumption(expr: &mut G) {
    expr.aux.level_arg = Stack::new();
    expr.aux.id = Ident::fresh();
}

impl DeriveNode {
    fn conjoin(context: Stack<Atom>, expr: G, left: &Self, right: &Self) -> Self {
        let rule = Rule::Conjoin;
        let ty = match (left.ty.kind(), right.ty.kind()) {
            (TauKind::Proposition(c1), TauKind::Proposition(c2)) => {
                Ty::mk_prop_ty(Atom::mk_conj(c1.clone(), c2.clone()))
            }
            (_, _) => panic!("fatal: self.ty={} and c.ty={}", left.ty, right.ty),
        };
        DeriveNode {
            context,
            rule,
            expr,
            ty,
        }
    }
    fn disjoin(context: Stack<Atom>, expr: G, left: &Self, right: &Self) -> Self {
        let rule = Rule::Disjoin;
        let ty = match (left.ty.kind(), right.ty.kind()) {
            (TauKind::Proposition(c1), TauKind::Proposition(c2)) => {
                Ty::mk_prop_ty(Atom::mk_disj(c1.clone(), c2.clone()))
            }
            (_, _) => panic!("fatal: self.ty={} and c.ty={}", left.ty, right.ty),
        };
        DeriveNode {
            context,
            rule,
            expr,
            ty,
        }
    }
    fn quantify(context: Stack<Atom>, expr: G, node: &Self, ident: &Ident) -> Self {
        let rule = Rule::Univ;
        let ty = match node.ty.kind() {
            TauKind::Proposition(c1) => Ty::mk_prop_ty(Atom::mk_quantifier_int(
                crate::formula::QuantifierKind::Universal,
                *ident,
                c1.clone(),
            )),
            TauKind::PTy(_, _) | TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => panic!("fatal"),
        };
        DeriveNode {
            context,
            rule,
            expr,
            ty,
        }
    }
    fn iarrow(context: Stack<Atom>, expr: G, node: &Self, ident: &Ident) -> Self {
        let rule = Rule::IAbs;
        let ty = Ty::mk_iarrow(*ident, node.ty.clone());
        DeriveNode {
            context,
            rule,
            expr,
            ty,
        }
    }
    fn arrow(context: Stack<Atom>, expr: G, node: &Self, ts: Vec<Ty>) -> Self {
        let rule = Rule::Abs(ts.clone());
        let ty = Ty::mk_arrow(ts, node.ty.clone());
        DeriveNode {
            context,
            rule,
            expr,
            ty,
        }
    }
    fn iapp(context: Stack<Atom>, expr: G, node: &Self, op: &Op) -> Self {
        let rule = Rule::IApp(op.clone());
        let ty = match node.ty.kind() {
            TauKind::IArrow(x, t2) => t2.subst(x, op),
            _ => panic!("fatal"),
        };
        DeriveNode {
            context,
            rule,
            expr,
            ty,
        }
    }
    fn subsumption(context: Stack<Atom>, node: &Self, ty: Ty) -> Self {
        let rule = Rule::Subsumption;
        let mut expr = node.expr.clone();
        // reset the information
        reset_expr_for_subsumption(&mut expr);
        DeriveNode {
            context,
            rule,
            expr,
            ty,
        }
    }
    fn equivalence(context: Stack<Atom>, added: Stack<Atom>, node: &Self, ty: Ty) -> Self {
        let rule = Rule::Equivalence(added);
        let expr = node.expr.clone();
        DeriveNode {
            context,
            rule,
            expr,
            ty,
        }
    }
    fn poly(context: Stack<Atom>, node: &Self, x: Ident) -> Self {
        let rule = Rule::Poly(x);
        let expr = node.expr.clone();
        let ty = Ty::mk_poly_ty(x, node.ty.clone());
        DeriveNode {
            context,
            rule,
            expr,
            ty,
        }
    }
    fn app(context: Stack<Atom>, expr: G, pred_node: &Self) -> Self {
        let rule = Rule::App;
        let ty = match pred_node.ty.kind() {
            TauKind::Arrow(_, rt) => rt.clone(),
            TauKind::PTy(_, _) | TauKind::Proposition(_) | TauKind::IArrow(_, _) => {
                panic!("app rule is used for a wrong derivation")
            }
        };
        DeriveNode {
            context,
            rule,
            expr,
            ty,
        }
    }
    pub fn constraint(&self) -> Atom {
        self.context
            .iter()
            .fold(Atom::mk_true(), |acc, c| Atom::mk_conj(acc, c.clone()))
    }
}

#[derive(Clone)]
pub(super) struct Derivation {
    tree: Tree<DeriveNode>,
    pub coefficients: Stack<Ident>,
}

impl crate::util::printer::Pretty for Derivation {
    fn pretty<'b, D, A>(
        &'b self,
        al: &'b D,
        config: &mut crate::util::printer::Config,
    ) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone,
    {
        self.tree.pretty(al, config)
    }
    fn pretty_color<'b, D>(
        &'b self,
        al: &'b D,
        config: &mut crate::util::printer::Config,
    ) -> pretty::DocBuilder<'b, D, pretty::termcolor::ColorSpec>
    where
        D: pretty::DocAllocator<'b, pretty::termcolor::ColorSpec>,
        D::Doc: Clone,
    {
        self.tree.pretty_color(al, config)
    }
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

/// clone_config: used for inference configuration
#[derive(Clone, Copy)]
pub struct CloneConfiguration {
    mode_shared: bool,
    polymorphic: bool,
}

impl CloneConfiguration {
    pub fn new() -> Self {
        Self {
            mode_shared: false,
            polymorphic: false,
        }
    }
    pub fn mode_shared(mut self, value: bool) -> Self {
        self.mode_shared = value;
        self
    }
    pub fn polymorphic(mut self, value: bool) -> Self {
        self.polymorphic = value;
        self
    }
}

impl std::fmt::Display for CloneConfiguration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "mode_shared: {}", self.mode_shared)?;
        write!(f, "polymorphic: {}", self.polymorphic)
    }
}

impl Derivation {
    pub fn get_node_by_id<'a>(&'a self, node_id: ID) -> Node<'a, DeriveNode> {
        self.tree.get_node_by_id(node_id)
    }
    pub fn get_nodes_by_goal_id<'a>(
        &'a self,
        id: &'a Ident,
    ) -> impl Iterator<Item = Node<'a, DeriveNode>> + 'a {
        self.tree.filter(move |n| n.expr.aux.id == *id)
    }
    pub fn get_node_closest_to_root_by_goal_id<'a>(
        &'a self,
        id: &'a Ident,
    ) -> Option<Node<'a, DeriveNode>> {
        fn inner<'a>(
            d: &'a Derivation,
            id: &Ident,
            cur: ID,
            level: usize,
        ) -> Option<(Node<'a, DeriveNode>, usize)> {
            let node = d.tree.get_node_by_id(cur);
            if node.item.expr.aux.id == *id {
                Some((node, level))
            } else {
                let mut mx = None;
                for child in d.tree.get_children(node) {
                    match (inner(d, id, child.id, level + 1), &mx) {
                        (Some((n, level)), Some((_, cur))) if level < *cur => mx = Some((n, level)),
                        (Some((n, level)), None) => mx = Some((n, level)),
                        (_, _) => (),
                    }
                }
                mx
            }
        }
        inner(self, id, self.tree.root().id, 0).map(|(n, _)| n)
    }
    #[allow(dead_code)]
    fn get_node_by_level<'a>(
        &'a self,
        node_id: ID,
        level: &'a usize,
    ) -> impl Iterator<Item = Node<'a, DeriveNode>> + 'a {
        let node = self.tree.get_node_by_id(node_id);
        self.tree.filter_descendants(node, move |n| {
            n.expr.aux.level_arg.iter().any(|arg| arg == level)
        })
    }
    #[allow(dead_code)]
    pub fn get_types_by_level<'a>(
        &'a self,
        node_id: ID,
        level: &'a usize,
    ) -> impl Iterator<Item = Ty> + 'a {
        self.get_node_by_level(node_id, level)
            .map(|n| n.item.ty.clone())
    }
    #[allow(dead_code)]
    pub fn get_derivations_by_level<'a>(
        &'a self,
        node_id: ID,
        level: &'a usize,
    ) -> impl Iterator<Item = Self> + 'a {
        let node = self.tree.get_node_by_id(node_id);
        self.tree
            .filter_descendants(node, move |n| {
                n.expr.aux.level_arg.iter().any(|arg| arg == level)
            })
            .map(move |n| self.sub_derivation(&n.id))
    }

    pub fn single_node(n: DeriveNode) -> Self {
        Self {
            tree: Tree::singleton(n),
            coefficients: Stack::new(),
        }
    }

    pub fn rule_atom(context: Stack<Atom>, expr: G, ty: Ty) -> Self {
        let rule = Rule::Atom;
        let node = DeriveNode {
            context,
            rule,
            expr,
            ty,
        };
        Self {
            tree: Tree::singleton(node),
            coefficients: Stack::new(),
        }
    }

    pub fn rule_var(
        context: Stack<Atom>,
        expr: G,
        ty: Ty,
        original_ty: Ty,
        coefficients: Stack<Ident>,
        instantiations: Stack<Instantiation>,
    ) -> Self {
        let rule = Rule::Var(instantiations, original_ty);
        let node = DeriveNode {
            context,
            rule,
            expr,
            ty,
        };
        Self {
            tree: Tree::singleton(node),
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
            coefficients: concat_stacks([d1.coefficients, d2.coefficients].iter()),
        }
    }

    fn rule_multiples<I>(node: DeriveNode, derivations: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        let mut tree = Tree::singleton(node);
        let (_, coefficients) = derivations.fold((&mut tree, Stack::new()), |(t, coefs), d| {
            t.append_children(d.tree);
            let coefficients = concat_stacks([coefs, d.coefficients].iter());
            (t, coefficients)
        });
        Self { tree, coefficients }
    }
    pub fn rule_conjoin(context: Stack<Atom>, expr: G, d1: Self, d2: Self) -> Self {
        let root = DeriveNode::conjoin(context, expr, d1.tree.root().item, d2.tree.root().item);
        Self::rule_two_arg_inner(root, d1, d2)
    }
    pub fn rule_disjoin(context: Stack<Atom>, expr: G, d1: Self, d2: Self) -> Self {
        let root = DeriveNode::disjoin(context, expr, d1.tree.root().item, d2.tree.root().item);
        Self::rule_two_arg_inner(root, d1, d2)
    }
    pub fn rule_quantifier(context: Stack<Atom>, expr: G, d: Self, x: &Ident) -> Self {
        let root = DeriveNode::quantify(context, expr, d.tree.root().item, x);
        Self::rule_one_arg_inner(root, d)
    }
    pub fn rule_iarrow(context: Stack<Atom>, expr: G, d: Self, x: &Ident) -> Self {
        let root = DeriveNode::iarrow(context, expr, d.tree.root().item, x);
        Self::rule_one_arg_inner(root, d)
    }
    pub fn rule_arrow(context: Stack<Atom>, expr: G, d: Self, tys: Vec<Ty>) -> Self {
        let root = DeriveNode::arrow(context, expr, d.tree.root().item, tys);
        Self::rule_one_arg_inner(root, d)
    }
    pub fn rule_iapp(context: Stack<Atom>, expr: G, d: Self, o: &Op) -> Self {
        let root = DeriveNode::iapp(context, expr, d.tree.root().item, o);
        Self::rule_one_arg_inner(root, d)
    }
    pub fn rule_subsumption(context: Stack<Atom>, d: Self, ty: Ty) -> Self {
        let child = d.tree.root();
        let root = DeriveNode::subsumption(context, child.item, ty);
        Self::rule_one_arg_inner(root, d)
    }
    pub fn rule_equivalence(context: Stack<Atom>, mut d: Self, ty: Ty) -> Self {
        let child_id = d.tree.root().id;
        let original_context = &d.tree.root().item.context;
        let mut added = Stack::new();
        for c in original_context.iter() {
            let mut flag = true;
            for c2 in context.iter() {
                if c == c2 {
                    flag = false;
                    break;
                }
            }
            if flag {
                added.push_mut(c.clone());
            }
        }
        let root = DeriveNode::equivalence(context, added, d.tree.root().item, ty);
        reset_expr_for_subsumption(&mut d.tree.update_node_by_id(child_id).expr);
        Self::rule_one_arg_inner(root, d)
    }
    pub fn rule_app<I>(context: Stack<Atom>, expr: G, d1: Self, args: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        let root = DeriveNode::app(context, expr, &d1.tree.root().item);
        Self::rule_multiples(root, std::iter::once(d1).chain(args))
    }
    pub fn rule_polymorphic_type(context: Stack<Atom>, d: Self, x: Ident) -> Self {
        let item = d.tree.root().item;
        let root = DeriveNode::poly(context, item, x);
        Self::rule_one_arg_inner(root, d)
    }
    pub fn update_with_model(&mut self, m: &solver::Model) {
        self.tree.iter_mut(|item| {
            let mut ty = item.ty.clone();
            let mut rule = item.rule.clone();
            for (var, val) in m.model.iter() {
                ty = ty.subst(var, &Op::mk_const(*val));
                rule = rule.subst(var, &Op::mk_const(*val));
            }
            // in rule, there are types that should be updated with the model.
            // For example, ∀x. (y: int -> *[x = y]) -> *[true], and it's instantiated
            // to (y: int -> [a = y]) -> *[true]. Then Var in the derivation for the argument
            // of this type, there is a template variable that should be updated
            // after they are solved.
            item.ty = ty;
            item.rule = rule;
        });
    }
    pub fn root_ty(&self) -> &Ty {
        &self.tree.root().item.ty
    }
    /// get subderivation of `id`
    fn sub_derivation<'a>(&'a self, id: &'a ID) -> Self {
        let node = id.to_node(&self.tree);
        let tree = self.tree.subtree(node);
        // Assume constraints and coeffcients are saved in the main derivation, so
        // we omit them here.
        Derivation {
            tree,
            coefficients: Stack::new(),
        }
    }

    // Assume a derivation tree like
    //        π          ⋮
    //   ----------  ---------
    //   P x: *<c>   Q x: *<c2>
    //   ------------------------
    //     P x /\ Q x: *<c/\c2>
    // and (\y. y /\ Q x) (P x) -> P x /\ Q x
    // then, by using this function, we can create a derivation tree like
    //                   ⋮
    //   ----------  ---------
    //   y: *<c>   Q x: *<c2>
    //   ------------------------
    //     P x /\ Q x: *<c/\c2>
    // and returns [π]
    pub fn replace_derivation_at_level_with_var(
        &mut self,
        context: &Stack<Atom>,
        node_id: ID,
        level: &usize,
        var: Ident,
        fvints: &HashSet<Ident>,
    ) -> Vec<Self> {
        let var_expr = G::mk_var(var);
        let mut tree = self.tree.clone();
        let mut derivations = vec![];
        for node in self
            .tree
            .filter_descendants(self.tree.get_node_by_id(node_id), move |n| {
                n.expr.aux.level_arg.iter().any(|arg| arg == level)
            })
        {
            let mut sub_derivation = self.sub_derivation(&node.id);

            let instantiated_ty = node.item.ty.clone();
            let fvs = instantiated_ty.fv();
            let mut instantiations = Stack::new();

            // introduce the difference of the context to the result type
            let context_original = sub_derivation.tree.root().item.context.clone();

            let mut constraint = Atom::mk_true();
            for cnstr in context_original.iter() {
                if !context.iter().any(|c| c == cnstr) {
                    constraint = Atom::mk_conj(constraint, cnstr.clone());
                }
            }
            if !constraint.is_true() {
                let new_ty = instantiated_ty.conjoin_constraint_to_rty(&constraint);
                sub_derivation =
                    Self::rule_equivalence(context.clone(), sub_derivation, new_ty.clone());
            }

            for id in fvs.difference(fvints) {
                sub_derivation = Self::rule_polymorphic_type(context.clone(), sub_derivation, *id);
                instantiations.push_mut(Instantiation {
                    ident: *id,
                    op: Op::mk_var(*id),
                });
            }

            let d = Self::rule_var(
                context_original,
                var_expr.clone(),
                instantiated_ty,
                sub_derivation.root_ty().clone(),
                Stack::new(),
                instantiations,
            );

            derivations.push(sub_derivation);
            tree = tree.replace_subtree(node, d.tree);
        }
        self.tree = tree;
        derivations
    }
}

/// aux function for Derivation::update_parents
fn handle_rule_in_update_parents(
    t: &Tree<DeriveNode>,
    cur: ID,
    prev: ID,
) -> either::Either<Ty, (bool, DeriveNode)> {
    let n = t.get_node_by_id(cur).item;
    let ty = match &n.rule {
        Rule::Conjoin => {
            let cnstr = t
                .get_children(t.get_node_by_id(cur))
                .map(|child| match child.item.ty.kind() {
                    TauKind::Proposition(c) => c.clone(),
                    TauKind::PTy(_, _) | TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => {
                        panic!("not conjoin")
                    }
                })
                .fold(Atom::mk_true(), Atom::mk_conj);
            Ty::mk_prop_ty(cnstr)
        }
        Rule::Disjoin => {
            let cnstr = t
                .get_children(t.get_node_by_id(cur))
                .map(|child| match child.item.ty.kind() {
                    TauKind::Proposition(c) => c.clone(),
                    TauKind::PTy(_, _) | TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => {
                        panic!("not disjoin")
                    }
                })
                .fold(Atom::mk_false(), Atom::mk_disj);
            Ty::mk_prop_ty(cnstr)
        }
        Rule::Univ => {
            let children: Vec<_> = t
                .get_children(t.get_node_by_id(cur))
                .map(|child| child.item)
                .collect();
            assert_eq!(children.len(), 1);
            let cnstr = match children[0].ty.kind() {
                TauKind::Proposition(c) => c.clone(),
                TauKind::PTy(_, _) | TauKind::IArrow(_, _) | TauKind::Arrow(_, _) => {
                    panic!("not conjoin")
                }
            };
            let x = n.expr.univ().0;
            Ty::mk_prop_ty(Atom::mk_univ_int(x.id, cnstr))
        }
        Rule::IAbs => {
            let children: Vec<_> = t
                .get_children(t.get_node_by_id(cur))
                .map(|child| child.item)
                .collect();
            assert_eq!(children.len(), 1);
            let x = n.expr.abs().0;
            Ty::mk_iarrow(x.id, children[0].ty.clone())
        }
        Rule::Poly(x) => {
            let children: Vec<_> = t
                .get_children(t.get_node_by_id(cur))
                .map(|child| child.item)
                .collect();
            assert_eq!(children.len(), 1);
            Ty::mk_poly_ty(*x, children[0].ty.clone())
        }
        Rule::Abs(x) => {
            let children: Vec<_> = t
                .get_children(t.get_node_by_id(cur))
                .map(|child| child.item)
                .collect();
            assert_eq!(children.len(), 1);
            Ty::mk_arrow(x.clone(), children[0].ty.clone())
        }
        Rule::IApp(o) => {
            let children: Vec<_> = t
                .get_children(t.get_node_by_id(cur))
                .map(|child| child.item)
                .collect();
            assert_eq!(children.len(), 1);
            match children[0].ty.kind() {
                TauKind::IArrow(x, t) => t.subst(&x, &o),
                _ => panic!("program error"),
            }
        }
        Rule::App => {
            let children: Vec<_> = t
                .get_children(t.get_node_by_id(cur))
                .map(|child| child)
                .collect();
            assert!(children.len() >= 1);
            let node = t.get_node_by_id(prev).item;

            // case1: the updated child was in pred
            if node.expr.aux.id == children[0].item.expr.aux.id {
                // then we retrieve the updated children
                let children: Vec<_> = t
                    .get_children(t.get_node_by_id(cur))
                    .map(|child| child)
                    .collect();
                let pred = children[0].item.ty.clone();
                let body_tys: Vec<_> = children[1..]
                    .iter()
                    .map(|child| child.item.ty.clone())
                    .collect();
                let (arg_ty, ret_ty) = match pred.kind() {
                    TauKind::Arrow(arg, t) => (arg.clone(), t.clone()),
                    TauKind::PTy(_, _) | TauKind::Proposition(_) | TauKind::IArrow(_, _) => {
                        panic!("program error")
                    }
                };

                if !body_tys
                    .iter()
                    .filter(|x| !x.is_bot())
                    .zip(arg_ty.iter().filter(|x| !x.is_bot()))
                    .all(|(t1, t2)| t1 == t2)
                {
                    debug!("subsumption");
                    for body_ty in body_tys.iter() {
                        crate::pdebug!(body_ty);
                    }
                    debug!("<:");
                    for body_ty in arg_ty.iter() {
                        crate::pdebug!(body_ty);
                    }
                    panic!("subsumption invalid")
                }
                ret_ty.clone()
            }
            // case2: the updated child was in body
            else {
                // insert subsumption here
                for child in children[1..].iter() {
                    if node.expr.aux.id == child.item.expr.aux.id {
                        todo!();
                        //return (true, n.clone());
                    }
                }
                panic!("program error")
            }
        }
        Rule::Equivalence(_) | Rule::Subsumption => {
            let children: Vec<_> = t
                .get_children(t.get_node_by_id(cur))
                .map(|child| child.item)
                .collect();
            assert_eq!(children.len(), 1);
            return either::Right((true, n.clone()));
        }
        Rule::Var(_, _) | Rule::Atom => panic!("program error"),
    };
    either::Left(ty)
}

impl Derivation {
    /// Updates the types in the parents of the node `target_id` according to the updated types of the node `target_id`.
    fn update_parents(&mut self, target_id: ID) {
        self.tree
            .update_parent_until(target_id, |t, cur, prev| {
                let n = t.get_node_by_id(cur).item;
                let ty = match prev {
                    None => n.ty.clone(),
                    Some(prev) => match handle_rule_in_update_parents(t, cur, prev) {
                        either::Either::Left(ty) => ty,
                        either::Either::Right(ret) => return ret,
                    },
                };
                let n = t.get_node_by_id(cur).item;
                let n = DeriveNode {
                    context: n.context.clone(),
                    ty,
                    rule: n.rule.clone(),
                    expr: n.expr.clone(),
                };
                (false, n)
            })
            .unwrap();
    }
}
/// aux function for Derivation::update_expr_inner
fn retrieve_ty_alpha_renaming(t: &Ty, map: Stack<(Ident, Ident)>) -> Ty {
    let mut ty = t.clone();
    for (x, y) in map.iter() {
        ty = ty.rename(x, y);
    }
    ty
}
impl Derivation {
    fn handle_rule_in_update_expr_inner(
        &mut self,
        mut alpha_renaming_map: Stack<(Ident, Ident)>,
        children: Vec<ID>,
        node_id: ID,
        expr: &G,
        old_expr: &G,
        old_ty: &Ty,
    ) -> Rule {
        let n = self.get_node_by_id(node_id).item;
        match &n.rule {
            Rule::Conjoin => {
                let (g1, g2) = expr.conj();
                assert_eq!(children.len(), 2);
                self.update_expr_inner(children[0], g1, alpha_renaming_map.clone());
                self.update_expr_inner(children[1], g2, alpha_renaming_map.clone());
                Rule::Conjoin
            }
            Rule::Disjoin => {
                let (g1, g2) = expr.disj();
                assert_eq!(children.len(), 2);

                let c: Option<Constraint> = g1.clone().into();
                let c = c.unwrap();

                self.update_expr_inner(children[0], g1, alpha_renaming_map.clone());
                self.update_expr_inner(children[1], g2, alpha_renaming_map.clone());
                Rule::Disjoin
            }
            Rule::Var(i, ty) => {
                debug_assert!(expr.is_var());
                let ty = retrieve_ty_alpha_renaming(&ty, alpha_renaming_map.clone());
                Rule::Var(i.clone(), ty)
            }
            Rule::Atom => Rule::Atom,
            Rule::Univ => {
                let (v, _) = old_expr.univ();
                let (w, g) = expr.univ();
                if v.ty.is_int() && v.id != w.id {
                    alpha_renaming_map.push_mut((v.id, w.id));
                }

                assert_eq!(children.len(), 1);
                self.update_expr_inner(children[0], g, alpha_renaming_map.clone());
                Rule::Univ
            }
            Rule::IAbs => {
                let (w, g) = expr.abs();
                debug_assert!(w.ty.is_int());

                // After the subject expansion, some of the expr are placed as "true"
                // as a placeholder, which can be ignored here.
                match old_expr.kind() {
                    hes::GoalKind::Abs(_, _) => {
                        let (v, _) = old_expr.abs();
                        if v.ty.is_int() && v.id != w.id {
                            alpha_renaming_map.push_mut((v.id, w.id));
                            let (x, t) = old_ty.iarrow();
                            let ty = Ty::mk_iarrow(v.id, t.rename(x, &v.id));
                            self.tree.update_node_by_id(node_id).ty =
                                retrieve_ty_alpha_renaming(&ty, alpha_renaming_map.clone());
                        }
                    }
                    _ => (),
                }
                assert_eq!(children.len(), 1);
                self.update_expr_inner(children[0], g, alpha_renaming_map.clone());
                Rule::IAbs
            }
            Rule::Abs(tys) => {
                let (_, g) = expr.abs();
                let tys = tys
                    .into_iter()
                    .map(|t| retrieve_ty_alpha_renaming(&t, alpha_renaming_map.clone()))
                    .collect();
                assert_eq!(children.len(), 1);
                self.update_expr_inner(children[0], g, alpha_renaming_map.clone());
                Rule::Abs(tys)
            }
            Rule::IApp(op) => {
                let (x, _y) = expr.app();
                let mut op = op.clone();
                assert_eq!(children.len(), 1);
                self.update_expr_inner(children[0], x, alpha_renaming_map.clone());

                for (x, y) in alpha_renaming_map.iter() {
                    op = op.rename(x, y)
                }
                Rule::IApp(op)
            }
            Rule::App => {
                let (x, y) = expr.app();
                assert!(children.len() >= 1);
                self.update_expr_inner(children[0], x, alpha_renaming_map.clone());
                let c = self.get_node_by_id(children[0]).item.ty.rty();
                for i in 1..children.len() {
                    self.update_expr_inner(children[i], y, alpha_renaming_map.clone());
                }
                Rule::App
            }
            Rule::Subsumption | Rule::Poly(_) => {
                let rule = n.rule.clone();
                assert_eq!(children.len(), 1);
                self.update_expr_inner(children[0], &expr, alpha_renaming_map.clone());

                let mut expr = expr.clone();
                reset_expr_for_subsumption(&mut expr);
                self.tree.update_node_by_id(node_id).expr = expr.clone();
                rule
            }
            Rule::Equivalence(s) => {
                assert_eq!(children.len(), 1);
                let s = s.clone();
                self.update_expr_inner(children[0], &expr, alpha_renaming_map.clone());

                let mut expr = expr.clone();
                reset_expr_for_subsumption(&mut expr);

                // Unlike the case for subsumption, we replace the original one
                // so that we can refer to the more general type afterwards.
                self.tree.update_node_by_id(children[0]).expr = expr.clone();
                Rule::Equivalence(s)
            }
        }
    }
    fn update_expr_inner(
        &mut self,
        node_id: ID,
        expr: &G,
        alpha_renaming_map: Stack<(Ident, Ident)>,
    ) {
        let old_expr = self.tree.get_node_by_id(node_id).item.expr.clone();
        let old_ty = self.tree.get_node_by_id(node_id).item.ty.clone();

        let node = self.tree.update_node_by_id(node_id);
        node.expr = expr.clone();
        node.ty = retrieve_ty_alpha_renaming(&old_ty, alpha_renaming_map.clone());

        let children: Vec<_> = self
            .tree
            .get_children(node_id.to_node(&self.tree))
            .map(|child| child.id)
            .collect();
        self.tree.update_node_by_id(node_id).rule = self.handle_rule_in_update_expr_inner(
            alpha_renaming_map,
            children,
            node_id,
            expr,
            &old_expr,
            &old_ty,
        );
    }

    //// Updates the expressions, contexts, and variables used in types in the derivation tree.
    fn update_expr(&mut self, expr: &G) {
        let root_id = self.tree.root().id;
        self.update_expr_inner(root_id, expr, Stack::new());
    }

    fn finalize_subject_expansion(&mut self, reduction: &super::Reduction, target_node: ID) {
        self.update_parents(target_node);
        // finally replace the expressions in the derivation with the expr before the reduction
        self.update_expr(&reduction.before_reduction);
    }

    pub fn subject_expansion_pred(
        &mut self,
        context: &Stack<Atom>,
        node_id: ID,
        reduction: &super::Reduction,
        reduction_idx: usize,
    ) -> Vec<Derivation> {
        //let ri = &reduction.reduction_info;
        let ri = &reduction.reduction_infos[reduction_idx];
        let arg_derivations = self.replace_derivation_at_level_with_var(
            context,
            node_id,
            &ri.level,
            ri.arg_var.id,
            &reduction.fvints,
        );
        let mut arg_derivations_new: Vec<Derivation> = Vec::new();
        for arg_d in arg_derivations {
            let mut should_append = true;
            for d2 in arg_derivations_new.iter() {
                if arg_d.root_ty() == d2.root_ty() {
                    // already exists
                    highlight!("arg derivations already exists");
                    pdebug!(arg_d, " vs ", d2);
                    should_append = false;
                    break;
                }
            }
            if should_append {
                arg_derivations_new.push(arg_d);
            }
        }
        arg_derivations_new
    }

    fn extract_body_derivation(&self, target_node: ID, int_arg_count: usize) -> Tree<DeriveNode> {
        let mut cur = target_node.to_node(&self.tree);
        for _ in 0..int_arg_count {
            debug_assert!(matches!(cur.item.rule, Rule::Univ));
            let n = self.tree.get_one_child(cur);
            debug_assert!(matches!(n.item.rule, Rule::Disjoin));
            cur = self.tree.get_two_children(n).1;
        }
        self.tree.subtree(cur)
    }

    fn append_int_abs(
        &self,
        context: Stack<Atom>,
        tree: Tree<DeriveNode>,
        ri: &super::ReductionInfo,
    ) -> Tree<DeriveNode> {
        let dummy = G::mk_true();
        let n = DeriveNode {
            context,
            rule: Rule::IAbs,
            expr: dummy.clone(),
            ty: Tau::mk_iarrow(ri.old_id, tree.root().item.ty.clone()),
        };
        Tree::tree_with_child(n, tree)
    }

    fn append_int_app(
        &self,
        context: Stack<Atom>,
        tree: Tree<DeriveNode>,
        ri: &super::ReductionInfo,
    ) -> Tree<DeriveNode> {
        let dummy = G::mk_true();
        let op: Op = ri.arg.clone().into();
        let (x, ty) = tree.root().item.ty.iarrow();
        let n = DeriveNode {
            context: context,
            rule: Rule::IApp(op.clone()),
            expr: dummy.clone(),
            ty: ty.subst(x, &op),
        };
        Tree::tree_with_child(n, tree)
    }

    fn append_pred_abs(
        &self,
        context: Stack<Atom>,
        tree: Tree<DeriveNode>,
        arg_derivations: &Vec<Derivation>,
    ) -> Tree<DeriveNode> {
        let arg_tys: Vec<_> = arg_derivations
            .iter()
            .map(|d| d.root_ty().clone())
            .collect();
        let dummy = G::mk_true();
        let n = DeriveNode {
            context: context,
            rule: Rule::Abs(arg_tys.clone()),
            expr: dummy.clone(),
            ty: Tau::mk_arrow(arg_tys.clone(), tree.root().item.ty.clone()),
        };
        Tree::tree_with_child(n, tree)
    }

    fn append_pred_app(
        &self,
        context: Stack<Atom>,
        tree: Tree<DeriveNode>,
        arg_derivations: Vec<Derivation>,
    ) -> Tree<DeriveNode> {
        let pred_derivation = Derivation {
            coefficients: Stack::new(),
            tree: tree,
        };
        let dummy = G::mk_true();
        Derivation::rule_app(context, dummy, pred_derivation, arg_derivations.into_iter()).tree
    }

    pub fn append_abs(
        &self,
        context: Stack<Atom>,
        t: Tree<DeriveNode>,
        reduction: &super::Reduction,
        derivation_map: &HashMap<usize, Vec<Derivation>>,
    ) -> Tree<DeriveNode> {
        let mut subtree = t;
        for (idx, ri) in reduction.reduction_infos.iter().enumerate().rev() {
            match ri.reduction_type {
                super::ReductionType::Int(_) => {
                    subtree = self.append_int_abs(context.clone(), subtree, ri);
                }
                super::ReductionType::Pred(_) => {
                    let derivations = derivation_map.get(&idx).unwrap();
                    subtree = self.append_pred_abs(context.clone(), subtree, derivations);
                }
            }
        }
        subtree
    }
    pub fn append_app(
        &self,
        context: Stack<Atom>,
        t: Tree<DeriveNode>,
        reduction: &super::Reduction,
        mut derivation_map: HashMap<usize, Vec<Derivation>>,
    ) -> Tree<DeriveNode> {
        let mut subtree = t;
        for (idx, ri) in reduction.reduction_infos.iter().enumerate() {
            match ri.reduction_type {
                super::ReductionType::Int(_) => {
                    subtree = self.append_int_app(context.clone(), subtree, ri);
                    let op: Op = ri.arg.clone().into();
                    let x = ri.old_id;
                    for (k, v) in derivation_map.iter_mut() {
                        if k > &idx {
                            for d in v.iter_mut() {
                                // subst x in types and contexts with its argument
                                // recursively apply susbt to the rules
                                d.tree.iter_mut(|n| {
                                    n.ty = n.ty.subst(&x, &op);
                                    n.rule = n.rule.subst(&x, &op);
                                    n.context =
                                        n.context.iter().map(|a| a.subst(&x, &op)).collect();
                                });
                            }
                        }
                    }
                }
                super::ReductionType::Pred(_) => {
                    let derivations = derivation_map.remove(&idx).unwrap();
                    subtree = self.append_pred_app(context.clone(), subtree, derivations);
                }
            }
        }
        subtree
    }

    pub fn expand_node(&mut self, target_node: ID, reduction: &super::Reduction) {
        let mut derivation_map = HashMap::new();
        let mut int_arg_count = 0;
        let context = target_node.to_node(&self.tree).item.context.clone();
        let mut added = Stack::new();
        for (idx, ri) in reduction.reduction_infos.iter().enumerate() {
            match ri.reduction_type {
                super::ReductionType::Int(_) => {
                    //self.subject_expansion_int(target_node, reduction, idx);
                    int_arg_count += 1;
                    added.push_mut(Atom::mk_constraint(Constraint::mk_eq(
                        Op::mk_var(ri.old_id),
                        ri.arg.clone().into(),
                    )))
                }
                super::ReductionType::Pred(_) => {
                    let arg_derivation =
                        self.subject_expansion_pred(&context, target_node, reduction, idx);
                    derivation_map.insert(idx, arg_derivation);
                }
            }
        }
        let subtree = self.extract_body_derivation(target_node, int_arg_count);

        let constr = added.iter().cloned().fold(Atom::mk_true(), Atom::mk_conj);
        let ty = &subtree.root().item.ty;
        let ty = ty.conjoin_constraint_to_rty(&constr);
        let root = DeriveNode::equivalence(context.clone(), added, &subtree.root().item, ty);
        let subtree = Tree::tree_with_child(root, subtree);

        let subtree = self.append_abs(context.clone(), subtree, reduction, &derivation_map);
        let subtree = self.append_app(context.clone(), subtree, reduction, derivation_map);
        // top_id must be a fresh id assigned by the dummy expr
        let top_id = subtree.root().item.expr.aux.id;

        self.tree = self.tree.insert_partial_tree(target_node, |_| subtree).0;

        let target_node = self
            .get_node_closest_to_root_by_goal_id(&top_id)
            .unwrap()
            .id;
        self.finalize_subject_expansion(reduction, target_node);
    }

    pub fn collect_constraints<'a>(&'a self, structural: bool) -> impl Iterator<Item = Atom> + 'a {
        // collect all subsumptions
        pdebug!("collect_constraints");
        self.tree
            .filter(|n| matches!(n.rule, Rule::Subsumption))
            .map(move |n| {
                let ty = n.item.ty.clone();
                let constraints = n
                    .item
                    .context
                    .iter()
                    .fold(Atom::mk_true(), |acc, c| Atom::mk_conj(acc, c.clone()));
                let children: Vec<_> = self.tree.get_children(n).collect();
                assert_eq!(children.len(), 1);
                let child = &children[0];
                // conjoin constraint of the rule
                pdebug!(child.item.ty, " <: " ty);
                if structural {
                    Ty::check_subtype_structural(constraints.clone(), &child.item.ty, &ty).expect(
                        &format!("failed to check subtype: {} <: {}", child.item.ty, ty),
                    )
                } else {
                    Ty::check_subtype_result(constraints.clone(), &child.item.ty, &ty)
                        .unwrap_or_else(|| {
                            let mut coefficients = Stack::new();
                            let c = Ty::check_subtype(
                                &constraints,
                                &child.item.ty,
                                &ty,
                                &mut coefficients,
                            );
                            if coefficients.iter().next().is_some() {
                                panic!("failed to check subtype: {} <: {}", child.item.ty, ty)
                            }
                            c
                        })
                }
            })
    }

    pub fn collect_chcs<'a>(
        &'a self,
        structural: bool,
    ) -> impl Iterator<Item = chc::CHC<chc::Atom, Constraint>> + 'a {
        self.collect_constraints(structural)
            .map(|c| match c.to_chcs_or_pcsps() {
                either::Either::Left(c) => c.into_iter(),
                either::Either::Right(_) => panic!("failed to transform to chcs: {}", c),
            })
            .flatten()
    }
}

#[derive(Clone)]
struct IntroduceTemplateConfiguration {
    env: Stack<(Ident, Stack<(Ty, Ty)>)>,
    configuration: CloneConfiguration,
    ints: Stack<Ident>,
    univ_ints: Stack<Ident>,
}

impl IntroduceTemplateConfiguration {
    fn new(configuration: CloneConfiguration) -> Self {
        Self {
            env: Stack::new(),
            configuration,
            ints: Stack::new(),
            univ_ints: Stack::new(),
        }
    }
    fn get_var_ty(
        &self,
        v: &Ident,
        original_ty: &Ty,
        node: &DeriveNode,
    ) -> Option<(Ty, Stack<Instantiation>, Ty)> {
        self.env
            .iter()
            .find_map(|(x, y)| if x == v { Some(y) } else { None })
            .map(|ty_map| {
                // if its bot type, we don't have to care about it
                if node.ty.is_bot() {
                    &ty_map.iter().next().unwrap().1
                } else {
                    ty_map
                        .iter()
                        .find_map(|(t1, t2)| if original_ty == t1 { Some(t2) } else { None })
                        .expect(&format!("failed to find {v}: {}", node.pretty_display()))
                }
            })
            .cloned()
            .map(|x| (x.clone(), Stack::new(), x.clone()))
    }
    fn push_univ_int(&self, v: &Variable) -> Self {
        let mut x = self.clone();
        if v.ty.is_int() {
            x.univ_ints.push_mut(v.id);
        }
        x
    }
    fn push_int(&self, v: &Ident) -> Self {
        let mut x = self.clone();
        x.ints.push_mut(*v);
        x
    }
    fn push_env(&self, v: Ident, ty_map: Stack<(Ty, Ty)>) -> Self {
        let mut x = self.clone();
        x.env.push_mut((v, ty_map));
        x
    }
}

// struct for prepare_for_subject_expansion
type PSFE = IntroduceTemplateConfiguration;

fn calc_fv(
    configuration: &CloneConfiguration,
    ints: &Stack<Ident>,
    univ_ints: &Stack<Ident>,
    expr: &G,
) -> HashSet<Ident> {
    let mut fvs: HashSet<_> = ints.iter().cloned().collect();

    let expr_fvs = expr.fv();
    // if polymorphic type is enabled, insert all the variables in univ_ints to fvs
    // otherwise we only insert the variables that expr depend on explicitly in their body
    for x in univ_ints.iter() {
        if configuration.polymorphic || expr_fvs.contains(x) {
            fvs.insert(*x);
        }
    }
    fvs
}

impl Derivation {
    fn clone_with_template_inner(
        &self,
        node_id: ID,
        env: &mut HashMap<Ident, Stack<(Ty, Ty)>>,
        // when mode_shared is enabled, we prepare only one template type for
        // each lambda abstraction's argument even the type was τ₁ ∧ ⋯ ∧ τₙ
        // otherwise, we prepare the template for each type
        configuration: CloneConfiguration,
        ints: Stack<Ident>,
        univ_ints: Stack<Ident>,
    ) -> Self {
        // aux function for clone_wit template_inner
        let n = self.get_node_by_id(node_id);
        let expr = n.item.expr.clone();
        let context = Stack::new();
        let t = match &n.item.rule {
            Rule::Conjoin => {
                let (child1, child2) = self.tree.get_two_children(n);
                let d1 = self.clone_with_template_inner(
                    child1.id,
                    env,
                    configuration,
                    ints.clone(),
                    univ_ints.clone(),
                );
                let d2 = self.clone_with_template_inner(
                    child2.id,
                    env,
                    configuration,
                    ints.clone(),
                    univ_ints.clone(),
                );
                Self::rule_conjoin(context, expr, d1, d2)
            }
            Rule::Disjoin => {
                let (child1, child2) = self.tree.get_two_children(n);
                let d1 = self.clone_with_template_inner(
                    child1.id,
                    env,
                    configuration,
                    ints.clone(),
                    univ_ints.clone(),
                );
                let d2 = self.clone_with_template_inner(
                    child2.id,
                    env,
                    configuration,
                    ints.clone(),
                    univ_ints.clone(),
                );
                Self::rule_disjoin(context, expr, d1, d2)
            }
            Rule::Var(instantiations, original_ty) => {
                let v = expr.var();
                let (ty, instantiations, original_ty) = env
                    .get(v)
                    .map(|ty_map| {
                        // if its bot type, we don't have to care about it
                        if n.item.ty.is_bot() {
                            &ty_map.iter().next().unwrap().1
                        } else {
                            ty_map
                                .iter()
                                .find_map(
                                    |(t1, t2)| if original_ty == t1 { Some(t2) } else { None },
                                )
                                .expect(&format!("failed to find {v}: {}", n.item.pretty_display()))
                        }
                    })
                    .cloned()
                    .map(|x| (x.clone(), Stack::new(), x.clone()))
                    .unwrap_or_else(|| {
                        (
                            n.item.ty.clone(),
                            instantiations.clone(),
                            original_ty.clone(),
                        )
                    });
                self.tree.get_no_child(n);
                Self::rule_var(context, expr, ty, original_ty, Stack::new(), instantiations)
            }
            Rule::Univ => {
                let v = expr.univ().0;
                let univ_ints = if v.ty.is_int() {
                    univ_ints.push(v.id)
                } else {
                    univ_ints
                };
                let x = expr.univ().0.id;
                let child = self.tree.get_one_child(n);
                let d = self.clone_with_template_inner(
                    child.id,
                    env,
                    configuration,
                    ints.clone(),
                    univ_ints.clone(),
                );
                Self::rule_quantifier(context, expr, d, &x)
            }
            Rule::IAbs => {
                let x = expr.abs().0.id;
                let child = self.tree.get_one_child(n);
                let d = self.clone_with_template_inner(
                    child.id,
                    env,
                    configuration,
                    ints.push(x),
                    univ_ints.clone(),
                );
                Self::rule_iarrow(context, expr, d, &x)
            }
            Rule::Abs(_) => {
                let x = expr.abs().0;
                let (arg_ty, _) = n.item.ty.arrow();

                let mut arg_template_tys = Vec::new();
                let fvs = calc_fv(&configuration, &ints, &univ_ints, &expr);
                let mut ty_map = Stack::new();
                if configuration.mode_shared {
                    let arg_temp_ty = Ty::from_sty(&x.ty, &fvs);
                    arg_template_tys.push(arg_temp_ty.clone());
                    for t in arg_ty.iter() {
                        ty_map.push_mut((t.clone(), arg_temp_ty.clone()));
                    }
                } else {
                    for t in arg_ty.iter() {
                        // wrong: intersection type is required at this part (Ty::from_sty removes all the intersection types)
                        let mut fvs = fvs.clone();
                        let arg_temp_ty = t.clone_with_template(&mut fvs);
                        arg_template_tys.push(arg_temp_ty.clone());
                        ty_map.push_mut((t.clone(), arg_temp_ty.clone()));
                    }
                };
                let old = env.insert(x.id, ty_map);
                let child = self.tree.get_one_child(n);
                let d = self.clone_with_template_inner(
                    child.id,
                    env,
                    configuration,
                    ints.clone(),
                    univ_ints.clone(),
                );
                if let Some(ty) = old {
                    env.insert(x.id, ty);
                }

                Self::rule_arrow(context, expr, d, arg_template_tys)
            }
            Rule::IApp(_) => {
                let (_, e) = expr.app();
                let o: Op = e.clone().into();
                let child = self.tree.get_one_child(n);
                let d = self.clone_with_template_inner(
                    child.id,
                    env,
                    configuration,
                    ints,
                    univ_ints.clone(),
                );
                Self::rule_iapp(context, expr, d, &o)
            }
            Rule::Poly(_) => {
                // skip poly
                let child = self.tree.get_one_child(n);
                self.clone_with_template_inner(
                    child.id,
                    env,
                    configuration,
                    ints,
                    univ_ints.clone(),
                )
            }
            Rule::App => {
                let mut c = self.tree.get_children(n);
                let c1 = c.next().unwrap();
                let d1 = self.clone_with_template_inner(
                    c1.id,
                    env,
                    configuration,
                    ints.clone(),
                    univ_ints.clone(),
                );
                let ty1 = d1.root_ty().clone();
                let mut derivations: Vec<_> = c
                    .map(|c2| {
                        self.clone_with_template_inner(
                            c2.id,
                            env,
                            configuration,
                            ints.clone(),
                            univ_ints.clone(),
                        )
                    })
                    .collect();
                let (arg_tys, ret_ty) = ty1.arrow();

                if derivations.len() == 0 {
                    return Self::rule_app(context, expr, d1, derivations.into_iter());
                }

                if configuration.mode_shared {
                    derivations = vec![derivations.remove(0)];
                } else {
                    //panic!("unimplmented")
                }
                if derivations.len() != arg_tys.len() {
                    pdebug!("derivations vs arg_tys not match");
                    debug!("{}", configuration);
                    pdebug!(self.get_node_by_id(node_id).item);
                    debug!("derivations:");
                    for d in derivations.iter() {
                        pdebug!(d);
                        pdebug!("--end--")
                    }
                    pdebug!("arg_tys:");
                    for d in arg_tys.iter() {
                        pdebug!(d);
                        pdebug!("--end--")
                    }
                }
                assert_eq!(derivations.len(), arg_tys.len());
                let new_arg_tys = derivations.iter().map(|d| d.root_ty().clone()).collect();

                let mut fvs = calc_fv(&configuration, &ints, &univ_ints, &expr);

                let ret_tmp_ty = ret_ty.clone_with_template(&mut fvs);
                let ty3 = Ty::mk_arrow(new_arg_tys, ret_tmp_ty);

                let d3 = Self::rule_subsumption(context.clone(), d1, ty3);

                Self::rule_app(context, expr, d3, derivations.into_iter())
            }
            // skip subsumption and equivalence
            Rule::Equivalence(_) => {
                let child = self.tree.get_one_child(n);
                let d = self.clone_with_template_inner(
                    child.id,
                    env,
                    configuration,
                    ints,
                    univ_ints.clone(),
                );
                d
                //if d.root_ty() != &before_ty {
                //    //Self::rule_subsumption(context, d, ty)
                //    panic!()
                //} else {
                //    Self::rule_equivalence(context, d, ty)
                //}
            }
            Rule::Subsumption => {
                let child = self.tree.get_one_child(n);
                let d = self.clone_with_template_inner(
                    child.id,
                    env,
                    configuration,
                    ints,
                    univ_ints.clone(),
                );
                d
            }
            Rule::Atom => Self::rule_atom(context, expr, n.item.ty.clone()),
        };
        Derivation {
            tree: t.tree,
            coefficients: t.coefficients,
        }
    }
    pub fn clone_with_template(&self, configuration: CloneConfiguration) -> Self {
        highlight!("clone_with_template");
        pdebug!(self);
        let root = self.tree.root().id;
        let mut env = HashMap::new();
        let ints: Stack<Ident> = Stack::new();
        let univ_ints = Stack::new();
        let d = self.clone_with_template_inner(root, &mut env, configuration, ints, univ_ints);
        let n = self.get_node_by_id(root);
        match n.item.rule {
            Rule::Subsumption => (),
            _ => panic!("program error"),
        }
        let ty = n.item.ty.clone();
        Self::rule_subsumption(Stack::new(), d, ty)
    }

    /// prepare_for_subject_expansion_inner for abs expressions
    fn prepare_fse_abs(&self, node_id: ID, cfg: PSFE, t: &Ty) -> Self {
        let n = self.get_node_by_id(node_id);
        let expr = n.item.expr.clone();
        match t.kind() {
            TauKind::Proposition(_) => {
                let d = self.prepare_fse_inner(node_id, cfg);
                Self::rule_subsumption(Stack::new(), d, t.clone())
            }
            TauKind::PTy(_, _) => todo!(),
            TauKind::IArrow(x, t) => {
                let v = expr.abs().0;
                assert!(v.ty.is_int());
                let t = t.rename(x, &v.id);
                let x = v.id;
                let child = self.tree.get_one_child(n);
                let cfg = cfg.push_int(&x);
                let d = self.prepare_fse_abs(child.id, cfg, &t);
                Self::rule_iarrow(Stack::new(), expr, d, &x)
            }
            TauKind::Arrow(arg_ty, _) => {
                let x = expr.abs().0;
                let original_ty = n.item.ty.arrow().0.clone();
                let cfg = cfg.push_env(
                    x.id,
                    original_ty
                        .into_iter()
                        .zip(arg_ty.iter().cloned())
                        .collect(),
                );
                let child = self.tree.get_one_child(n);
                let d = self.prepare_fse_abs(child.id, cfg, t);
                Self::rule_arrow(Stack::new(), expr, d, arg_ty.clone())
            }
        }
    }

    /// prepare_for_subject_expansion_inner for app expressions
    fn prepare_fse_app(&self, node_id: ID, cfg: PSFE) -> Self {
        let n = self.get_node_by_id(node_id);
        let expr = n.item.expr.clone();
        let mut c = self.tree.get_children(n);
        let c1 = c.next().unwrap();
        let d1 = self.prepare_fse_inner(c1.id, cfg.clone());
        let ty1 = d1.root_ty().clone();

        let (arg_tys, _) = ty1.arrow();

        let arg_derivations = c.collect::<Vec<_>>();
        assert_eq!(arg_derivations.len(), arg_tys.len());

        let derivations: Vec<_> = arg_derivations
            .into_iter()
            .zip(arg_tys.iter())
            .map(|(c2, ty)| self.prepare_fse_abs(c2.id, cfg.clone(), ty))
            .collect();

        Self::rule_app(Stack::new(), expr, d1, derivations.into_iter())
    }

    /// prepare_for_subject_expansion_inner
    fn prepare_fse_inner(&self, node_id: ID, cfg: PSFE) -> Self {
        let n = self.get_node_by_id(node_id);
        let expr = n.item.expr.clone();
        let empty_ctx = Stack::new();
        let t = match &n.item.rule {
            Rule::Conjoin => {
                let (child1, child2) = self.tree.get_two_children(n);
                let d1 = self.prepare_fse_inner(child1.id, cfg.clone());
                let d2 = self.prepare_fse_inner(child2.id, cfg.clone());
                Self::rule_conjoin(empty_ctx, expr, d1, d2)
            }
            Rule::Disjoin => {
                let (child1, child2) = self.tree.get_two_children(n);
                let d1 = self.prepare_fse_inner(child1.id, cfg.clone());
                let d2 = self.prepare_fse_inner(child2.id, cfg.clone());
                Self::rule_disjoin(empty_ctx, expr, d1, d2)
            }
            Rule::Var(instantiations, original_ty) => {
                let v = expr.var();
                let (ty, instantiations, original_ty) =
                    cfg.get_var_ty(v, original_ty, &n.item).unwrap_or_else(|| {
                        (
                            n.item.ty.clone(),
                            instantiations.clone(),
                            original_ty.clone(),
                        )
                    });
                self.tree.get_no_child(n);
                let d = Self::rule_var(
                    empty_ctx,
                    expr.clone(),
                    ty.clone(),
                    original_ty,
                    Stack::new(),
                    instantiations,
                );

                let mut fvs = calc_fv(&cfg.configuration, &cfg.ints, &cfg.univ_ints, &expr);
                let t2 = ty.clone_with_template(&mut fvs);

                Self::rule_subsumption(Stack::new(), d, t2)
            }
            Rule::Univ => {
                let v = expr.univ().0;
                let cfg = cfg.push_univ_int(v);
                let x = expr.univ().0.id;
                let child = self.tree.get_one_child(n);
                let d = self.prepare_fse_inner(child.id, cfg);
                Self::rule_quantifier(empty_ctx, expr, d, &x)
            }
            Rule::Subsumption => {
                // ignore subsumption now
                let child = self.tree.get_one_child(n);
                let d = self.prepare_fse_inner(child.id, cfg);
                d
            }
            Rule::Atom => Self::rule_atom(empty_ctx, expr, n.item.ty.clone()),
            Rule::IAbs | Rule::Abs(_) => {
                unimplemented!()
            }
            Rule::IApp(_) => {
                let (_, e) = expr.app();
                let o: Op = e.clone().into();
                let child = self.tree.get_one_child(n);
                let d = self.prepare_fse_inner(child.id, cfg);
                Self::rule_iapp(empty_ctx, expr, d, &o)
            }
            Rule::App => self.prepare_fse_app(node_id, cfg),
            Rule::Poly(_) => {
                unimplemented!()
            }
            // skip subsumption and equivalence
            Rule::Equivalence(_) => panic!("program error"),
        };
        Derivation {
            tree: t.tree,
            coefficients: t.coefficients,
        }
    }
    /// Arranges the derivation for subject expansion
    ///
    /// This function
    ///  - introduces a new predicate variable after Var rule,
    ///  - removes context and pack the condition into the type.
    pub fn prepare_for_subject_expansion(&self) -> Self {
        pdebug!("prepare_for_subject_expansion"; title);
        let root = self.tree.root().id;
        let configuration = CloneConfiguration::new()
            .polymorphic(true)
            .mode_shared(false);
        let cfg = PSFE::new(configuration);
        let d = self.prepare_fse_inner(root, cfg);
        let ty = Ty::mk_prop_ty(Atom::mk_true());
        Self::rule_subsumption(Stack::new(), d, ty)
    }
    #[allow(dead_code)]
    /// This function is used to check that the derivation is well-formed
    /// if strict flag is enabled, then check_sanity checks if the given derivation tree
    /// is well-formed in the sense that all free variables of each type are bound.
    pub fn check_sanity(&self, strict: bool) -> bool {
        // now only check if app is sane since others are probably fine
        fn go(
            d: &Derivation,
            node_id: ID,
            ints: &Stack<Ident>,
            strict: bool,
            env: &HashTrieMap<Ident, Vec<Ty>>,
        ) -> bool {
            let n = d.get_node_by_id(node_id);
            let fvs = n.item.ty.fv();
            if strict
                && !fvs
                    .difference(&ints.iter().cloned().collect())
                    .next()
                    .is_none()
            {
                pdebug!("fail: ", n.item);
                panic!("derivation is not well-formed");
            };
            match &n.item.rule {
                Rule::Var(_, _ty) => {
                    d.tree.get_no_child(n);
                    //if !ints.iter().any(|y| x == y) {
                    //    let ty2 = env.get(&x).unwrap();
                    //    assert!(ty2.iter().any(|t| t == ty));
                    //}
                    true
                }
                Rule::Atom => {
                    let expr: Constraint = n.item.expr.clone().into();
                    let expr2 = n.item.ty.prop().clone().into();
                    assert_eq!(expr, expr2);
                    true
                }
                Rule::Conjoin | Rule::Disjoin => {
                    let (child1, child2) = d.tree.get_two_children(n);
                    go(d, child1.id, ints, strict, env) && go(d, child2.id, ints, strict, env)
                }
                Rule::IAbs => {
                    let x = n.item.expr.abs().0;
                    assert!(x.ty.is_int());
                    let ints = ints.push(x.id);
                    let child = d.tree.get_one_child(n);
                    go(d, child.id, &ints, strict, env)
                }
                Rule::Univ => {
                    let x = n.item.expr.univ().0;
                    assert!(x.ty.is_int());
                    let ints = ints.push(x.id);
                    let child = d.tree.get_one_child(n);
                    go(d, child.id, &ints, strict, env)
                }
                Rule::Poly(x) => {
                    let ints = ints.push(*x);
                    let child = d.tree.get_one_child(n);
                    go(d, child.id, &ints, strict, env)
                }
                Rule::IApp(_) | Rule::Subsumption | Rule::Equivalence(_) => {
                    let child = d.tree.get_one_child(n);
                    go(d, child.id, ints, strict, env)
                }
                Rule::Abs(_) => {
                    let (arg_ty, _) = n.item.ty.arrow();
                    let (x, _) = n.item.expr.abs();
                    let child = d.tree.get_one_child(n);
                    let env = env.insert(x.id, arg_ty.clone());
                    go(d, child.id, ints, strict, &env)
                }
                Rule::App => {
                    let children: Vec<_> = d.tree.get_children(n).collect();
                    let pred_ty = children[0].item.ty.clone();
                    let arg_tys: Vec<_> = children[1..]
                        .iter()
                        .map(|child| child.item.ty.clone())
                        .collect();
                    let body_tys = pred_ty.arrow().0;
                    // subsumption
                    if !body_tys
                        .iter()
                        .filter(|x| !x.is_bot())
                        .zip(arg_tys.iter().filter(|x| !x.is_bot()))
                        .all(|(t1, t2)| t1 == t2)
                    {
                        debug!("subsumption");
                        debug!("{}", d.get_node_by_id(node_id).item.expr);
                        for body_ty in body_tys.iter() {
                            crate::pdebug!(body_ty);
                        }
                        debug!("<:");
                        for body_ty in arg_tys.iter() {
                            crate::pdebug!(body_ty);
                        }
                        debug!("is wrong");
                        panic!();
                    }

                    children.iter().all(|c| go(d, c.id, ints, strict, env))
                }
            }
        }
        go(
            self,
            self.tree.root().id,
            &Stack::new(),
            strict,
            &HashTrieMap::new(),
        )
    }
}
