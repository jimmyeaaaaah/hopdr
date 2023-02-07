use std::collections::HashMap;

use crate::util::global_counter;

#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash, PartialOrd, Ord)]
pub struct ID(u64);

fn gen_id() -> ID {
    ID(global_counter())
}

// using petgraph's Graph as the core graph library is not a good choice since
// it seems not to support merging two graphs in an efficient way
// (c.f. https://github.com/petgraph/petgraph/issues/276)
// In hopdr's usecase, merging two nodes happens everywhere.
// I guess it does not cause any bottleneck immediately, since basically the slowest
// part of hopdr is SMT solving.
// However, we should be aware that this part will be a bottleneck.
//
// I think it is not so much hard to implement myself this tree library
// without depending on any other external crate since we don't use almost nothing
// other than add_node and connect two nodes.
// So, if I have a time to do so, I'll do so...

#[derive(Clone)]
struct IDTree {
    //nodes: Vec<ID>,
    edges: HashMap<ID, Vec<ID>>,
    parent: HashMap<ID, ID>,
}

impl IDTree {
    fn new() -> Self {
        IDTree {
            edges: HashMap::new(),
            parent: HashMap::new(),
        }
    }
    fn add_node(&mut self, node: ID) {
        self.edges.insert(node, Vec::new());
    }
    fn add_edge(&mut self, from: ID, to: ID) {
        debug_assert!(self.edges.contains_key(&from) && self.edges.contains_key(&to));
        self.edges.get_mut(&from).unwrap().push(to);
        let r = self.parent.insert(to, from);
        debug_assert!(r.is_none())
    }
    fn nodes<'a>(&'a self) -> impl Iterator<Item = ID> + 'a {
        self.edges.keys().copied()
    }
    fn all_edges<'a>(&'a self) -> impl Iterator<Item = (ID, ID)> + 'a {
        self.edges
            .iter()
            .map(|(x, v)| v.iter().map(move |y| (*x, *y)))
            .flatten()
    }
    fn get_parent(&self, node: ID) -> Option<ID> {
        self.parent.get(&node).copied()
    }
    fn edges<'a>(&'a self, node: ID) -> impl Iterator<Item = (ID, ID)> + 'a {
        self.edges
            .get(&node)
            .unwrap()
            .iter()
            .map(move |y| (node, *y))
    }
}

#[derive(Clone)]
pub struct Tree<T> {
    graph: IDTree,
    items: HashMap<ID, T>,
    root: ID,
}

#[derive(Copy, Clone)]
pub struct Node<'a, T> {
    pub item: &'a T,
    id: ID,
}

impl<T> Tree<T> {
    fn get_node_by_id<'a>(&'a self, id: ID) -> Node<'a, T> {
        let item = self.items.get(&id).unwrap();
        Node { item, id }
    }
    pub fn singleton(item: T) -> Tree<T> {
        let root = gen_id();
        let mut graph = IDTree::new();
        graph.add_node(root);
        let mut items = HashMap::new();
        items.insert(root, item);
        Tree { graph, items, root }
    }
    pub fn append_children(&mut self, child: Tree<T>) {
        for node in child.graph.nodes() {
            self.graph.add_node(node);
        }
        for (a, b) in child.graph.all_edges() {
            let n = self.graph.add_edge(a, b);
        }
        self.graph.add_edge(self.root, child.root);
        self.items.extend(child.items)
    }
    pub fn tree_from_children<I>(item: T, children: I) -> Tree<T>
    where
        I: Iterator<Item = Tree<T>>,
    {
        let mut tree = Self::singleton(item);
        for child in children {
            tree.append_children(child)
        }
        tree
    }
    pub fn tree_with_child(item: T, child: Tree<T>) -> Tree<T> {
        Self::tree_from_children(item, std::iter::once(child))
    }
    pub fn tree_with_two_children(item: T, child1: Tree<T>, child2: Tree<T>) -> Tree<T> {
        Self::tree_from_children(item, std::iter::once(child1).chain(std::iter::once(child2)))
    }
    pub fn root(&self) -> Node<T> {
        self.get_node_by_id(self.root)
    }
    pub fn get_children<'a>(&'a self, node: Node<'a, T>) -> impl Iterator<Item = Node<'a, T>> {
        let id = node.id;
        self.graph
            .edges(id)
            .map(move |(_, id)| self.get_node_by_id(id))
    }
    pub fn search<'a, F>(&'a self, check: F) -> Option<Node<'a, T>>
    where
        F: Fn(&T) -> bool,
    {
        self.graph.nodes().find_map(|id| {
            let node = self.get_node_by_id(id);
            if check(node.item) {
                Some(node)
            } else {
                None
            }
        })
    }
    pub fn filter<'a, P>(&'a self, predicate: P) -> impl Iterator<Item = Node<'a, T>>
    where
        P: 'a + Fn(&T) -> bool,
    {
        self.graph.nodes().filter_map(move |id| {
            let node = self.get_node_by_id(id);
            if predicate(node.item) {
                Some(node)
            } else {
                None
            }
        })
    }
    pub fn iter_mut<'a, P>(&'a mut self, f: P)
    where
        P: Fn(&mut T),
    {
        self.items.iter_mut().for_each(|(key, item)| f(item))
    }
    fn parent(&self, node: ID) -> Option<ID> {
        self.graph.get_parent(node)
    }
    pub fn traverse_parent_until<'a, P>(
        &'a self,
        base: Node<'a, T>,
        predicate: P,
    ) -> Option<Node<'a, T>>
    where
        P: Fn(&T) -> bool,
    {
        let mut cur = base;
        loop {
            if predicate(cur.item) {
                break Some(cur);
            }
            if let Some(parent_id) = self.parent(cur.id) {
                cur = self.get_node_by_id(parent_id)
            } else {
                break None;
            }
        }
    }
}

#[test]
fn tree_basics() {
    let t1 = Tree::singleton(3);
    let t3 = Tree::tree_with_child(2, t1);
    let t2 = Tree::singleton(2);
    let t = Tree::tree_with_two_children(1, t3, t2);
    let root = t.root();
    assert_eq!(*root.item, 1);
    for child in t.get_children(root) {
        assert_eq!(*child.item, 2);
        for child2 in t.get_children(child) {
            assert_eq!(*child2.item, 3);

            // parent
            let parent = t.parent(child2.id).unwrap();
            assert_eq!(parent, child.id);

            assert!(t.traverse_parent_until(child2, |v| *v == 1).is_some())
        }
    }
    assert!(t.search(|x| *x == 4).is_none());
    assert!(t.search(|x| *x == 3).is_some());

    assert_eq!(t.filter(|x| *x == 2).count(), 2)
}
