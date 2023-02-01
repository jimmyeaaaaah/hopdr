use petgraph::graphmap::GraphMap;
use petgraph::Directed;
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
// However, in hopdr's usecase, merging two nodes happens everywhere.
// I guess it does not cause any bottleneck imeediately, since basically the slowest
// part of hopdr is SMT solving.
// However, we should be aware that this part will be a bottleneck.
//
// I think it is not so much hard to implement myself this tree library
// without depending on any other external crate since we don't use almost nothing
// other than add_node and connect two nodes.
// So, if I have a time to do so, I'll do so...
pub struct Tree<T> {
    graph: GraphMap<ID, (), Directed>,
    items: HashMap<ID, T>,
    root: ID,
}

#[derive(Copy, Clone)]
pub struct Node<'a, T> {
    pub item: &'a T,
    id: ID,
}

impl<T> Tree<T> {
    pub fn singleton(item: T) -> Tree<T> {
        let root = gen_id();
        let mut graph = GraphMap::new();
        graph.add_node(root);
        let mut items = HashMap::new();
        items.insert(root, item);
        Tree { graph, items, root }
    }
    pub fn tree_from_children<I>(item: T, children: I) -> Tree<T>
    where
        I: Iterator<Item = Tree<T>>,
    {
        let mut tree = Self::singleton(item);
        for child in children {
            // add nodes
            for node in child.graph.nodes() {
                tree.graph.add_node(node);
            }
            for (a, b, _) in child.graph.all_edges() {
                tree.graph.add_edge(a, b, ()).unwrap()
            }
            tree.graph.add_edge(tree.root, child.root, ());
            tree.items.extend(child.items)
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
        let id = self.root;
        let item = self.items.get(&id).unwrap();
        Node { id, item }
    }
    pub fn get_children<'a>(&'a self, node: Node<'a, T>) -> impl Iterator<Item = Node<'a, T>> {
        let id = node.id;
        self.graph.edges(id).map(move |(_, id, _)| {
            let item = self.items.get(&id).unwrap();
            Node { item, id }
        })
    }
    fn search<F>(&self, check: F) -> &T
    where
        F: Fn(&T) -> bool,
    {
        unimplemented!()
    }
}

#[test]
fn tree_basics() {
    let t1 = Tree::singleton(2);
    let t2 = Tree::singleton(2);
    let t = Tree::tree_with_two_children(1, t1, t2);
    let root = t.root();
    assert_eq!(*root.item, 1);
    for child in t.get_children(root) {
        assert_eq!(*child.item, 2)
    }
}
