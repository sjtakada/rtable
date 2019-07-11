//
// Routing Table
//   Copyright (C) 2019 Toshiaki Takada
//

use std::cell::Ref;
use std::cell::RefCell;
use std::rc::Rc;
use std::iter::Iterator;
use std::iter::IntoIterator;

use super::prefix::*;

///
/// Tree struct.
///
pub struct Tree<P: Prefixable, D> {
    /// Top Node.
    top: RefCell<Option<Rc<Node<P, D>>>>,

    /// Number of node in this tree.
    count: usize,
}

///
/// Tree impl.
///
impl<P: Prefixable, D> Tree<P, D> {
    /// Get node with given prefix, create one if it doesn't exist.
    pub fn get_node(&self, prefix: &P) -> NodeIterator<P, D> {
        let mut matched: Option<Rc<Node<P, D>>> = None;
        let mut curr: Option<Rc<Node<P, D>>> = self.top.borrow_mut().clone();
        let mut new_node: Rc<Node<P, D>>;
        
        // have lambda to do the loop condition.
        let f = |curr: Option<Rc<Node<P, D>>>, prefix: &P| {
            let node = curr.unwrap();
            node.prefix.len() <= prefix.len() && node.prefix().contain(prefix)
        };

        while curr.is_some() && f(curr.clone(), prefix) {
            let node = curr.clone().unwrap();
            if node.prefix().len() == prefix.len() {
                return NodeIterator::from_node(node)
            }

            matched = Some(node.clone());
            curr = node.child_with(prefix.bit_at(node.prefix().len()));
        }

        match curr {
            None => {
                new_node = Rc::new(Node::new(prefix));
                match matched {
                    Some(node) => {
                        Node::<P, D>::set_child(node, new_node.clone());
                    },
                    None => {
                        self.top.replace(Some(new_node.clone()));
                    }
                }

            },
            Some(node) => {
                new_node = Rc::new(Node::from_common(node.prefix(), prefix));
                Node::<P, D>::set_child(new_node.clone(), node.clone());

                match matched {
                    Some(node) => {
                        Node::<P, D>::set_child(node, new_node.clone());
                    },
                    None => {
                        self.top.replace(Some(new_node.clone()));
                    }
                }

                if new_node.prefix().len() != prefix.len() {
                    matched = Some(new_node.clone());
                    new_node = Rc::new(Node::new(prefix));
                    Node::<P, D>::set_child(matched.unwrap().clone(), new_node.clone());
                }
            }
        }

        NodeIterator::from_node(new_node)
    }
}

///
///
///
impl<P: Prefixable, D> IntoIterator for Tree<P, D> {
    type Item = Rc<Node<P, D>>;
    type IntoIter = NodeIterator<P, D>;

    fn into_iter(self) -> Self::IntoIter {
        let top = self.top.borrow_mut().clone();

        NodeIterator::<P, D> {
            node: top,
        }
    }
}

pub struct NodeIterator<P: Prefixable, D> {
    node: Option<Rc<Node<P, D>>>,
}

impl<P: Prefixable, D> NodeIterator<P, D> {
    pub fn from_node(node: Rc<Node<P, D>>) -> NodeIterator<P, D> {
        NodeIterator::<P, D> {
            node: Some(node.clone())
        }
    }
}

impl<P: Prefixable, D> Iterator for NodeIterator<P, D> {
    type Item = Rc<Node<P, D>>;
    fn next(&mut self) -> Option<Rc<Node<P, D>>> {
        match &self.node {
            Some(node) => node.next().clone(),
            None => None
        }
    }
}

///
/// Enum Child.
///
pub enum Child {
    Left = 0,
    Right = 1,
}

///
/// Node struct.
///
pub struct Node<P: Prefixable, D> {
    /// Parent Node.
    parent: RefCell<Option<Rc<Node<P, D>>>>,

    /// Child Nodes.
    children: [RefCell<Option<Rc<Node<P, D>>>>; 2],

    /// Prefix associated with this node.
    prefix: P,

    /// Data.
    data: RefCell<Option<D>>,
}

///
/// Node impl.
///
impl<P: Prefixable, D> Node<P, D> {
    /// Return new node.
    pub fn new(prefix: &P) -> Node<P, D> {
        Node {
            parent: RefCell::new(None),
            children: [RefCell::new(None), RefCell::new(None)],
            prefix: P::from_prefix(prefix),
            data: RefCell::new(None),
        }
    }

    /// Return new node with common prefix.
    pub fn from_common(prefix1: &P, prefix2: &P) -> Node<P, D> {
        let pcommon = P::from_common(prefix1, prefix2);
        Self::new(&pcommon)
    }

    /// Return reference to prefix.
    pub fn prefix(&self) -> &P {
        &self.prefix
    }

    /// Return one of child node - left(0) or right(1)
    pub fn child(&self, bit: Child) -> Option<Rc<Node<P, D>>> {
        self.children[bit as usize].borrow().clone()
    }

    /// Return one of child node - left(0) or right(1)
    pub fn child_with(&self, bit: u8) -> Option<Rc<Node<P, D>>> {
        self.children[bit as usize].borrow().clone()
    }

    /// Return parent node.
    pub fn parent(&self) -> Option<Rc<Node<P, D>>> {
        self.parent.borrow().clone()
    }

    /// Set given node as a child at left or right
    fn set_child(parent: Rc<Node<P, D>>, child: Rc<Node<P, D>>) {
        let bit = child.prefix().bit_at(parent.prefix().len());
        parent.set_child_at(child.clone(), bit);
        child.set_parent(parent.clone());
    }

    /// Set child at left or right.
    fn set_child_at(&self, child: Rc<Node<P, D>>, bit: u8) {
        self.children[bit as usize].replace(Some(child.clone()));
    }

    /// Set parent.
    pub fn set_parent(&self, parent: Rc<Node<P, D>>) {
        self.parent.replace(Some(parent.clone()));
    }

    /// Set dats.
    pub fn set_data(&self, data: D) {
        self.data.replace(Some(data));
    }

    /// Unset data.
    pub fn unset_data(&self) {
        self.data.replace(None);
    }

    /// Return reference to data.
    pub fn data(&self) -> Ref<Option<D>> {
        self.data.borrow()
    }

    /// Return true if node has child or data.
    pub fn is_locked(&self) -> bool {
        if let Some(_) = *self.children[Child::Left as usize].borrow() {
            true
        }
        else if let Some(_) = *self.children[Child::Right as usize].borrow() {
            true
        }
        else if let Some(_) = *self.data.borrow() {
            true
        }
        else {
            false
        }
    }

    /// Return next Node.  TODO: refactoring
    pub fn next(&self) -> Option<Rc<Node<P, D>>> {
        if let Some(node) = self.child(Child::Left) {
            return Some(node.clone())
        }
        else if let Some(node) = self.child(Child::Right) {
            return Some(node.clone())
        }
        else {
            if let Some(parent) = self.parent() {
                if let Some(l_child) = parent.child(Child::Left) {
                    if l_child.as_ref() as *const _ == self as *const _ {
                        if let Some(r_child) = parent.child(Child::Right) {
                            return Some(r_child.clone())
                        }
                    }
                }

                let mut curr = parent;
                while let Some(parent) = curr.parent() {
                    if let Some(l_child) = parent.child(Child::Left) {
                        if l_child.as_ref() as *const _ == curr.as_ref() as *const _ {
                            if let Some(r_child) = parent.child(Child::Right) {
                                return Some(r_child.clone())
                            }
                        }
                    }
                    curr = parent;
                }
            }
        }

        None
    }
}
