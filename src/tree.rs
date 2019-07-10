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
    top: Rc<Node<P, D>>,

    /// Number of node in this tree.
    count: usize,
}

///
/// Tree impl.
///
impl<P: Prefixable, D> Tree<P, D> {
    pub fn get_node(&self, prefix: &P) -> NodeIterator<P, D> {
        let mut curr = Some(self.top.clone());
        let mut matched: Option<Rc<Node<P, D>>> = None;

        while let Some(node) = curr {
            if node.prefix().len() <= prefix.len() && node.prefix().contain(prefix) {
                if node.prefix().len() == prefix.len() {
                    return NodeIterator::from_node(node)
                }
            }

            matched = Some(node.clone());
            curr = node.child(prefix.bit_at(curr.prefix().len()));
        }

        /*
    NodePtr new_node;
    NodePtr curr = top_;
    NodePtr matched = nullptr;

    while (curr
           && curr->prefix().len() <= prefix.len()
           && curr->prefix().match(prefix)) {
      // Found the exact node.                                                                                                                                                                                                                
      if (curr->prefix().len() == prefix.len())
        return iterator(curr);

      matched = curr;
      curr = curr->child(prefix.bit_at(curr->prefix().len()));
    }

    if (curr == NULL) {
      new_node = get_node_for(prefix);
      if (matched)
        matched->set_child(new_node);
      else
        top_ = new_node;
    }
    else {
      new_node = make_shared<Node>(curr->prefix(), prefix);
      new_node->set_child(curr);

      if (matched)
        matched->set_child(new_node);
      else
        top_ = new_node;

      if (new_node->prefix().len() != prefix.len()) {
        matched = new_node;
        new_node = get_node_for(prefix);
        matched->set_child(new_node);
      }
    }

    return iterator(new_node);

*/
        NodeIterator::from_node(self.top.clone())
    }
}

///
///
///
impl<P: Prefixable, D> IntoIterator for Tree<P, D> {
    type Item = Rc<Node<P, D>>;
    type IntoIter = NodeIterator<P, D>;

    fn into_iter(self) -> Self::IntoIter {
        NodeIterator::<P, D> {
            node: self.top.clone()
        }
    }
}

pub struct NodeIterator<P: Prefixable, D> {
    node: Rc<Node<P, D>>,
}

impl<P: Prefixable, D> NodeIterator<P, D> {
    pub fn from_node(node: Rc<Node<P, D>>) -> NodeIterator<P, D> {
        NodeIterator::<P, D> {
            node: node.clone()
        }
    }
}

impl<P: Prefixable, D> Iterator for NodeIterator<P, D> {
    type Item = Rc<Node<P, D>>;
    fn next(&mut self) -> Option<Rc<Node<P, D>>> {
        self.node.next()
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
    pub fn new(prefix: P) -> Node<P, D> {
        Node {
            parent: RefCell::new(None),
            children: [RefCell::new(None), RefCell::new(None)],
            prefix: prefix,
            data: RefCell::new(None),
        }
    }

    /// Return reference to prefix.
    pub fn prefix(&self) -> &P {
        &self.prefix
    }

    /// Return one of child node - left(0) or right(1)
    pub fn child(&self, bit: Child) -> Option<Rc<Node<P, D>>> {
        self.children[bit as usize].borrow().clone()
    }

    /// Return parent node.
    pub fn parent(&self) -> Option<Rc<Node<P, D>>> {
        self.parent.borrow().clone()
    }

    /// Set child at left or right.
    fn set_child_at(&self, child: Rc<Node<P, D>>, bit: Child) {
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
