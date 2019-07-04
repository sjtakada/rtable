//
// Routing Table
//   Copyright (C) 2019 Toshiaki Takada
//

use std::cell::Ref;
use std::cell::RefCell;
use std::rc::Rc;

///
/// Tree struct.
///
pub struct Tree<P, D> {
    /// Top Node.
    top: Rc<Node<P, D>>,

    /// Number of node in this tree.
    count: usize,
}

///
/// Tree impl.
///
impl<P, D> Tree<P, D> {

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
pub struct Node<P, D> {
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
impl<P, D> Node<P, D> {
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

    /*
    /// Return next Node.
    pub fn next(&self) -> Rc<Node<P, D>> {
        if let Some(node) = *self->childlen[Child::Left as usize].borrow() {
            node.clone()
        }
        else if let Some(node) = *self->childlen[Child::Right as usize].borrow() {
            node.clone()
        }
        else {
            let node = self;

            while let Some(parent) = *self->parent.borrow() {
                if parent->children[Child::Left as usize] == self && let Some(node) = *parent->children[Child::Right as usize].borrow() {
                    return node.clone()
                }

                curr = curr->parent;
            }
        }

*/
}
