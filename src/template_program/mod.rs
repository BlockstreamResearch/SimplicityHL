mod witness;

use std::sync::Arc;

use crate::named;
use crate::Arguments;

pub use self::witness::TemplateProgramWitness;

/// A program which has been compiled to Simplicity, except that its parameters have not been
/// resolved.
pub struct TemplateProgram {
    inner: Arc<named::CommitNode>,
}

impl TemplateProgram {
    /// Creates a [`TemplateProgram`] from a [`named::ConstructNode`] output from the compiler.
    ///
    /// # Panics
    ///
    /// Panics if given a program that doesn't typecheck -- that is, which has infinitely sized
    /// types or whose source and target types are non-unit and non-free.
    pub(crate) fn from_construct_node<'brand>(node: &named::ConstructNode<'brand>) -> Self {
        Self {
            inner: named::finalize_types(node)
                .expect("SimplicityHL types are 1->1 and have finite types by construction"),
        }
    }

    /// Instantiates the templated program with the given arguments.
    ///
    /// ## Precondition
    ///
    /// The supplied `arguments` are consistent with the program's parameters.
    /// Call [`Arguments::is_consistent`] before calling this method!
    pub fn instantiate(self, _: Arguments) -> Arc<named::CommitNode> {
        self.inner
    }
}
