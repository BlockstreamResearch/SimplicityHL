use std::collections::HashMap;

use crate::pattern::BasePattern;
use crate::str::Identifier;

/// The live bindings of a scope stack, in the shape that makes identifier
/// extraction O(distance) instead of O(live bindings).
///
/// ## Input pattern
///
/// The bindings form the _input pattern_, the right-nested product
///
/// ```text
/// product(binding_n, product(binding_{n-1}, ..., product(binding_1, binding_0)))
/// ```
///
/// All valid input values match the input pattern.
/// Inner scopes occur higher in the tree than outer scopes.
/// Later assignments occur higher in the tree than earlier assignments.
///
/// ## Example
///
/// The stack `[[p1], [p2, p3]]` corresponds to a nested product pattern:
///
/// ```text
///    .
///   / \
/// p3   .
///     / \
///   p2   p1
/// ```
///
/// ## Invariants
///
/// - `binding_starts` is nonempty and non-decreasing; its last entry is the
///   index where the current (innermost) scope's bindings begin.
/// - Every index stored in `identifiers` is in range of `bindings`, and
///   every identifier's indices are ascending: the last one is the binding
///   in effect, earlier ones are shadowed by it.
/// - All mutations go through [`insert`](Self::insert),
///   [`push_scope`](Self::push_scope) and [`pop_scope`](Self::pop_scope),
///   which restore the invariants before returning.
#[derive(Debug)]
pub(super) struct ScopeBindings {
    /// The patterns of all live bindings, in insertion order: the oldest
    /// binding first, the newest last.
    bindings: Vec<BasePattern>,
    /// For every live identifier, the indices into `bindings` of the
    /// bindings that bind it, oldest first. The last index is the binding
    /// in effect; earlier ones are shadowed and come back into effect when
    /// their scope pops.
    identifiers: HashMap<Identifier, Vec<usize>>,
    /// For every scope on the stack, the index in `bindings` where that
    /// scope starts. Popping a scope truncates the bindings and restores
    /// the shadowed identifiers.
    binding_starts: Vec<usize>,
}

impl ScopeBindings {
    /// Create bindings whose oldest binding — the right tip of the input
    /// pattern — is `root`.
    pub(super) fn from_root(root: BasePattern) -> Self {
        let mut bindings = Self {
            bindings: vec![root.clone()],
            identifiers: HashMap::new(),
            binding_starts: vec![0],
        };
        for identifier in root.identifiers() {
            bindings
                .identifiers
                .entry(identifier.clone())
                .or_default()
                .push(0);
        }
        bindings
    }

    /// The live bindings, oldest first. A binding's index in the slice is
    /// its position in the input pattern: 0 is the right tip, `len() - 1`
    /// the newest, leftmost binding.
    pub(super) fn as_slice(&self) -> &[BasePattern] {
        &self.bindings
    }

    /// The index of the binding in effect for `identifier`, or `None` if no
    /// live binding binds that name.
    pub(super) fn position_of(&self, identifier: &Identifier) -> Option<usize> {
        self.identifiers
            .get(identifier)
            .and_then(|indices| indices.last().copied())
    }

    /// Open a new, empty scope.
    pub(super) fn push_scope(&mut self) {
        self.binding_starts.push(self.bindings.len());
    }

    /// Close the current scope: its bindings die and the identifiers they
    /// shadowed come back into effect.
    ///
    /// ## Panics
    ///
    /// The stack is empty.
    pub(super) fn pop_scope(&mut self) {
        let start = self.binding_starts.pop().expect("Empty stack");
        while self.bindings.len() > start {
            let index = self.bindings.len() - 1;
            for identifier in self.bindings[index].identifiers() {
                match self.identifiers.get_mut(identifier) {
                    Some(indices) => {
                        debug_assert_eq!(indices.last(), Some(&index));
                        indices.pop();
                        if indices.is_empty() {
                            self.identifiers.remove(identifier);
                        }
                    }
                    None => unreachable!("every binding registers its identifiers"),
                }
            }
            self.bindings.pop();
        }
    }

    /// Append `binding` to the current scope and register its identifiers.
    ///
    /// Update the input pattern accordingly:
    ///
    /// ```text
    ///   .
    ///  / \
    /// p   previous
    /// ```
    pub(super) fn insert(&mut self, binding: BasePattern) {
        let index = self.bindings.len();
        for identifier in binding.identifiers() {
            self.identifiers
                .entry(identifier.clone())
                .or_default()
                .push(index);
        }
        self.bindings.push(binding);
    }
}
