//! Computes the bottom-up load order of dependencies using a DFS.
//!
//! # Architectural Note: Why pure DFS instead of C3?
//! Unlike OOP languages that require C3 Linearization to resolve complex method
//! overriding (MRO), SimplicityHL module imports rely on namespacing and aliasing.
//! Because we do not need to enforce strict local precedence, a standard post-order
//! DFS is a better option.

use std::collections::HashSet;
use std::fmt;

use crate::driver::DependencyGraph;

/// This is a core component of the [`DependencyGraph`].
impl DependencyGraph {
    /// Returns the deterministic, BOTTOM-UP load order of dependencies.
    pub(super) fn linearize(&self) -> Result<Vec<usize>, LinearizationError> {
        let mut visited = HashSet::new();
        let mut visiting = Vec::new();
        let mut order = Vec::new();

        self.dfs_linearize(0, &mut visited, &mut visiting, &mut order)?;

        Ok(order)
    }

    /// Core recursive Post-Order DFS for topological sorting.
    ///
    /// - **Visited Set (`visited`):** Prevents processing shared dependencies multiple times (solves diamonds).
    /// - **Cycle Detection (`visiting`):** Tracks the current path stack to catch infinite loops.
    /// - **Order List (`order`):** Accumulates the deterministic load order bottom-up.
    fn dfs_linearize(
        &self,
        module: usize,
        visited: &mut HashSet<usize>,
        visiting: &mut Vec<usize>,
        order: &mut Vec<usize>,
    ) -> Result<(), LinearizationError> {
        // If we have already fully processed this module, skip it (Diamond Deduplication)
        if visited.contains(&module) {
            return Ok(());
        }

        if let Some(cycle_start) = visiting.iter().position(|&m| m == module) {
            return Err(LinearizationError::CycleDetected(
                visiting[cycle_start..]
                    .iter()
                    .map(|&id| self.modules[id].source.str_name())
                    .collect(),
            ));
        }

        visiting.push(module);

        let parents = self
            .dependencies
            .get(&module)
            .map_or(&[] as &[usize], |v| v.as_slice());

        for &parent in parents {
            self.dfs_linearize(parent, visited, visiting, order)?;
        }

        visiting.pop();
        visited.insert(module);
        order.push(module);

        Ok(())
    }
}

#[derive(Debug)]
pub enum LinearizationError {
    /// Raised when a circular dependency (e.g., A -> B -> A) is detected.
    CycleDetected(Vec<String>),
}

impl fmt::Display for LinearizationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LinearizationError::CycleDetected(cycle) => {
                write!(f, "Circular dependency detected: {:?}", cycle.join(" -> "))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::driver::tests::setup_graph;

    use super::*;

    #[test]
    fn test_linearize_simple_import() {
        let (graph, ids, _dir) = setup_graph(vec![
            ("main.simf", "use lib::math::some_func;"),
            ("libs/lib/math.simf", ""),
        ]);

        let order = graph.linearize().unwrap();

        let root_id = ids["main"];
        let math_id = ids["math"];

        assert_eq!(order, vec![math_id, root_id]);
    }

    #[test]
    fn test_linearize_diamond_dependency_deduplication() {
        // Setup:
        // root -> imports A, B
        // A -> imports Common
        // B -> imports Common
        // Expected: Common loaded ONLY ONCE.

        let (graph, ids, _dir) = setup_graph(vec![
            ("main.simf", "use lib::A::foo; use lib::B::bar;"),
            ("libs/lib/A.simf", "use lib::Common::dummy1;"),
            ("libs/lib/B.simf", "use lib::Common::dummy2;"),
            ("libs/lib/Common.simf", ""),
        ]);

        let order = graph.linearize().unwrap();

        // Verify order using IDs from the helper map
        let main_id = ids["main"];
        let a_id = ids["A"];
        let b_id = ids["B"];
        let common_id = ids["Common"];

        assert!(
            order == vec![common_id, b_id, a_id, main_id]
                || order == vec![common_id, a_id, b_id, main_id]
        );
    }

    #[test]
    fn test_linearize_detects_cycle() {
        let (graph, _, _dir) = setup_graph(vec![
            ("main.simf", "use lib::A::entry;"),
            ("libs/lib/A.simf", "use lib::B::func;"),
            ("libs/lib/B.simf", "use lib::A::func;"),
        ]);

        let order = graph.linearize();
        assert!(matches!(
            order,
            Err(LinearizationError::CycleDetected { .. })
        ));
    }

    #[test]
    fn test_linearize_allows_conflicting_nested_import_order() {
        // A imports X then Y, while B imports Y then X.
        // This DAG is still valid because neither X nor Y depends on the other.
        let (graph, ids, _dir) = setup_graph(vec![
            ("main.simf", "use lib::A::foo; use lib::B::bar;"),
            ("libs/lib/A.simf", "use lib::X::foo; use lib::Y::bar;"),
            ("libs/lib/B.simf", "use lib::Y::baz; use lib::X::qux;"),
            ("libs/lib/X.simf", ""),
            ("libs/lib/Y.simf", ""),
        ]);

        let order = graph
            .linearize()
            .expect("valid dependency DAG should linearize successfully");

        let main_id = ids["main"];
        let a_id = ids["A"];
        let b_id = ids["B"];
        let x_id = ids["X"];
        let y_id = ids["Y"];

        assert!(
            order == vec![x_id, y_id, a_id, b_id, main_id]
                || order == vec![y_id, x_id, a_id, b_id, main_id]
                || order == vec![x_id, y_id, b_id, a_id, main_id]
                || order == vec![y_id, x_id, b_id, a_id, main_id]
        );
    }
}
