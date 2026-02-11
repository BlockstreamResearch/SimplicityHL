use super::*;
use std::fs::{self, File};
use std::io::Write;
use std::path::Path;
use tempfile::TempDir;

fn create_simf_file(dir: &Path, rel_path: &str, content: &str) -> PathBuf {
    let full_path = dir.join(rel_path);

    // Ensure parent directories exist
    if let Some(parent) = full_path.parent() {
        fs::create_dir_all(parent).unwrap();
    }

    let mut file = File::create(&full_path).expect("Failed to create file");
    file.write_all(content.as_bytes())
        .expect("Failed to write content");
    full_path
}

// Helper to mock the initial root program parsing
fn parse_root(path: &Path) -> parse::Program {
    parse_and_get_program(path).expect("Root parsing failed")
}

/// Initializes a graph environment for testing.
/// Returns:
/// 1. The constructed `ProjectGraph`.
/// 2. A `HashMap` mapping filenames (e.g., "A.simf") to their `FileID` (usize).
/// 3. The `TempDir` (to keep files alive during the test).
fn setup_graph(files: Vec<(&str, &str)>) -> (ProjectGraph, HashMap<String, usize>, TempDir) {
    let temp_dir = TempDir::new().unwrap();
    let mut lib_map = HashMap::new();

    // Define the standard library path structure
    let lib_path = temp_dir.path().join("libs/lib");
    lib_map.insert("lib".to_string(), lib_path);

    let mut root_path = None;

    // Create all requested files
    for (name, content) in files {
        if name == "main.simf" {
            root_path = Some(create_simf_file(temp_dir.path(), name, content));
        } else {
            // Names should be passed like "libs/lib/A.simf"
            create_simf_file(temp_dir.path(), name, content);
        }
    }

    let root_p = root_path.expect("main.simf must be defined in file list");
    let root_program = parse_root(&root_p);

    let config = LibConfig::new(lib_map, &root_p);
    let graph = ProjectGraph::new(&config, &root_program).unwrap();

    // Create a lookup map for tests: "A.simf" -> FileID
    let mut file_ids = HashMap::new();
    for (path, id) in &graph.lookup {
        let file_name = path.file_name().unwrap().to_string_lossy().to_string();
        file_ids.insert(file_name, *id);
    }

    (graph, file_ids, temp_dir)
}

#[cfg(test)]
mod graph_construction_and_dependency_resolution {
    use super::*;

    // Creates a file with specific content in the temp directory
    #[test]
    fn test_simple_import() {
        // Setup:
        // root.simf -> "use std::math;"
        // libs/std/math.simf -> ""

        let (graph, ids, _dir) = setup_graph(vec![
            ("main.simf", "use lib::math::some_func;"),
            ("libs/lib/math.simf", ""),
        ]);

        assert_eq!(graph.modules.len(), 2, "Should have Root and Math module");

        let root_id = ids["main"];
        let math_id = ids["math"];

        assert!(
            graph.dependencies[&root_id].contains(&math_id),
            "Root (main.simf) should depend on Math (main.simf)"
        );
    }

    #[test]
    fn test_diamond_dependency_deduplication() {
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

        // Check strict deduplication (Unique modules count)
        assert_eq!(
            graph.modules.len(),
            4,
            "Should resolve exactly 4 unique modules"
        );

        // Verify Graph Topology via IDs
        let a_id = ids["A"];
        let b_id = ids["B"];
        let common_id = ids["Common"];

        // Check A -> Common
        assert!(
            graph.dependencies[&a_id].contains(&common_id),
            "A should depend on Common"
        );

        // Check B -> Common (Crucial: Must be the SAME common_id)
        assert!(
            graph.dependencies[&b_id].contains(&common_id),
            "B should depend on Common"
        );
    }

    #[test]
    fn test_cyclic_dependency() {
        // Setup: A <-> B cycle
        // main -> imports A
        // A -> imports B
        // B -> imports A

        let (graph, ids, _dir) = setup_graph(vec![
            ("main.simf", "use lib::A::entry;"),
            ("libs/lib/A.simf", "use lib::B::func;"),
            ("libs/lib/B.simf", "use lib::A::func;"),
        ]);

        let a_id = ids["A"];
        let b_id = ids["B"];

        // Check if graph correctly recorded the cycle
        assert!(
            graph.dependencies[&a_id].contains(&b_id),
            "A should depend on B"
        );
        assert!(
            graph.dependencies[&b_id].contains(&a_id),
            "B should depend on A"
        );
    }

    #[test]
    fn test_ignores_unmapped_imports() {
        // Setup: root imports from "unknown", which is not in our lib_map
        let (graph, ids, _dir) = setup_graph(vec![("main.simf", "use unknown::library;")]);

        assert_eq!(graph.modules.len(), 1, "Should only contain root");
        assert!(graph.dependencies[&ids["main"]].is_empty());
    }
}

#[cfg(test)]
mod c3_linearization {
    use super::*;

    #[test]
    fn test_c3_simple_import() {
        // Setup similar to above
        let (graph, ids, _dir) = setup_graph(vec![
            ("main.simf", "use lib::math::some_func;"),
            ("libs/lib/math.simf", ""),
        ]);

        let order = graph.c3_linearize().expect("C3 failed");

        let root_id = ids["main"];
        let math_id = ids["math"];

        // Assuming linearization order: Dependent (Root) -> Dependency (Math)
        assert_eq!(order, vec![root_id, math_id]);
    }

    #[test]
    fn test_c3_diamond_dependency_deduplication() {
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

        let order = graph.c3_linearize().expect("C3 failed");

        // Verify order using IDs from the helper map
        let main_id = ids["main"];
        let a_id = ids["A"];
        let b_id = ids["B"];
        let common_id = ids["Common"];

        // In the `resolve_complication_order` function, the order was reversed.
        // Therefore, `common` will be the first, and `main` will be last.
        assert_eq!(order, vec![main_id, a_id, b_id, common_id]);
    }

    #[test]
    fn test_c3_detects_cycle() {
        let (graph, _, _dir) = setup_graph(vec![
            ("main.simf", "use lib::A::entry;"),
            ("libs/lib/A.simf", "use lib::B::func;"),
            ("libs/lib/B.simf", "use lib::A::func;"),
        ]);

        let order = graph.c3_linearize();
        matches!(order, Err(C3Error::CycleDetected(_)));
    }
}

#[cfg(test)]
mod error_diganostic_and_terminal_formatting {
    use super::*;

    #[test]
    fn test_missing_file_error() {
        // Setup:
        // root -> imports missing_lib

        let temp_dir = TempDir::new().unwrap();
        let root_path = create_simf_file(temp_dir.path(), "root.simf", "use std::ghost;");
        // We do NOT create ghost.simf

        let mut lib_map = HashMap::new();
        lib_map.insert("std".to_string(), temp_dir.path().join("libs/std"));

        let root_program = parse_root(&root_path);
        let config = LibConfig::new(lib_map, &root_path);
        let result = ProjectGraph::new(&config, &root_program);

        assert!(result.is_err(), "Should fail for missing file");
        let err_msg = result.err().unwrap();
        assert!(
            err_msg.contains("does not exist"),
            "Error message should mention missing file"
        );
    }
}
