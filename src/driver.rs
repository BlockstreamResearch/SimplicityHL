use std::collections::{HashMap, VecDeque};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::error::ErrorCollector;
use crate::parse::{self, ParseFromStrWithErrors};
use crate::LibConfig;

/// Represents a single, isolated file in the SimplicityHL project.
/// In this architecture, a file and a module are the exact same thing.
#[derive(Debug, Clone)]
pub struct Module {
    /// The completely parsed program for this specific file.
    /// it contains all the functions, aliases, and imports defined inside the file.
    pub parsed_program: parse::Program,
}

/// The Dependency Graph itself.
pub struct ProjectGraph {
    /// Arena Pattern: the data itself lives here.
    /// A flat vector guarantees that module data is stored contiguously in memory.
    pub modules: Vec<Module>,

    /// Fast lookup: File Path -> Module ID.
    /// A reverse index mapping absolute file paths to their internal IDs.
    /// This solves the duplication problem, ensuring each file is only parsed once.
    pub lookup: HashMap<PathBuf, usize>,

    /// The Adjacency List: Defines the Directed acyclic Graph (DAG) of imports.
    ///
    /// The Key (`usize`) is the ID of a "Parent" module (the file doing the importing).
    /// The Value (`Vec<usize>`) is a list of IDs of the "Child" modules it relies on.
    ///
    /// Example: If `main.simf` (ID: 0) has `use lib::math;` (ID: 1) and `use lib::io;` (ID: 2),
    /// this map will contain: `{ 0: [1, 2] }`.
    pub dependencies: HashMap<usize, Vec<usize>>,
}

fn parse_and_get_program(prog_file: &Path) -> Result<parse::Program, String> {
    let prog_text = std::fs::read_to_string(prog_file).map_err(|e| e.to_string())?;
    let file = prog_text.into();
    let mut error_handler = crate::error::ErrorCollector::new(Arc::clone(&file));

    if let Some(program) = parse::Program::parse_from_str_with_errors(&file, &mut error_handler) {
        Ok(program)
    } else {
        Err(ErrorCollector::to_string(&error_handler))?
    }
}

impl ProjectGraph {
    pub fn new(lib_cfg: &LibConfig, root_program: &parse::Program) -> Result<Self, String> {
        let mut modules: Vec<Module> = vec![Module {
            parsed_program: root_program.clone(),
        }];
        let mut lookup: HashMap<PathBuf, usize> = HashMap::new();
        let mut dependencies: HashMap<usize, Vec<usize>> = HashMap::new();

        let root_id = 0;
        lookup.insert(lib_cfg.root_path.clone(), root_id);
        dependencies.insert(root_id, Vec::new());

        // Implementation of the standard BFS algorithm with memoization and queue
        let mut queue = VecDeque::new();
        queue.push_back(root_id);

        while let Some(curr_id) = queue.pop_front() {
            let mut pending_imports: Vec<PathBuf> = Vec::new();
            let current_program = &modules[curr_id].parsed_program;

            for elem in current_program.items() {
                if let parse::Item::Use(use_decl) = elem {
                    if let Ok(path) = lib_cfg.get_full_path(use_decl) {
                        pending_imports.push(path);
                    }
                }
            }

            for path in pending_imports {
                let full_path = path.with_extension("simf");

                if !full_path.is_file() {
                    return Err(format!("File in {:?}, does not exist", full_path));
                }

                if let Some(&existing_id) = lookup.get(&path) {
                    dependencies.entry(curr_id).or_default().push(existing_id);
                    continue;
                }

                let last_ind = modules.len();
                let program = parse_and_get_program(&full_path)?;

                modules.push(Module {
                    parsed_program: program,
                });
                lookup.insert(path.clone(), last_ind);
                dependencies.entry(curr_id).or_default().push(last_ind);

                queue.push_back(last_ind);
            }
        }

        Ok(Self {
            modules,
            lookup,
            dependencies,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::{self, File};
    use std::io::Write;
    use std::path::Path;
    use tempfile::TempDir;

    // --- Helper to setup environment ---
    // Creates a file with specific content in the temp directory
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

    #[test]
    fn test_simple_import() {
        // Setup:
        // root.simf -> "use std::math;"
        // libs/std/math.simf -> ""

        let temp_dir = TempDir::new().unwrap();
        let root_path = create_simf_file(temp_dir.path(), "root.simf", "use std::math::some_func;");
        create_simf_file(temp_dir.path(), "libs/std/math.simf", "");

        // Setup Library Map
        let mut lib_map = HashMap::new();
        lib_map.insert("std".to_string(), temp_dir.path().join("libs/std"));

        // Parse Root
        let root_program = parse_root(&root_path);
        let config = LibConfig::new(lib_map, &root_path);

        // Run Logic
        let graph = ProjectGraph::new(&config, &root_program).expect("Graph build failed");

        // Assertions
        assert_eq!(graph.modules.len(), 2, "Should have Root and Math module");
        assert!(
            graph.dependencies[&0].contains(&1),
            "Root should depend on Math"
        );
    }

    #[test]
    fn test_diamond_dependency_deduplication() {
        // Setup:
        // root -> imports A, B
        // A -> imports Common
        // B -> imports Common
        // Expected: Common loaded ONLY ONCE.

        let temp_dir = TempDir::new().unwrap();
        let root_path = create_simf_file(
            temp_dir.path(),
            "root.simf",
            "use lib::A::foo; use lib::B::bar;",
        );
        create_simf_file(
            temp_dir.path(),
            "libs/lib/A.simf",
            "use lib::Common::dummy1;",
        );
        create_simf_file(
            temp_dir.path(),
            "libs/lib/B.simf",
            "use lib::Common::dummy2;",
        );
        create_simf_file(temp_dir.path(), "libs/lib/Common.simf", ""); // Empty leaf

        let mut lib_map = HashMap::new();
        lib_map.insert("lib".to_string(), temp_dir.path().join("libs/lib"));

        let root_program = parse_root(&root_path);
        let config = LibConfig::new(lib_map, &root_path);
        let graph = ProjectGraph::new(&config, &root_program).expect("Graph build failed");

        // Assertions
        // Structure: Root(0), A(1), B(2), Common(3)
        assert_eq!(
            graph.modules.len(),
            4,
            "Should resolve exactly 4 unique modules"
        );

        // Check A -> Common
        let a_id = 1;
        let common_id = 3;
        assert!(graph.dependencies[&a_id].contains(&common_id));

        // Check B -> Common (Should point to SAME ID)
        let b_id = 2;
        assert!(graph.dependencies[&b_id].contains(&common_id));
    }

    #[test]
    fn test_cyclic_dependency() {
        // Setup:
        // A -> imports B
        // B -> imports A
        // Expected: Should finish without infinite loop

        let temp_dir = TempDir::new().unwrap();
        let a_path = create_simf_file(
            temp_dir.path(),
            "libs/test/A.simf",
            "use test::B::some_test;",
        );
        create_simf_file(
            temp_dir.path(),
            "libs/test/B.simf",
            "use test::A::another_test;",
        );

        let mut lib_map = HashMap::new();
        lib_map.insert("test".to_string(), temp_dir.path().join("libs/test"));

        let root_program = parse_root(&a_path);
        let config = LibConfig::new(lib_map, &a_path);
        let graph = ProjectGraph::new(&config, &root_program).expect("Graph build failed");

        println!("Graph dependencies: {:?}", graph.dependencies);
        println!("lookup: {:?}", graph.lookup);
        assert_eq!(graph.modules.len(), 2, "Should only have A and B");

        // A depends on B
        assert!(graph.dependencies[&0].contains(&1));
        // B depends on A (Circular)
        assert!(graph.dependencies[&1].contains(&0));
    }

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

    #[test]
    fn test_ignores_unmapped_imports() {
        // Setup:
        // root -> "use unknown::library;"
        // "unknown" is NOT in library_map.
        // Expected: It should simply skip this import (based on `if let Ok(path)` logic)

        let temp_dir = TempDir::new().unwrap();
        let root_path = create_simf_file(temp_dir.path(), "root.simf", "use unknown::library;");

        let lib_map = HashMap::new();

        let root_program = parse_root(&root_path);
        let config = LibConfig::new(lib_map, &root_path);
        let graph =
            ProjectGraph::new(&config, &root_program).expect("Should succeed but ignore import");

        assert_eq!(graph.modules.len(), 1, "Should only contain root");
        assert!(
            graph.dependencies[&0].is_empty(),
            "Root should have no resolved dependencies"
        );
    }
}
