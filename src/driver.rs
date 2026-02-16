use std::collections::{HashMap, VecDeque};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::error::{ErrorCollector, Span};
use crate::parse::{self, ParseFromStrWithErrors, Visibility};
use crate::str::Identifier;
use crate::LibConfig;

/// Graph Node: One file = One module
#[derive(Debug, Clone)]
struct Module {
    /// Parsed AST (your `parse::Program`)
    /// Using Option to first create the node, then add the AST
    pub parsed_program: parse::Program,
}

/// The Dependency Graph itself
pub struct ProjectGraph {
    /// Arena Pattern: the data itself lies here. Vector guarantees data lives in one place.
    pub(self) modules: Vec<Module>,

    /// Fast lookup: Path -> ID
    /// Solves the duplicate problem (so as not to parse a.simf twice)
    pub config: Arc<LibConfig>,
    pub lookup: HashMap<PathBuf, usize>,
    pub paths: Vec<PathBuf>,

    /// Adjacency list: Who depends on whom
    pub dependencies: HashMap<usize, Vec<usize>>,
}

#[derive(Clone, Debug)]
pub struct Resolution {
    pub visibility: Visibility,
}

pub struct Program {
    //pub graph: ProjectGraph,
    pub items: Arc<[parse::Item]>,
    pub scope_items: Vec<HashMap<Identifier, Resolution>>,
    pub span: Span,
}

#[derive(Debug)]
pub enum C3Error {
    CycleDetected(Vec<usize>),
    InconsistentLinearization { module: usize },
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
    pub fn new(config: Arc<LibConfig>, root_program: &parse::Program) -> Result<Self, String> {
        let mut modules: Vec<Module> = vec![Module {
            parsed_program: root_program.clone(),
        }];
        let mut lookup: HashMap<PathBuf, usize> = HashMap::new();
        let mut paths: Vec<PathBuf> = vec![config.root_path.clone()];
        let mut dependencies: HashMap<usize, Vec<usize>> = HashMap::new();

        let root_id = 0;
        lookup.insert(config.root_path.clone(), root_id);
        dependencies.insert(root_id, Vec::new());

        // Implementation of the standard BFS algorithm with memoization and queue
        let mut queue = VecDeque::new();
        queue.push_back(root_id);

        while let Some(curr_id) = queue.pop_front() {
            let mut pending_imports: Vec<PathBuf> = Vec::new();
            let current_program = &modules[curr_id].parsed_program;

            for elem in current_program.items() {
                if let parse::Item::Use(use_decl) = elem {
                    if let Ok(path) = config.get_full_path(use_decl) {
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
                paths.push(path.clone());
                dependencies.entry(curr_id).or_default().push(last_ind);

                queue.push_back(last_ind);
            }
        }

        Ok(Self {
            modules,
            config,
            lookup,
            paths,
            dependencies,
        })
    }

    pub fn c3_linearize(&self) -> Result<Vec<usize>, C3Error> {
        self.linearize_module(0)
    }

    fn linearize_module(&self, root: usize) -> Result<Vec<usize>, C3Error> {
        let mut memo = HashMap::<usize, Vec<usize>>::new();
        let mut visiting = Vec::<usize>::new();

        self.linearize_rec(root, &mut memo, &mut visiting)
    }

    fn linearize_rec(
        &self,
        module: usize,
        memo: &mut HashMap<usize, Vec<usize>>,
        visiting: &mut Vec<usize>,
    ) -> Result<Vec<usize>, C3Error> {
        if let Some(result) = memo.get(&module) {
            return Ok(result.clone());
        }

        if visiting.contains(&module) {
            let cycle_start = visiting.iter().position(|m| *m == module).unwrap();
            return Err(C3Error::CycleDetected(visiting[cycle_start..].to_vec()));
        }

        visiting.push(module);

        let parents = self.dependencies.get(&module).cloned().unwrap_or_default();

        let mut seqs: Vec<Vec<usize>> = Vec::new();

        for parent in &parents {
            let lin = self.linearize_rec(*parent, memo, visiting)?;
            seqs.push(lin);
        }

        seqs.push(parents.clone());

        let mut result = vec![module];
        let merged = merge(seqs).ok_or(C3Error::InconsistentLinearization { module })?;

        result.extend(merged);

        visiting.pop();
        memo.insert(module, result.clone());

        Ok(result)
    }

    // TODO: @Sdoba16 to implement
    // fn build_ordering(&self) {}

    fn process_use_item(
        scope_items: &mut [HashMap<Identifier, Resolution>],
        file_id: usize,
        ind: usize,
        elem: &Identifier,
        use_decl_visibility: Visibility,
    ) -> Result<(), String> {
        if matches!(
            scope_items[ind][elem].visibility,
            parse::Visibility::Private
        ) {
            return Err(format!(
                "Function {} is private and cannot be used.",
                elem.as_inner()
            ));
        }

        scope_items[file_id].insert(
            elem.clone(),
            Resolution {
                visibility: use_decl_visibility,
            },
        );

        Ok(())
    }

    fn register_def(
        items: &mut Vec<parse::Item>,
        scope: &mut HashMap<Identifier, Resolution>,
        item: &parse::Item,
        name: Identifier,
        vis: &parse::Visibility,
    ) {
        items.push(item.clone());
        scope.insert(
            name,
            Resolution {
                visibility: vis.clone(),
            },
        );
    }

    // TODO: Change. Consider processing more than one errro at a time
    fn build_program(&self, order: &Vec<usize>) -> Result<Program, String> {
        let mut items: Vec<parse::Item> = Vec::new();
        let mut scope_items: Vec<HashMap<Identifier, Resolution>> =
            vec![HashMap::new(); order.len()];

        for &file_id in order {
            let program_items = self.modules[file_id].parsed_program.items();

            for elem in program_items {
                match elem {
                    parse::Item::Use(use_decl) => {
                        let full_path = self.config.get_full_path(use_decl)?;
                        let ind = self.lookup[&full_path];
                        let visibility = use_decl.visibility();

                        let use_targets = match use_decl.items() {
                            parse::UseItems::Single(elem) => std::slice::from_ref(elem),
                            parse::UseItems::List(elems) => elems.as_slice(),
                        };

                        for target in use_targets {
                            ProjectGraph::process_use_item(
                                &mut scope_items,
                                file_id,
                                ind,
                                target,
                                visibility.clone(),
                            )?;
                        }
                    }
                    parse::Item::TypeAlias(alias) => {
                        Self::register_def(
                            &mut items,
                            &mut scope_items[file_id],
                            elem,
                            alias.name().clone().into(),
                            alias.visibility(),
                        );
                    }
                    parse::Item::Function(function) => {
                        Self::register_def(
                            &mut items,
                            &mut scope_items[file_id],
                            elem,
                            function.name().clone().into(),
                            function.visibility(),
                        );
                    }
                    parse::Item::Module => {}
                }
            }
        }

        Ok(Program {
            items: items.into(),
            scope_items,
            span: *self.modules[0].parsed_program.as_ref(),
        })
    }

    pub fn resolve_complication_order(&self) -> Result<Program, String> {
        // TODO: Resolve errors more appropriately
        let mut order = self.c3_linearize().unwrap();
        order.reverse();
        // self.build_ordering();
        self.build_program(&order)
    }
}

fn merge(mut seqs: Vec<Vec<usize>>) -> Option<Vec<usize>> {
    let mut result = Vec::new();

    loop {
        seqs.retain(|s| !s.is_empty());
        if seqs.is_empty() {
            return Some(result);
        }

        let mut candidate = None;

        'outer: for seq in &seqs {
            let head = seq[0];

            if seqs.iter().all(|s| !s[1..].contains(&head)) {
                candidate = Some(head);
                break 'outer;
            }
        }

        let head = candidate?;

        result.push(head);

        for seq in &mut seqs {
            if seq.first() == Some(&head) {
                seq.remove(0);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::{self, File};
    use std::io::Write;
    use std::path::Path;
    use tempfile::TempDir;

    // ProjectGraph::new tests
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
    // (Assuming your parser works via a helper function)
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

        let config = Arc::from(LibConfig::new(lib_map, &root_p));
        let graph = ProjectGraph::new(config, &root_program).expect("Failed to build graph");

        // Create a lookup map for tests: "A.simf" -> FileID
        let mut file_ids = HashMap::new();
        for (path, id) in &graph.lookup {
            let file_name = path.file_name().unwrap().to_string_lossy().to_string();
            file_ids.insert(file_name, *id);
        }

        (graph, file_ids, temp_dir)
    }

    #[test]
    fn test_local_definitions_visibility() {
        // Scenario:
        // main.simf defines a private function and a public function.
        // Expected: Both should appear in the scope with correct visibility.

        let (graph, ids, _dir) = setup_graph(vec![(
            "main.simf",
            "fn private_fn() {} pub fn public_fn() {}",
        )]);

        let root_id = *ids.get("main").unwrap();
        let order = vec![root_id]; // Only one file

        let program = graph
            .build_program(&order)
            .expect("Failed to build program");
        let scope = &program.scope_items[root_id];

        // Check private function
        let private_res = scope
            .get(&Identifier::from("private_fn"))
            .expect("private_fn missing");
        assert_eq!(private_res.visibility, Visibility::Private);

        // Check public function
        let public_res = scope
            .get(&Identifier::from("public_fn"))
            .expect("public_fn missing");
        assert_eq!(public_res.visibility, Visibility::Public);
    }

    #[test]
    fn test_pub_use_propagation() {
        // Scenario: Re-exporting.
        // 1. A.simf defines `pub fn foo`.
        // 2. B.simf imports it and re-exports it via `pub use`.
        // 3. main.simf imports it from B.
        // Expected: B's scope must contain `foo` marked as Public.

        let (graph, ids, _dir) = setup_graph(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("libs/lib/B.simf", "pub use lib::A::foo;"),
            ("main.simf", "use lib::B::foo;"),
        ]);

        let id_a = *ids.get("A").unwrap();
        let id_b = *ids.get("B").unwrap();
        let id_root = *ids.get("main").unwrap();

        // Manual topological order: A -> B -> Root
        let order = vec![id_a, id_b, id_root];

        let program = graph
            .build_program(&order)
            .expect("Failed to build program");

        // Check B's scope
        let scope_b = &program.scope_items[id_b];
        let foo_in_b = scope_b
            .get(&Identifier::from("foo"))
            .expect("foo missing in B");

        // This is the critical check: Did `pub use` make it Public in B?
        assert_eq!(
            foo_in_b.visibility,
            Visibility::Public,
            "B should re-export foo as Public"
        );

        // Check Root's scope
        let scope_root = &program.scope_items[id_root];
        let foo_in_root = scope_root
            .get(&Identifier::from("foo"))
            .expect("foo missing in Root");

        // Root imported it via `use` (not pub use), so it should be Private in Root
        assert_eq!(
            foo_in_root.visibility,
            Visibility::Private,
            "Root should have foo as Private"
        );
    }

    #[test]
    fn test_private_import_encapsulation_error() {
        // Scenario: Access violation.
        // 1. A.simf defines `pub fn foo`.
        // 2. B.simf imports it via `use` (Private import).
        // 3. main.simf tries to import `foo` from B.
        // Expected: Error, because B did not re-export foo.

        let (graph, ids, _dir) = setup_graph(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("libs/lib/B.simf", "use lib::A::foo;"), // <--- Private binding!
            ("main.simf", "use lib::B::foo;"),       // <--- Should fail
        ]);

        let id_a = *ids.get("A").unwrap();
        let id_b = *ids.get("B").unwrap();
        let id_root = *ids.get("main").unwrap();

        // Order: A -> B -> Root
        let order = vec![id_a, id_b, id_root];

        let result = graph.build_program(&order);

        assert!(
            result.is_err(),
            "Build should fail when importing a private binding"
        );

        // Optional: Verify the error message contains relevant info
        // let err = result.err().unwrap();
        // assert!(err.to_string().to_lowercase().contains("private"));
    }

    /*
    #[test]
    fn test_renaming_with_use() {
        // Scenario: Renaming imports.
        // main.simf: use lib::A::foo as bar;
        // Expected: Scope should contain "bar", but not "foo".

        let (graph, ids, _dir) = setup_graph(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("main.simf",       "use lib::A::foo;"),
        ]);

        let id_a = *ids.get("A.simf").unwrap();
        let id_root = *ids.get("main.simf").unwrap();
        let order = vec![id_a, id_root];

        let program = graph.build_program(&order).expect("Failed to build program");
        let scope = &program.scope_items[id_root];

        assert!(scope.get(&Identifier::from("foo")).is_none(), "Original name 'foo' should not be in scope");
        assert!(scope.get(&Identifier::from("bar")).is_some(), "Alias 'bar' should be in scope");
    }
    */

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
        let config = Arc::from(LibConfig::new(lib_map, &root_path));

        // Run Logic
        let graph = ProjectGraph::new(config, &root_program).expect("Graph build failed");

        // Assertions
        assert_eq!(graph.modules.len(), 2, "Should have Root and Math module");
        assert!(
            graph.dependencies[&0].contains(&1),
            "Root should depend on Math"
        );
    }

    #[test]
    fn test_c3_simple_import() {
        let temp_dir = TempDir::new().unwrap();
        let root_path = create_simf_file(temp_dir.path(), "root.simf", "use std::math::some_func;");
        create_simf_file(temp_dir.path(), "libs/std/math.simf", "");

        let mut lib_map = HashMap::new();
        lib_map.insert("std".to_string(), temp_dir.path().join("libs/std"));

        let root_program = parse_root(&root_path);
        let config = Arc::from(LibConfig::new(lib_map, &root_path));
        let graph = ProjectGraph::new(config, &root_program).expect("Graph build failed");

        let order = graph.c3_linearize().expect("C3 failed");

        assert_eq!(order, vec![0, 1]);
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
        let config = Arc::from(LibConfig::new(lib_map, &root_path));
        let graph = ProjectGraph::new(config, &root_program).expect("Graph build failed");

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
    fn test_c3_diamond_dependency_deduplication() {
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
        let config = Arc::from(LibConfig::new(lib_map, &root_path));
        let graph = ProjectGraph::new(config, &root_program).expect("Graph build failed");

        let order = graph.c3_linearize().expect("C3 failed");

        assert_eq!(order, vec![0, 1, 2, 3],);
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
        let config = Arc::from(LibConfig::new(lib_map, &a_path));
        let graph = ProjectGraph::new(config, &root_program).expect("Graph build failed");

        assert_eq!(graph.modules.len(), 2, "Should only have A and B");

        // A depends on B
        assert!(graph.dependencies[&0].contains(&1));
        // B depends on A (Circular)
        assert!(graph.dependencies[&1].contains(&0));
    }

    #[test]
    fn test_c3_cyclic_dependency() {
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
        let config = Arc::from(LibConfig::new(lib_map, &a_path));
        let graph = ProjectGraph::new(config, &root_program).expect("Graph build failed");

        let order = graph.c3_linearize().unwrap_err();
        matches!(order, C3Error::CycleDetected(_));
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
        let config = Arc::from(LibConfig::new(lib_map, &root_path));
        let result = ProjectGraph::new(config, &root_program);

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

        let lib_map = HashMap::new(); // Empty map

        let root_program = parse_root(&root_path);
        let config = Arc::from(LibConfig::new(lib_map, &root_path));
        let graph =
            ProjectGraph::new(config, &root_program).expect("Should succeed but ignore import");

        assert_eq!(graph.modules.len(), 1, "Should only contain root");
        assert!(
            graph.dependencies[&0].is_empty(),
            "Root should have no resolved dependencies"
        );
    }
}
