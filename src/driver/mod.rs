use std::collections::{HashMap, HashSet, VecDeque};
use std::path::PathBuf;
use std::sync::Arc;

use chumsky::container::Container;

use crate::error::{Error, ErrorCollector, RichError, Span};
use crate::parse::{self, ParseFromStrWithErrors};
use crate::resolution::{CanonPath, DependencyMap, SourceFile};

/// Represents a single, isolated file in the SimplicityHL project.
/// In this architecture, a file and a module are the exact same thing.
#[derive(Debug, Clone)]
struct Module {
    source: SourceFile,
    /// The completely parsed program for this specific file.
    /// it contains all the functions, aliases, and imports defined inside the file.
    parsed_program: parse::Program,
}

/// An Intermediate Representation that helps transform isolated files into a global program.
///
/// While an AST only understands a single file, the `DependencyGraph` links multiple
/// ASTs together into a Directed Acyclic Graph (DAG). This DAG is then used to build
/// one convenient `Program` struct for the semantic analyzer can easily process.
///
/// This structure provides the global context necessary to solve high-level compiler
/// problems, including:
/// * **Cross-Module Resolution:** Allowing the compiler to traverse edges and verify
///   that imported symbols, functions, and types actually exist in other files.
/// * **Topological Sorting:** Guaranteeing that modules are analyzed and compiled in
///   the strictly correct mathematical order (e.g., analyzing module `B` before module
///   `A` if `A` depends on `B`).
/// * **Cycle Detection:** Preventing infinite compiler loops by ensuring no circular
///   imports exist before heavy semantic processing begins.
pub struct DependencyGraph {
    /// Implements the Arena Pattern to act as the sole, centralized owner of all parsed modules.
    ///
    /// In C++ or Java, a graph would typically link dependencies using direct memory
    /// pointers (e.g., `List<Module*>`). In Rust, doing this requires either
    /// lifetimes or performance-heavy reference counting (`Rc<RefCell<T>>`).
    ///
    /// Using a flat `Vec` as a memory arena is the idiomatic Rust solution.
    modules: Vec<Module>,

    /// The configuration environment.
    /// Used to resolve external library dependencies and invoke their associated functions.
    dependency_map: Arc<DependencyMap>,

    /// Fast lookup: `CanonPath` -> Module ID.
    /// A reverse index mapping absolute file paths to their internal IDs.
    /// This solves the duplication problem, ensuring each file is only parsed once.
    lookup: HashMap<CanonPath, usize>,

    /// Fast lookup: Module ID -> `CanonPath`.
    /// A direct index mapping internal IDs back to their absolute file paths.
    /// This serves as the exact inverse of the `lookup` map.
    paths: Vec<CanonPath>,

    /// The Adjacency List: Defines the Directed acyclic Graph (DAG) of imports.
    ///
    /// The Key (`usize`) is the ID of a "Parent" module (the file doing the importing).
    /// The Value (`Vec<usize>`) is a list of IDs of the "Child" modules it relies on.
    ///
    /// Example: If `main.simf` (ID: 0) has `use lib::math;` (ID: 1) and `use lib::io;` (ID: 2),
    /// this map will contain: `{ 0: [1, 2] }`.
    dependencies: HashMap<usize, Vec<usize>>,
}

impl DependencyGraph {
    /// Initializes a new `ProjectGraph` by parsing the root program and discovering all dependencies.
    ///
    /// Performs a BFS to recursively parse `use` statements,
    /// building a DAG of the project's modules.
    ///
    /// # Arguments
    ///
    /// * `root_source` - The `SourceFile` representing the entry point of the project.
    /// * `dependency_map` - The context-aware mapping rules used to resolve external imports.
    /// * `root_program` - A reference to the already-parsed AST of the root file.
    /// * `handler` - The diagnostics collector used to record resolution and parsing errors.
    ///
    /// # Returns
    ///
    /// * `Ok(Some(Self))` - If the entire project graph was successfully resolved and parsed.
    /// * `Ok(None)` - If the graph traversal completed, but one or more modules contained
    ///   errors (which have been safely logged into the `handler`).
    ///
    /// # Errors
    ///
    /// This function will return an `Err(String)` only for critical internal compiler errors
    /// (e.g., if a provided `SourceFile` is unexpectedly missing its underlying file path).
    pub fn new(
        root_source: SourceFile,
        dependency_map: Arc<DependencyMap>,
        root_program: &parse::Program,
        handler: &mut ErrorCollector,
    ) -> Result<Option<Self>, String> {
        let root_name = if let Some(root_name) = root_source.name() {
            CanonPath::canonicalize(root_name)?
        } else {
            return Err(
                "The root_source variable inside the ProjectGraph::new() function has no name"
                    .to_string(),
            );
        };

        let mut graph = Self {
            modules: vec![Module {
                source: root_source,
                parsed_program: root_program.clone(),
            }],
            dependency_map,
            lookup: HashMap::new(),
            paths: vec![root_name.clone()],
            dependencies: HashMap::new(),
        };

        let root_id = 0;
        graph.lookup.insert(root_name, root_id);
        graph.dependencies.insert(root_id, Vec::new());

        let mut queue = VecDeque::new();
        queue.push_back(root_id);

        // Prevent errors in the checked files from being doubled in the `load_and_parse_dependencies` function.
        let mut inalid_imports = HashSet::new();

        while let Some(curr_id) = queue.pop_front() {
            let Some(current_module) = graph.modules.get(curr_id) else {
                return Err(format!(
                    "Internal Driver Error: Module ID {} is in the queue but missing from the graph.modules.",
                    curr_id
                ));
            };

            // We need this to report errors inside THIS file.
            let importer_source = current_module.source.clone();

            let importer_source_name = if let Some(name) = importer_source.name() {
                CanonPath::canonicalize(name)?
            } else {
                return Err(format!(
                    "The {:?} variable inside the DependencyGraph::new() function has no name",
                    importer_source
                ));
            };

            // PHASE 1: Immutably read from the graph
            let valid_imports = Self::resolve_imports(
                &current_module.parsed_program,
                &importer_source,
                importer_source_name,
                &graph.dependency_map,
                handler,
            );

            // PHASE 2: Mutate the graph
            graph.load_and_parse_dependencies(
                curr_id,
                valid_imports,
                &mut inalid_imports,
                &importer_source,
                handler,
                &mut queue,
            );
        }

        // TODO: Consider getting rid of the 'String' error here and changing it to a more appropriate error
        // (e.g. 'Result<Self, ErrorCollector>') after resolving https://github.com/BlockstreamResearch/SimplicityHL/issues/270.
        Ok((!handler.has_errors()).then_some(graph))
    }

    /// This helper cleanly encapsulates the process of loading source text, parsing it
    /// into an `parse::Program`, and combining them so the compiler can easily work with the file.
    /// If the file is missing or contains syntax errors, it logs the diagnostic to the
    /// `ErrorCollector` and safely returns `None`.
    fn parse_and_get_program(
        path: &CanonPath,
        importer_source: SourceFile,
        span: Span,
        handler: &mut ErrorCollector,
    ) -> Option<Module> {
        let Ok(content) = std::fs::read_to_string(path.as_path()) else {
            let err = RichError::new(Error::FileNotFound(PathBuf::from(path.as_path())), span)
                .with_source(importer_source.clone());

            handler.push(err);
            return None;
        };

        let mut error_handler = ErrorCollector::new();
        let dep_source_file = SourceFile::new(path.as_path(), Arc::from(content.clone()));

        let ast = parse::Program::parse_from_str_with_errors(&dep_source_file, &mut error_handler);

        if error_handler.has_errors() {
            handler.extend_with_handler(dep_source_file, &error_handler);
            None
        } else {
            ast.map(|parsed_program| Module {
                source: dep_source_file.clone(),
                parsed_program,
            })
        }
    }

    /// PHASE 1 OF GRAPH CONSTRUCTION: Resolves all imports inside a single `parse::Program`.
    /// Note: This is a specialized helper function designed exclusively for the `DependencyGraph::new()` constructor.
    fn resolve_imports(
        current_program: &parse::Program,
        importer_source: &SourceFile,
        importer_source_name: CanonPath,
        dependency_map: &DependencyMap,
        handler: &mut ErrorCollector,
    ) -> Vec<(CanonPath, Span)> {
        let mut valid_imports = Vec::new();

        for elem in current_program.items() {
            let parse::Item::Use(use_decl) = elem else {
                continue;
            };

            match dependency_map.resolve_path(importer_source_name.clone(), use_decl) {
                Ok(path) => valid_imports.push((path, *use_decl.span())),
                Err(err) => handler.push(err.with_source(importer_source.clone())),
            }
        }

        valid_imports
    }

    /// PHASE 2 OF GRAPH CONSTRUCTION: Loads, parses, and registers new dependencies.
    /// Note: This is a specialized helper function designed exclusively for the `DependencyGraph::new()` constructor.
    fn load_and_parse_dependencies(
        &mut self,
        curr_id: usize,
        valid_imports: Vec<(CanonPath, Span)>,
        inalid_imports: &mut HashSet<CanonPath>,
        importer_source: &SourceFile,
        handler: &mut ErrorCollector,
        queue: &mut VecDeque<usize>,
    ) {
        for (path, import_span) in valid_imports {
            if inalid_imports.contains(&path) {
                continue;
            }

            if let Some(&existing_id) = self.lookup.get(&path) {
                let deps = self.dependencies.entry(curr_id).or_default();
                if !deps.contains(&existing_id) {
                    deps.push(existing_id);
                }
                continue;
            }

            let Some(module) =
                Self::parse_and_get_program(&path, importer_source.clone(), import_span, handler)
            else {
                inalid_imports.push(path);
                continue;
            };

            let last_ind = self.modules.len();
            self.modules.push(module);

            self.lookup.insert(path.clone(), last_ind);
            self.paths.push(path.clone());
            self.dependencies.entry(curr_id).or_default().push(last_ind);

            queue.push_back(last_ind);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolution::tests::canon;
    use crate::test_utils::TempWorkspace;

    #[test]
    fn test_new_bfs_traversal_state() {
        // Goal: Verify that a simple chain (main -> a -> b) correctly pushes items
        // into the vectors and builds the adjacency list in BFS order.

        let ws = TempWorkspace::new("bfs_state");
        let mut handler = ErrorCollector::new();

        let workspace = canon(&ws.create_dir("workspace"));

        let dir_a = canon(&ws.create_dir("workspace/a"));
        let dir_b = canon(&ws.create_dir("workspace/b"));

        let main_content = "use a::mock_file::mock_item;";
        let a_content = "use b::mock_file::mock_item;";
        let b_content = "";

        let main_file = canon(&ws.create_file("workspace/main.simf", main_content));
        let a_file = canon(&ws.create_file("workspace/a/mock_file.simf", a_content));
        let b_file = canon(&ws.create_file("workspace/b/mock_file.simf", b_content));

        let mut map = DependencyMap::new();

        map.insert(workspace.clone(), "a".to_string(), dir_a)
            .unwrap();
        map.insert(workspace.clone(), "b".to_string(), dir_b)
            .unwrap();
        let map = Arc::new(map);

        let main_source = SourceFile::new(main_file.as_path(), Arc::from(main_content));
        let main_program_option =
            parse::Program::parse_from_str_with_errors(&main_source, &mut handler);

        let Some(main_program) = main_program_option else {
            eprintln!("Parser Error in Test Setup: {}", handler);
            std::process::exit(1);
        };

        // Act
        let graph_option =
            DependencyGraph::new(main_source, map, &main_program, &mut handler).unwrap();

        let Some(graph) = graph_option else {
            eprintln!("DependencyGraph Error: {}", handler);
            std::process::exit(1);
        };

        // Assert: Size checks
        assert_eq!(graph.modules.len(), 3);
        assert_eq!(graph.paths.len(), 3);

        // Assert: Ensure BFS assigned the IDs in the exact correct order
        let main_id = *graph.lookup.get(&main_file).unwrap();
        let a_id = *graph.lookup.get(&a_file).unwrap();
        let b_id = *graph.lookup.get(&b_file).unwrap();

        assert_eq!(main_id, 0);
        assert_eq!(a_id, 1);
        assert_eq!(b_id, 2);

        // Assert: Ensure the Adjacency List (dependencies map) linked them correctly
        assert_eq!(
            *graph.dependencies.get(&main_id).unwrap(),
            vec![a_id],
            "Main depends on A"
        );
        assert_eq!(
            *graph.dependencies.get(&a_id).unwrap(),
            vec![b_id],
            "A depends on B"
        );
        assert!(
            !graph.dependencies.contains_key(&b_id),
            "B depends on nothing"
        );
    }
}
