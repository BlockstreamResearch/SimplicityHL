//! The `driver` module is responsible for module resolution and dependency management.
//!
//! Our compiler operates in a strict pipeline: `Lexer -> Parser -> Driver -> AST`.
//! While the Parser only understands a single file at a time, the Driver processes
//! multiple files, resolves their dependencies, and converts them into a unified
//! structure ready for final AST construction.
//!
//! # Architecture
//!
//! ## Dependency Graph & Linearization
//!
//! The driver parses the root file and recursively discovers all imported modules
//! to build a Directed Acyclic Graph (DAG) of the project's dependencies. Because
//! the final AST requires a flat array of items, the driver applies a deterministic
//! linearization strategy to this DAG. This safely flattens the multi-file project
//! into a single, logically ordered sequence.
//!
//! ## Project Structure & Entry Point
//!
//! SimplicityHL programs begin execution at a single entry point file,
//! which the driver registers internally as the root [`MAIN_MODULE`].
//! This is typically the file passed as the root to the [`DependencyGraph::new`] function.
//!
//! External libraries are explicitly linked using the `--dep` flag. The driver
//! resolves and parses these external files relative to the entry point during
//! the dependency graph construction.

mod linearization;
mod resolve_order;

use std::collections::{HashMap, HashSet, VecDeque};
use std::path::PathBuf;
use std::sync::Arc;

use crate::error::{Error, ErrorCollector, RichError, Span};
use crate::parse::{self, ParseFromStrWithErrors};
use crate::resolution::{DependencyMap, ResolvedUse};
use crate::source::{CanonPath, CanonSourceFile};

/// The reserved identifier for the program's entry point.
pub(crate) const MAIN_STR: &str = "main";

/// The reserved identifier for the local workspace root.
pub(crate) const CRATE_STR: &str = "crate";

/// The root node index in the [`DependencyGraph`] representing the entry file.
pub(crate) const MAIN_MODULE: usize = 0;

/// Represents a single, isolated file in the SimplicityHL project.
/// In this architecture, a file and a module are the exact same thing.
#[derive(Debug, Clone)]
struct SourceModule {
    source: CanonSourceFile,
    /// The completely parsed program for this specific file.
    /// it contains all the functions, aliases, and imports defined inside the file.
    program: parse::Program,
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
pub(crate) struct DependencyGraph {
    /// Implements the Arena Pattern to act as the sole, centralized owner of all parsed modules.
    ///
    /// In C++ or Java, a graph would typically link dependencies using direct memory
    /// pointers (e.g., `List<Module*>`). In Rust, doing this requires either
    /// lifetimes or performance-heavy reference counting (`Rc<RefCell<T>>`).
    ///
    /// Using a flat `Vec` as a memory arena is the idiomatic Rust solution.
    modules: Vec<SourceModule>,

    /// The configuration environment.
    /// Used to resolve external library dependencies and invoke their associated functions.
    dependency_map: Arc<DependencyMap>,

    /// Fast lookup: `CanonPath` -> Module ID.
    /// A reverse index mapping absolute file paths to their internal IDs.
    /// This solves the duplication problem, ensuring each file is only parsed once.
    lookup: HashMap<CanonPath, usize>,

    /// Fast lookup: Module ID -> `CanonPath`.
    ///
    /// A direct index mapping internal IDs back to their absolute file paths.
    /// This serves as the exact inverse of the `lookup` map.
    ///
    /// This is highly useful for error reporting and diagnostics.
    paths: Vec<CanonPath>,

    /// Memoized results of [`crate::resolution::DependencyMap::resolve_path`] to avoid
    /// resolving the same [`parse::UseDecl`] twice — once during the driver phase
    /// and once during the building phase after linearization.
    use_cache: HashMap<parse::UseDecl, ResolvedUse>,

    // TODO: Consider to optimising this with `Vec` instead of `HashMap`
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
    /// This function will return an `Err(String)` only for critical internal compiler errors.
    pub fn new(
        root_source: CanonSourceFile,
        dependency_map: Arc<DependencyMap>,
        root_program: &parse::Program,
        handler: &mut ErrorCollector,
    ) -> Result<Option<Self>, String> {
        let mut graph = Self {
            modules: vec![SourceModule {
                source: root_source.clone(),
                program: root_program.clone(),
            }],
            dependency_map,
            lookup: HashMap::new(),
            paths: vec![root_source.name().clone()],
            use_cache: HashMap::new(),
            dependencies: HashMap::new(),
        };

        graph.lookup.insert(root_source.name().clone(), MAIN_MODULE);
        graph.dependencies.insert(MAIN_MODULE, Vec::new());

        let mut use_cache = HashMap::new();
        let mut queue = VecDeque::new();
        queue.push_back(MAIN_MODULE);

        // Prevent errors in the checked files from being doubled in the `load_and_parse_dependencies` function.
        let mut invalid_imports = HashSet::new();

        while let Some(curr_id) = queue.pop_front() {
            let Some(current_source_module) = graph.modules.get(curr_id) else {
                return Err(format!(
                    "Internal Driver Error: Module ID {} is in the queue but missing from the graph.modules.",
                    curr_id
                ));
            };

            // We need this to report errors inside THIS file.
            let importer_source = current_source_module.source.clone();
            let current = CurrentModule {
                id: curr_id,
                source: importer_source,
            };

            let valid_imports = Self::resolve_imports(
                &current_source_module.program,
                &current,
                &graph.dependency_map,
                &mut use_cache,
                handler,
            );

            let mut ctx = LoadContext {
                invalid_imports: &mut invalid_imports,
                handler,
                queue: &mut queue,
            };
            graph.load_and_parse_dependencies(&current, valid_imports, &mut ctx);
        }

        graph.use_cache = use_cache;

        // TODO: Consider getting rid of the 'String' error here and changing it to a more appropriate error
        // (e.g. 'Result<Self, ErrorCollector>') after resolving https://github.com/BlockstreamResearch/SimplicityHL/issues/270.
        Ok((!handler.has_errors()).then_some(graph))
    }

    /// This helper cleanly encapsulates the process of loading source text, parsing it
    /// into an `parse::Program`, and combining them so the compiler can easily work with the file.
    /// If the file is missing or contains syntax errors, it logs the diagnostic to the
    /// `ErrorCollector` and safely returns `None`.
    fn parse_and_get_source_module(
        path: &CanonPath,
        importer_source: &CanonSourceFile,
        span: Span,
        handler: &mut ErrorCollector,
    ) -> Option<SourceModule> {
        let Ok(content) = std::fs::read_to_string(path.as_path()) else {
            let err = RichError::new(
                Error::FileNotFound {
                    filename: PathBuf::from(path.as_path()),
                },
                span,
            )
            .with_source(importer_source.clone());

            handler.push(err);
            return None;
        };

        let mut error_handler = ErrorCollector::new();
        let source = CanonSourceFile::new(path.clone(), Arc::from(content));

        let ast = parse::Program::parse_from_str_with_errors(source.clone(), &mut error_handler);

        if error_handler.has_errors() {
            handler.extend_with_handler(source, &error_handler);
            None
        } else {
            ast.map(|program| SourceModule { source, program })
        }
    }

    /// PHASE 1 OF GRAPH CONSTRUCTION: Resolves all `use` declarations within a single
    /// [`parse::Program`], recursively walking into inline `mod` blocks.
    ///
    /// Results are cached in `use_cache` to avoid redundant filesystem lookups during
    /// later construction phases.
    /// Note: This is a specialized helper designed exclusively for [`DependencyGraph::new`].
    fn resolve_imports(
        current_program: &parse::Program,
        current_module: &CurrentModule,
        dependency_map: &DependencyMap,
        use_cache: &mut HashMap<parse::UseDecl, ResolvedUse>,
        handler: &mut ErrorCollector,
    ) -> Vec<(CanonPath, Span)> {
        let mut ctx = ImportContext {
            current: current_module.clone(),
            dependency_map,
            use_cache,
            handler,
        };

        let mut valid_imports = Vec::new();
        for item in current_program.items() {
            ctx.process_item(item, &mut valid_imports);
        }
        valid_imports
    }

    /// PHASE 2 OF GRAPH CONSTRUCTION: Loads, parses, and registers new dependencies.
    /// Note: This is a specialized helper designed exclusively for [`DependencyGraph::new`].
    fn load_and_parse_dependencies(
        &mut self,
        current: &CurrentModule,
        valid_imports: Vec<(CanonPath, Span)>,
        ctx: &mut LoadContext,
    ) {
        for (path, import_span) in valid_imports {
            if ctx.invalid_imports.contains(&path) {
                continue;
            }

            if let Some(&existing_id) = self.lookup.get(&path) {
                let deps = self.dependencies.entry(current.id).or_default();
                if !deps.contains(&existing_id) {
                    deps.push(existing_id);
                }
                continue;
            }

            let Some(module) =
                Self::parse_and_get_source_module(&path, &current.source, import_span, ctx.handler)
            else {
                // Safe to ignore output: previous `.contains` check prevents collisions.
                let _ = ctx.invalid_imports.insert(path);
                continue;
            };

            let last_ind = self.modules.len();
            self.modules.push(module);

            self.lookup.insert(path.clone(), last_ind);
            self.paths.push(path.clone());
            self.dependencies
                .entry(current.id)
                .or_default()
                .push(last_ind);
            ctx.queue.push_back(last_ind);
        }
    }
}

/// Groups all shared state for import resolution to avoid threading a lot of parameters
/// through every recursive call. Lives only for the duration of [`resolve_imports`].
struct ImportContext<'a> {
    current: CurrentModule,
    dependency_map: &'a DependencyMap,
    use_cache: &'a mut HashMap<parse::UseDecl, ResolvedUse>,
    handler: &'a mut ErrorCollector,
}

impl<'a> ImportContext<'a> {
    /// Resolves a single `use` declaration, caches the result for reuse during
    /// later graph construction phases, and returns the resolved path and span.
    /// Returns `None` and reports to `handler` if resolution fails.
    fn resolve_single(&mut self, use_decl: &parse::UseDecl) -> Option<(CanonPath, Span)> {
        let resolved = match self
            .dependency_map
            .resolve_path_internal(self.current.source.name(), use_decl)
        {
            Ok(res) => res,
            Err(err) => {
                self.handler
                    .push(err.with_source(self.current.source.clone()));
                return None;
            }
        };

        // We assign a file ID to prevent collisions between identical `use` statements across different files.
        // For instance, `use crate::A::foo;` in the local workspace and in an external dependency
        // might resolve to completely different implementations of the `foo` function.
        let mut use_decl = use_decl.clone();
        let span = *use_decl.span();
        use_decl.set_file_id(self.current.id);

        let result: (CanonPath, Span) = (resolved.path.clone(), span);

        // Since we found an error, when we can reevalute the result, we do not want to break it again
        // So, add error to prevent similar cases in the future
        if let Some(old_value) = self.use_cache.insert(use_decl, resolved) {
            let msg = format!(
                "Reevaluated an existing use_decl. Old value was: {:?}",
                old_value
            );
            let err = RichError::new(Error::Internal { msg }, span)
                .with_source(self.current.source.clone());
            self.handler.push(err);
        }
        Some(result)
    }

    /// Recursively walks an item, collecting resolved imports.
    /// Recurses into inline `mod` blocks.
    fn process_item(&mut self, item: &parse::Item, valid_imports: &mut Vec<(CanonPath, Span)>) {
        match item {
            parse::Item::Use(use_decl) => {
                if let Some(import) = self.resolve_single(use_decl) {
                    valid_imports.push(import);
                }
            }
            parse::Item::Module(module) => {
                for item in module.items() {
                    self.process_item(item, valid_imports);
                }
            }

            // These items carry no import information at this stage and can be safely skipped.
            parse::Item::TypeAlias(_) | parse::Item::Function(_) | parse::Item::Ignored => {}
        }
    }
}

/// Shared mutable state threaded through dependency loading.
/// Lives only for the duration of [`DependencyGraph::new`].
struct LoadContext<'a> {
    invalid_imports: &'a mut HashSet<CanonPath>,
    handler: &'a mut ErrorCollector,
    queue: &'a mut VecDeque<usize>,
}

/// The currently processed module and its source, used for error reporting
/// and dependency registration.
#[derive(Debug, Clone)]
struct CurrentModule {
    id: usize,
    source: CanonSourceFile,
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::resolution::tests::{build_map, canon};
    use crate::test_utils::TempWorkspace;

    /// Initializes a raw graph environment for testing, explicitly allowing for and capturing failure states.
    ///
    /// This function handles the boilerplate of setting up a workspace, virtual files, and dependency maps.
    /// It is primarily used to test error handling (e.g., syntax errors, unmapped imports) by returning
    /// the raw results and the error collector without automatically panicking or exiting.
    ///
    /// # Arguments
    ///
    /// * `files` - A vector of tuples representing the file tree, formatted as `(file_path, file_content)`.
    ///   **Note:** The list must include exactly one `"main.simf"` to act as the root entry point.
    ///
    /// # Returns
    ///
    /// A 4-element tuple containing:
    /// 1. `Option<DependencyGraph>`: The constructed graph, or `None` if parsing/graph building failed.
    /// 2. `HashMap<String, usize>`: A lookup mapping file stems (e.g., `"A"` from `"A.simf"`) to their `FileID`.
    ///    This will be empty if graph creation fails.
    /// 3. `TempWorkspace`: The temporary directory instance. This must be kept in scope by the caller so
    ///    the OS doesn't delete the files before the test finishes.
    /// 4. `ErrorCollector`: The handler containing any logged errors, useful fo
    pub(crate) fn setup_graph_raw(
        files: Vec<(&str, &str)>,
    ) -> (
        Option<DependencyGraph>,
        HashMap<String, usize>,
        TempWorkspace,
        ErrorCollector,
    ) {
        let ws = TempWorkspace::new("graph");
        let mut handler = ErrorCollector::new();

        // Create base directories
        let workspace_dir = canon(&ws.create_dir("workspace"));
        let lib_dir = canon(&ws.create_dir("workspace/libs/lib"));

        // Set up the dependency map for imports (e.g. `use lib::...`)
        let map =
            Arc::new(build_map(&workspace_dir, &[(&workspace_dir, "lib", &lib_dir)]).unwrap());

        let mut root_file_path = None;
        let mut root_content = String::new();

        // Create all requested files
        for (path, content) in files {
            let full_path = format!("workspace/{}", path);
            let created_file = canon(&ws.create_file(&full_path, content));

            if path == "main.simf" {
                root_file_path = Some(created_file);
                root_content = content.to_string();
            }
        }

        let root_p = root_file_path.expect("main.simf must be defined in file list");
        let main_canon_source = CanonSourceFile::new(root_p, Arc::from(root_content));

        let main_program_option =
            parse::Program::parse_from_str_with_errors(main_canon_source.clone(), &mut handler);

        let Some(main_program) = main_program_option else {
            return (None, HashMap::new(), ws, handler);
        };

        let graph_option =
            DependencyGraph::new(main_canon_source, map, &main_program, &mut handler).unwrap();

        let mut file_ids = HashMap::new();

        if let Some(ref graph) = graph_option {
            for (path, id) in &graph.lookup {
                let file_stem = path
                    .as_path()
                    .file_stem()
                    .unwrap()
                    .to_string_lossy()
                    .to_string();
                file_ids.insert(file_stem, *id);
            }
        }

        (graph_option, file_ids, ws, handler)
    }

    /// Initializes a complete graph environment for testing, expecting strict success.
    ///
    /// This wrapper around [`setup_graph_raw`] is designed for "happy path" tests. It streamlines
    /// testing by guaranteeing a valid graph is returned, stripping away the error handling boilerplate.
    ///
    /// # Arguments
    ///
    /// * `files` - A vector of tuples representing the file tree, formatted as `(file_path, file_content)`.
    ///   **Note:** The list must include exactly one `"main.simf"` to act as the root entry point.
    ///
    /// # Returns
    ///
    /// A 3-element tuple containing:
    /// 1. `DependencyGraph`: The successfully constructed dependency graph.
    /// 2. `HashMap<String, usize>`: A lookup mapping file stems (e.g., `"A"` from `"A.simf"`) to their `FileID`.
    /// 3. `TempWorkspace`: The temporary directory instance. This must be kept in scope by the caller so
    ///    the OS doesn't delete the files before the test finishes.
    ///
    /// # Exits
    ///
    /// This function will immediately panic and print the collected errors
    /// to standard error if the parser or graph builder encounters any issues.
    pub(crate) fn setup_graph(
        files: Vec<(&str, &str)>,
    ) -> (DependencyGraph, HashMap<String, usize>, TempWorkspace) {
        let (graph_option, file_ids, ws, handler) = setup_graph_raw(files);

        let Some(graph) = graph_option else {
            panic!(
                "Parser or DependencyGraph Error in Test Setup:\n{}",
                handler
            );
        };

        (graph, file_ids, ws)
    }

    #[test]
    fn test_simple_import() {
        // Setup:
        // root.simf -> "use lib::math::some_func;"
        // libs/lib/math.simf -> ""

        let (graph, ids, _ws) = setup_graph(vec![
            ("main.simf", "use lib::math::some_func;"),
            ("libs/lib/math.simf", ""),
        ]);

        assert_eq!(graph.modules.len(), 2, "Should have Root and Math module");

        let root_id = ids["main"];
        let math_id = ids["math"];

        assert!(
            graph
                .dependencies
                .get(&root_id)
                .is_some_and(|deps| deps.contains(&math_id)),
            "Root (main.simf) should depend on Math (math.simf)"
        );
    }

    #[test]
    fn test_diamond_dependency_deduplication() {
        // Setup:
        // root -> imports A, B
        // A -> imports Common
        // B -> imports Common
        // Expected: Common loaded ONLY ONCE.

        let (graph, ids, _ws) = setup_graph(vec![
            ("main.simf", "use lib::A::foo; use lib::B::bar;"),
            ("libs/lib/A.simf", "use crate::Common::dummy1;"),
            ("libs/lib/B.simf", "use crate::Common::dummy2;"),
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
            graph
                .dependencies
                .get(&a_id)
                .is_some_and(|deps| deps.contains(&common_id)),
            "A should depend on Common"
        );

        // Check B -> Common (Crucial: Must be the SAME common_id)
        assert!(
            graph
                .dependencies
                .get(&b_id)
                .is_some_and(|deps| deps.contains(&common_id)),
            "B should depend on Common"
        );
    }

    #[test]
    fn test_cyclic_dependency() {
        // Setup: A <-> B cycle
        // main -> imports A
        // A -> imports B
        // B -> imports A

        let (graph, ids, _ws) = setup_graph(vec![
            ("main.simf", "use lib::A::entry;"),
            ("libs/lib/A.simf", "use crate::B::func;"),
            ("libs/lib/B.simf", "use crate::A::func;"),
        ]);

        let a_id = ids["A"];
        let b_id = ids["B"];

        // Check if graph correctly recorded the cycle
        assert!(
            graph
                .dependencies
                .get(&a_id)
                .is_some_and(|deps| deps.contains(&b_id)),
            "A should depend on B"
        );
        assert!(
            graph
                .dependencies
                .get(&b_id)
                .is_some_and(|deps| deps.contains(&a_id)),
            "B should depend on A"
        );
    }

    #[test]
    fn test_fails_on_unmapped_imports() {
        // Setup: root imports from "unknown", which is not in our dependency map.
        // We use `setup_graph_raw` because we expect graph generation to fail and
        // emit an error, rather than panicking the standard test helper.
        let (graph_option, _ids, _ws, handler) =
            setup_graph_raw(vec![("main.simf", "use unknown::library::item;")]);

        assert!(
            graph_option.is_none(),
            "Graph unexpectedly succeeded despite having an unknown import!"
        );

        assert!(
            handler.has_errors(),
            "The ErrorCollector should have logged an error about the unmapped import"
        );
    }

    #[test]
    fn test_new_bfs_traversal_state() {
        // Goal: Verify that a simple chain (main -> a -> b) correctly pushes items
        // into the vectors and builds the adjacency list in BFS order.

        let (graph, ids, _ws) = setup_graph(vec![
            ("main.simf", "use lib::A::mock_item;"),
            ("libs/lib/A.simf", "use crate::B::mock_item;"),
            ("libs/lib/B.simf", ""),
        ]);

        // Assert: Size checks
        assert_eq!(graph.modules.len(), 3);
        assert_eq!(graph.paths.len(), 3);

        // Assert: Ensure BFS assigned the IDs in the exact correct order
        let main_id = ids["main"];
        let a_id = ids["A"];
        let b_id = ids["B"];

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

        // Check that B has no dependencies
        let b_has_no_deps = graph
            .dependencies
            .get(&b_id)
            .map_or(true, |deps| deps.is_empty());
        assert!(b_has_no_deps, "B depends on nothing");
    }
}
