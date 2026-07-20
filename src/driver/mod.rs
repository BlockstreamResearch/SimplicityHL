#![allow(rustdoc::private_intra_doc_links)]
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
//! This is typically the file passed as the root to the [`DependencyGraph::build_program`] function.
//!
//! External libraries are explicitly linked using the `--dep` flag. The driver
//! resolves and parses these external files relative to the entry point during
//! the dependency graph construction.

mod linearization;
mod resolve_order;

#[cfg(test)]
mod version_tests;

use std::collections::{HashMap, HashSet, VecDeque};
use std::path::PathBuf;
use std::sync::Arc;

use crate::error::{Diagnostic, DiagnosticManager, Error, Span};
use crate::parse::{self, ParseFromStrWithErrors};
use crate::resolution::{DependencyMap, ResolvedUse};
use crate::source::{CanonPath, CanonSourceFile};
use crate::unstable::UnstableFeatures;

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

/// Record of all modules that was discovered.
#[derive(Debug, Clone)]
pub struct SourceMap {
    /// Fast lookup: `CanonPath` -> Module ID.
    /// A reverse index mapping absolute file paths to their internal IDs.
    /// This solves the duplication problem, ensuring each file is only parsed once.
    ids: HashMap<CanonPath, usize>,

    /// Fast lookup: Module ID -> `CanonPath`.
    ///
    /// A direct index mapping internal IDs back to their absolute file paths.
    /// This serves as the exact inverse of the `lookup` map.
    ///
    /// This is highly useful for error reporting and diagnostics.
    entries: Vec<CanonSourceFile>,
}

impl SourceMap {
    pub(crate) fn with_source(source: CanonSourceFile) -> Self {
        let mut ids = HashMap::new();

        ids.insert(source.name().clone(), MAIN_MODULE);

        Self {
            ids,
            entries: vec![source],
        }
    }

    pub(crate) fn insert(&mut self, entry: CanonSourceFile) {
        let id = self.entries.len();

        self.ids.insert(entry.name().clone(), id);
        self.entries.push(entry);

        debug_assert_eq!(self.ids.len(), self.entries.len());
    }

    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn id(&self, path: &CanonPath) -> Option<usize> {
        self.ids.get(path).copied()
    }

    pub fn entry(&self, id: usize) -> Option<&CanonSourceFile> {
        self.entries.get(id)
    }

    pub fn content(&self, id: usize) -> Option<Arc<str>> {
        self.entries.get(id).map(|e| e.content().clone())
    }

    pub fn path(&self, id: usize) -> Option<&CanonPath> {
        self.entries.get(id).map(|e| e.name())
    }

    pub fn iter(&self) -> impl Iterator<Item = (&CanonPath, &usize)> {
        self.ids.iter()
    }
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
    /// An entry should exist only for files that parsed successfully.
    ///
    /// A missing key for an id present in `sources` means the file was poisoned
    /// during discovery and its imports were not propagated.
    modules: HashMap<usize, SourceModule>,

    /// The configuration environment.
    /// Used to resolve external library dependencies and invoke their associated functions.
    dependency_map: Arc<DependencyMap>,

    /// Fast bidirectional lookup between `CanonPath` and Module IDs
    sources: SourceMap,

    /// Memoizes [`crate::resolution::DependencyMap::resolve_path_internal`] results,
    /// keyed by the source [`Span`] of each `use` declaration, so the resolver runs
    /// once per occurrence and the linearization phase can look the result up directly.
    use_cache: HashMap<Span, ResolvedUse>,

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
    /// Compile a project into a single `parse::Program`.
    ///
    /// Runs both driver phases: dependency discovery, then linearization and
    /// assembly. The returned [`DiagnosticManager`] has its [`SourceMap`]
    /// attached and is ready to render.
    ///
    /// # Arguments
    ///
    /// * `root_source` - The entry-point source file of the project.
    /// * `dependency_map` - The context-aware mapping rules used to resolve external imports.
    /// * `unstable_features` - Feature gates active for this compilation
    ///
    /// # Returns
    ///
    /// * `(Some(graph), diagnostics)` if the graph was built without errors.
    ///   Warnings may be present in `diagnostics`; sources are on the graph.
    /// * `(None, diagnostics)` if any error was reported. Sources are on
    ///   the diagnostics manager, ready for rendering.
    pub fn build_program(
        root_source: CanonSourceFile,
        dependency_map: Arc<DependencyMap>,
        unstable_features: &UnstableFeatures,
    ) -> (Option<parse::Program>, DiagnosticManager) {
        let (graph, mut diagnostics) =
            Self::build_graph(root_source, dependency_map, unstable_features);

        let Some(graph) = graph else {
            return (None, diagnostics);
        };

        let program = graph.linearize_and_assemble(&mut diagnostics);
        diagnostics.with_sources(graph.sources);
        (program, diagnostics)
    }

    /// Build the dependency graph without linearizing. Exposed for tests
    /// that need to inspect the intermediate graph state.
    fn build_graph(
        root_source: CanonSourceFile,
        dependency_map: Arc<DependencyMap>,
        unstable_features: &UnstableFeatures,
    ) -> (Option<Self>, DiagnosticManager) {
        let mut diagnostics = DiagnosticManager::default();
        let sources = SourceMap::with_source(root_source.clone());

        let Some(program) = parse::Program::parse_from_str_with_errors(
            MAIN_MODULE,
            &root_source.content(),
            unstable_features,
            &mut diagnostics,
        ) else {
            diagnostics.with_sources(sources);
            return (None, diagnostics);
        };

        let mut modules = HashMap::new();
        modules.insert(
            MAIN_MODULE,
            SourceModule {
                source: root_source.clone(),
                program,
            },
        );

        // Build the graph
        let mut graph = Self {
            modules,
            dependency_map,
            sources,
            use_cache: HashMap::new(),
            dependencies: HashMap::new(),
        };

        graph.discover_dependencies(&mut diagnostics, unstable_features);

        if diagnostics.has_errors() {
            diagnostics.with_sources(graph.sources);
            (None, diagnostics)
        } else {
            (Some(graph), diagnostics)
        }
    }

    /// BFS over `use` declarations, populating `modules`, `dependencies`,
    /// and `use_cache`. Errors go into `diagnostics`; no `Result` because
    /// partial state on failure is still useful for reporting.
    fn discover_dependencies(
        &mut self,
        diagnostics: &mut DiagnosticManager,
        unstable_features: &UnstableFeatures,
    ) {
        self.dependencies.insert(MAIN_MODULE, Vec::new());
        let mut use_cache = HashMap::new();
        let mut queue = VecDeque::new();
        queue.push_back(MAIN_MODULE);

        // Prevent errors in the checked files from being doubled in the `load_and_parse_dependencies` function.
        let mut invalid_imports = HashSet::new();

        while let Some(curr_id) = queue.pop_front() {
            let Some(current_source_module) = self.modules.get(&curr_id) else {
                debug_assert!(
                    false,
                    "poisoned invariant broken: id {curr_id} popped without a module"
                );
                diagnostics.push(Diagnostic::global(Error::Internal {
                    msg: format!("module id {curr_id} missing from graph; aborting compilation"),
                }));
                return;
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
                &self.dependency_map,
                &mut use_cache,
                diagnostics,
            );

            let mut ctx = LoadContext {
                invalid_imports: &mut invalid_imports,
                diagnostics,
                queue: &mut queue,
                unstable_features,
            };
            self.load_and_parse_dependencies(&current, valid_imports, &mut ctx);
        }

        self.use_cache = use_cache;
    }

    /// PHASE 1 OF GRAPH CONSTRUCTION: Resolves all `use` declarations within a single
    /// [`parse::Program`], recursively walking into inline `mod` blocks.
    ///
    /// Results are cached in `use_cache` to avoid redundant filesystem lookups during
    /// later construction phases.
    /// Note: This is a specialized helper designed exclusively for `DependencyGraph::build_graph`.
    fn resolve_imports(
        current_program: &parse::Program,
        current_module: &CurrentModule,
        dependency_map: &DependencyMap,
        use_cache: &mut HashMap<Span, ResolvedUse>,
        diagnostics: &mut DiagnosticManager,
    ) -> Vec<(CanonPath, Span)> {
        let mut ctx = ImportContext {
            current: current_module.clone(),
            dependency_map,
            use_cache,
            diagnostics,
        };

        let mut valid_imports = Vec::new();
        for item in current_program.items() {
            ctx.process_item(item, &mut valid_imports);
        }
        valid_imports
    }

    /// PHASE 2 OF GRAPH CONSTRUCTION: Loads, parses, and registers new dependencies.
    /// Note: This is a specialized helper designed exclusively for `DependencyGraph::build_graph`.
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

            if let Some(existing_id) = self.sources.id(&path) {
                let deps = self.dependencies.entry(current.id).or_default();
                if !deps.contains(&existing_id) {
                    deps.push(existing_id);
                }
                continue;
            }

            let Ok(content) = std::fs::read_to_string(path.as_path()) else {
                let err = Diagnostic::new(
                    Error::FileNotFound {
                        filename: PathBuf::from(path.as_path()),
                    },
                    import_span,
                );

                ctx.diagnostics.push(err);

                // Safe to ignore output: previous `.contains` check prevents collisions.
                let _ = ctx.invalid_imports.insert(path);
                continue;
            };

            // Store source inside source_map, before checking is it valid or not.
            let source = CanonSourceFile::new(path.clone(), Arc::from(content));

            // Must be read before inserting!
            let new_id = self.sources.len();
            self.sources.insert(source.clone());

            let Some(parsed_program) = Self::parse_and_get_source_module(
                new_id,
                &source.content(),
                ctx.diagnostics,
                ctx.unstable_features,
            ) else {
                // Safe to ignore output: previous `.contains` check prevents collisions.
                let _ = ctx.invalid_imports.insert(path);
                continue;
            };

            let module = SourceModule {
                source: source.clone(),
                program: parsed_program,
            };

            self.modules.insert(new_id, module);
            self.dependencies
                .entry(current.id)
                .or_default()
                .push(new_id);
            ctx.queue.push_back(new_id);
        }
    }

    /// This helper cleanly encapsulates the process of parsing source text into an
    /// `parse::Program`, and combining them so the compiler can easily work with the file.
    /// If the file is contains syntax errors, it logs the diagnostic to the
    /// `ErrorCollector` and safely returns `None`.
    fn parse_and_get_source_module(
        new_id: usize,
        content: &str,
        diagnostics: &mut DiagnosticManager,
        unstable_features: &UnstableFeatures,
    ) -> Option<parse::Program> {
        let before = diagnostics.error_count();

        let ast = parse::Program::parse_from_str_with_errors(
            new_id,
            content,
            unstable_features,
            diagnostics,
        );

        if diagnostics.error_count() > before {
            return None;
        }

        ast
    }
}

/// Groups all shared state for import resolution to avoid threading a lot of parameters
/// through every recursive call. Lives only for the duration of [`DependencyGraph::resolve_imports`].
struct ImportContext<'a> {
    current: CurrentModule,
    dependency_map: &'a DependencyMap,
    use_cache: &'a mut HashMap<Span, ResolvedUse>,
    diagnostics: &'a mut DiagnosticManager,
}

impl<'a> ImportContext<'a> {
    /// Recursively walks an item, collecting resolved imports.
    /// Recurses into inline `mod` blocks.
    fn process_item(&mut self, item: &parse::Item, valid_imports: &mut Vec<(CanonPath, Span)>) {
        match item {
            parse::Item::Use(use_decl) => valid_imports.extend(self.resolve_single(use_decl)),
            parse::Item::Module(module) => {
                for item in module.items() {
                    self.process_item(item, valid_imports);
                }
            }

            // These items carry no import information at this stage and can be safely skipped.
            parse::Item::TypeAlias(_) | parse::Item::Function(_) | parse::Item::Ignored => {}
        }
    }

    /// Resolves a single `use` declaration, caches the result for reuse during
    /// later graph construction phases, and returns the resolved path and span.
    /// Returns `None` and reports to `diagnostics` if resolution fails.
    fn resolve_single(&mut self, use_decl: &parse::UseDecl) -> Option<(CanonPath, Span)> {
        let resolved = match self
            .dependency_map
            .resolve_path_internal(self.current.source.name(), use_decl)
        {
            Ok(res) => res,
            Err(err) => {
                self.diagnostics.push(err);
                return None;
            }
        };

        let span = *use_decl.span();
        let result: (CanonPath, Span) = (resolved.path.clone(), span);

        // Since we found an error, when we can reevalute the result, we do not want to break it again
        // So, add error to prevent similar cases in the future
        if let Some(old_value) = self.use_cache.insert(span, resolved) {
            let msg = format!(
                "Reevaluated an existing use_decl. Old value was: {:?}",
                old_value
            );

            let err = Diagnostic::new(Error::Internal { msg }, span);
            self.diagnostics.push(err);
        }

        Some(result)
    }
}

/// Shared mutable state threaded through dependency loading.
/// Lives only for the duration of `DependencyGraph::discover_dependencies`.
struct LoadContext<'a> {
    invalid_imports: &'a mut HashSet<CanonPath>,
    diagnostics: &'a mut DiagnosticManager,
    queue: &'a mut VecDeque<usize>,
    unstable_features: &'a UnstableFeatures,
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
    /// 4. `DiagnosticManager`: The manager containing any logged errors.
    pub(crate) fn setup_graph_raw(
        files: Vec<(&str, &str)>,
    ) -> (
        Option<DependencyGraph>,
        HashMap<String, usize>,
        TempWorkspace,
        DiagnosticManager,
    ) {
        let ws = TempWorkspace::new("graph");

        // Create base directories
        let workspace_dir = canon(&ws.create_dir("workspace"));
        let lib_dir = canon(&ws.create_dir("workspace/libs/lib"));

        // Set up the dependency map for imports (e.g. `use lib::...`)
        let dependency_map =
            Arc::new(build_map(&workspace_dir, &[(&workspace_dir, "lib", &lib_dir)]).unwrap());

        // Create all requested files
        let mut root_source_opt = None;
        for (path, content) in files {
            let full_path = format!("workspace/{}", path);
            let created = canon(&ws.create_file(&full_path, content));

            if path == "main.simf" {
                root_source_opt = Some(CanonSourceFile::new(created, Arc::from(content)));
            }
        }
        let root_source = root_source_opt.expect("main.simf must be defined in file list");

        let (graph_opt, diagnostics) =
            DependencyGraph::build_graph(root_source, dependency_map, &UnstableFeatures::all());

        let file_ids = match &graph_opt {
            Some(graph) => build_file_ids(&graph.sources),
            None => diagnostics
                .sources()
                .map(build_file_ids)
                .unwrap_or_default(),
        };

        (graph_opt, file_ids, ws, diagnostics)
    }

    fn build_file_ids(sources: &SourceMap) -> HashMap<String, usize> {
        sources
            .iter()
            .filter_map(|(path, id)| {
                let stem = path.as_path().file_stem()?;
                Some((stem.to_string_lossy().into_owned(), *id))
            })
            .collect()
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
    ) -> (
        DependencyGraph,
        HashMap<String, usize>,
        TempWorkspace,
        DiagnosticManager,
    ) {
        let (graph_option, file_ids, ws, diagnostics) = setup_graph_raw(files);

        let Some(graph) = graph_option else {
            panic!(
                "Parser or DependencyGraph Error in Test Setup:\n{}",
                diagnostics
            );
        };

        (graph, file_ids, ws, diagnostics)
    }

    #[test]
    fn test_simple_import() {
        // Setup:
        // root.simf -> "use lib::math::some_func;"
        // libs/lib/math.simf -> ""

        let (graph, ids, _ws, _diags) = setup_graph(vec![
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

        let (graph, ids, _ws, _diags) = setup_graph(vec![
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

        let (graph, ids, _ws, _diags) = setup_graph(vec![
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
        let (graph_option, _ids, _ws, diagnostics) =
            setup_graph_raw(vec![("main.simf", "use unknown::library::item;")]);

        assert!(
            graph_option.is_none(),
            "Graph unexpectedly succeeded despite having an unknown import!"
        );

        assert!(
            diagnostics.has_errors(),
            "The ErrorCollector should have logged an error about the unmapped import"
        );
    }

    #[test]
    fn test_new_bfs_traversal_state() {
        // Goal: Verify that a simple chain (main -> a -> b) correctly pushes items
        // into the vectors and builds the adjacency list in BFS order.

        let (graph, ids, _ws, _diags) = setup_graph(vec![
            ("main.simf", "use lib::A::mock_item;"),
            ("libs/lib/A.simf", "use crate::B::mock_item;"),
            ("libs/lib/B.simf", ""),
        ]);

        // Assert: Size checks
        assert_eq!(graph.modules.len(), 3);
        assert_eq!(graph.sources.len(), 3);

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
