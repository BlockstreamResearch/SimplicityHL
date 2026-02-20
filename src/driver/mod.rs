//! The `driver` module is responsible for module resolution and dependency management.
//!
//! Our compiler operates in a strict pipeline: `Lexer -> Parser -> Driver -> AST`.
//! While the Parser only understands a single file at a time, the Driver processes
//! multiple files, resolves their dependencies, and converts them into a unified
//! structure ready for final AST construction.
//!
//! # Package Management & Distribution
//!
//! SimplicityHL is currently **transport-agnostic**, meaning it does not provide its own
//! package registry. Developers can use existing ecosystems to distribute `.simf` modules.
//!
//! ## Distributing via crates.io
//!
//! 1. **Publishing:** Create a Rust library (`cargo new --lib`), and place
//!    your `.simf` files inside it. Then publish the crate to `crates.io`.
//!
//! 2. **Downloading:** In the consuming Rust project, add the published crate to
//!    your `Cargo.toml`. Running `cargo build` forces Cargo to download the files
//!    to your global registry cache.
//!
//! 3. **Locating:** Find the exact path to the downloaded crate package on your system.
//!    *(e.g., `~/.cargo/registry/src/index.crates.io-<hash>/simplicity-calculator-0.1.0/`)*
//!
//! 4. **Linking:** Pass this path to the compiler using
//!    the `--lib` flag, assigning it a custom alias:
//!    ``` text
//!    simc path/to/main.simf --lib calc=~/.cargo/registry/src/.../simplicity-calculator-0.1.0/
//!    ```
//!
//! 5. **Importing:** Inside your `main.simf`, start with the assigned alias (`calc`).
//!    If the `.simf` file is nested inside subdirectories, the path must reflect
//!    that folder structure. Follow the alias with the directory names, the target
//!    filename, and finally the items to import:
//!    ``` text
//!    // If `calculator.simf` is directly in the library's root:
//!    use calc::calculator::{add_32, subtract_32};
//!
//!    // If `calculator.simf` is nested inside a `utils` directory:
//!    use calc::utils::calculator::{add_32, subtract_32};
//!    ```
//!
//! ## Distributing via npm
//!
//! NPM can also be used as a simple file delivery system for SimplicityHL,
//! which is especially useful for developers working in web environments.
//!
//! 1. **Publishing:** Create a directory, generate a `package.json` file
//!    (`npm init -y`), place your `.simf` files inside, and run `npm publish`.
//!
//! 2. **Downloading:** In the consuming project's directory, run
//!    `npm install <package-name>`. NPM will download the files locally.
//!
//! 3. **Locating:** The `.simf` files will be placed inside the standard
//!    `node_modules` directory at `./node_modules/<package-name>/`.
//!
//! 4. **Linking:** Pass this local path to the Simplicity compiler using
//!    the `--lib` flag, assigning it a custom alias:
//!    ``` text
//!    simc main.simf --lib calc=./node_modules/simplicity-calculator/
//!    ```
//!
//! 5. **Importing:** Inside your `main.simf`, use the alias exactly as
//!    you would with any other dependency:
//!    ``` text
//!    use calc::calculator::{add_32, subtract_32};
//!    ```
//!
//! # Architecture
//!
//! ## Dependency Graph & Linearization
//!
//! The driver parses the root file and recursively discovers all imported modules
//! to build a Directed Acyclic Graph (DAG) of the project's dependencies. Because
//! the final AST requires a flat array of items, the driver applies a deterministic
//! linearization strategy to this DAG. This safely flattens the multi-file project
//! into a single, logically ordered sequence, strictly enforcing visibility rules
//! and preventing duplicate imports.
//!
//! ## Project Structure & Entry Point
//!
//! SimplicityHL does not define a "project root" directory. Instead, the compiler
//! relies on a single entry point: the file passed as the first positional argument.
//! This file must contain the `main` function, which serves as the program's
//! starting point.
//!
//! External libraries are explicitly linked using the `--lib` flag. The driver
//! resolves and parses these external files relative to the entry point during
//! the dependency graph construction.

#[cfg(test)]
pub mod tests;

use std::collections::{BTreeMap, HashMap, VecDeque};
use std::fmt;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::error::{ErrorCollector, Span};
use crate::impl_eq_hash;
use crate::parse::{self, ParseFromStrWithErrors, Visibility};
use crate::resolution::{get_full_path, LibTable, SourceName};
use crate::str::Identifier;

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
    pub(self) modules: Vec<Module>,

    /// The configuration environment.
    /// Used to resolve xternal library dependencies and invoke their associated functions.
    pub config: Arc<LibTable>,

    /// Fast lookup: `SourceName` -> Module ID.
    /// A reverse index mapping absolute file paths to their internal IDs.
    /// This solves the duplication problem, ensuring each file is only parsed once.
    pub lookup: HashMap<SourceName, usize>,

    /// Fast lookup: Module ID -> `SourceName`.
    /// A direct index mapping internal IDs back to their absolute file paths.
    /// This serves as the exact inverse of the `lookup` map.
    pub paths: Arc<[SourceName]>,

    /// The Adjacency List: Defines the Directed acyclic Graph (DAG) of imports.
    ///
    /// The Key (`usize`) is the ID of a "Parent" module (the file doing the importing).
    /// The Value (`Vec<usize>`) is a list of IDs of the "Child" modules it relies on.
    ///
    /// Example: If `main.simf` (ID: 0) has `use lib::math;` (ID: 1) and `use lib::io;` (ID: 2),
    /// this map will contain: `{ 0: [1, 2] }`.
    pub dependencies: HashMap<usize, Vec<usize>>,
}

pub type FileResolutions = BTreeMap<Identifier, Visibility>;

/// The final, flattened representation of a SimplicityHL program.
///
/// This struct holds the fully resolved sequence of items, paths, and scope
/// resolutions, ready to be passed to the next stage of the compiler.
#[derive(Clone, Debug)]
pub struct Program {
    /// The linear sequence of compiled items (`Functions`, `TypeAliases`, etc.).
    items: Arc<[parse::Item]>,

    /// The list of source files that make up this program.
    paths: Arc<[SourceName]>,

    /// The visibility and scoping resolutions for each file.
    // Use BTreeMap instead of HashMap for the impl_eq_hash! macro.
    resolutions: Arc<[FileResolutions]>,

    span: Span,
}

impl Program {
    /// Converts a parsed one-file program directly into a driver program.
    ///
    /// This function takes a raw `parse::Program` and converts it into a `driver::Program`.
    /// It is strictly meant for single-file programs. Because it bypasses the full `ProjectGraph`
    /// dependency resolution, it will throw an error if the file contains any `use` statements.
    ///
    /// # Arguments
    /// * `parsed` - The parsed single file.
    /// * `root_path` - The source path of the file.
    ///
    /// # Errors
    /// Returns an `Err(String)` if the file contains `use` statements, or if registering an item fails.
    pub fn from_parse(parsed: &parse::Program, root_path: SourceName) -> Result<Self, String> {
        let root_path = root_path.without_extension();

        let mut items: Vec<parse::Item> = Vec::new();
        let mut resolutions: Vec<FileResolutions> = vec![BTreeMap::new()];

        let main_file_id = 0usize;
        let mut errors: Vec<String> = Vec::new();

        for item in parsed.items() {
            match item {
                parse::Item::Use(_) => {
                    errors.push("Unsuitable Use type".to_string());
                }
                parse::Item::TypeAlias(alias) => {
                    ProjectGraph::register_def(
                        &mut items,
                        &mut resolutions,
                        main_file_id,
                        item,
                        alias.name().clone().into(),
                        &parse::Visibility::Public,
                    );
                }
                parse::Item::Function(function) => {
                    ProjectGraph::register_def(
                        &mut items,
                        &mut resolutions,
                        main_file_id,
                        item,
                        function.name().clone().into(),
                        &parse::Visibility::Public,
                    );
                }
                parse::Item::Module => {}
            }
        }

        if !errors.is_empty() {
            return Err(errors.join("\n"));
        }

        Ok(Program {
            items: items.into(),
            paths: Arc::from([root_path]),
            resolutions: resolutions.into(),
            span: *parsed.as_ref(),
        })
    }

    /// Access the items of the program.
    pub fn items(&self) -> &[parse::Item] {
        &self.items
    }

    /// Access the paths of the program
    pub fn paths(&self) -> &[SourceName] {
        &self.paths
    }

    /// Access the scope items of the program.
    pub fn resolutions(&self) -> &[FileResolutions] {
        &self.resolutions
    }
}

impl_eq_hash!(Program; items, paths, resolutions);

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

// Function used by the C3 algorithm.
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

impl ProjectGraph {
    /// Initializes a new `ProjectGraph` by parsing the root program and discovering all dependencies.
    ///
    /// Performs a BFS to recursively parse `use` statements,
    /// building a DAG of the project's modules.
    ///
    /// # Arguments
    /// * `source_name` - The root file path (extension is stripped internally).
    /// * `config` - Library configuration for resolving external imports.
    /// * `root_program` - The parsed root file.
    ///
    /// # Errors
    ///
    /// This function will return an `Err(String)` in the following scenarios:
    /// * A referenced module file (e.g., declared via a `use` statement) does not exist on the file system.
    /// * The `parse_and_get_program` function encounters a syntax error while trying to parse one of the discovered dependency files.
    pub fn new(
        source_name: SourceName,
        config: Arc<LibTable>,
        root_program: &parse::Program,
    ) -> Result<Self, String> {
        let source_name = source_name.without_extension();
        let mut modules: Vec<Module> = vec![Module {
            parsed_program: root_program.clone(),
        }];
        let mut lookup: HashMap<SourceName, usize> = HashMap::new();
        let mut paths: Vec<SourceName> = vec![source_name.clone()];
        let mut dependencies: HashMap<usize, Vec<usize>> = HashMap::new();

        let root_id = 0;
        lookup.insert(source_name, root_id);
        dependencies.insert(root_id, Vec::new());

        // Implementation of the standard BFS algorithm with memoization and queue
        let mut queue = VecDeque::new();
        queue.push_back(root_id);

        while let Some(curr_id) = queue.pop_front() {
            let mut pending_imports: Vec<PathBuf> = Vec::new();
            let current_program = &modules[curr_id].parsed_program;

            for elem in current_program.items() {
                if let parse::Item::Use(use_decl) = elem {
                    if let Ok(path) = get_full_path(&config, use_decl) {
                        pending_imports.push(path);
                    }
                }
            }

            for path in pending_imports {
                let full_path = path.with_extension("simf");
                let source_path = SourceName::Real(path);

                if !full_path.is_file() {
                    return Err(format!("File in {:?}, does not exist", full_path));
                }

                if let Some(&existing_id) = lookup.get(&source_path) {
                    let deps = dependencies.entry(curr_id).or_default();
                    if !deps.contains(&existing_id) {
                        deps.push(existing_id);
                    }
                    continue;
                }

                let last_ind = modules.len();
                let program = parse_and_get_program(&full_path)?;

                modules.push(Module {
                    parsed_program: program,
                });
                lookup.insert(source_path.clone(), last_ind);
                paths.push(source_path.clone());
                dependencies.entry(curr_id).or_default().push(last_ind);

                queue.push_back(last_ind);
            }
        }

        Ok(Self {
            modules,
            config,
            lookup,
            paths: paths.into(),
            dependencies,
        })
    }

    /// Computes the linear resolution order of the project modules.
    ///
    /// # Errors
    /// Returns a `C3Error` if a cyclic dependency is detected or if a valid
    /// linearization is mathematically impossible.
    pub fn c3_linearize(&self) -> Result<Vec<usize>, C3Error> {
        self.linearize_module(0)
    }

    /// Internal helper to initiate the recursive C3 linearization process.
    fn linearize_module(&self, root: usize) -> Result<Vec<usize>, C3Error> {
        let mut memo = HashMap::<usize, Vec<usize>>::new();
        let mut visiting = Vec::<usize>::new();

        self.linearize_rec(root, &mut memo, &mut visiting)
    }

    /// Recursively calculates the C3 linearization sequence for a given module.
    ///
    /// Uses memoization to cache results and tracks the `visiting` path to
    /// detect infinite cyclic dependencies (e.g., A imports B, B imports A).
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

    /// Validates and registers an imported item from a dependency file.
    ///
    /// Ensures that the imported item is marked as public in the source file.
    /// If validation passes, the item is inserted into the current file's resolution table.
    fn process_use_item(
        resolutions: &mut [FileResolutions],
        file_id: usize,
        ind: usize,
        elem: &Identifier,
        use_decl_visibility: Visibility,
    ) -> Result<(), String> {
        if matches!(resolutions[ind][elem], parse::Visibility::Private) {
            return Err(format!(
                "Function {} is private and cannot be used.",
                elem.as_inner()
            ));
        }

        resolutions[file_id].insert(elem.clone(), use_decl_visibility);

        Ok(())
    }

    /// Registers a newly defined item (like a `Function` or `TypeAlias`) in the resolution table.
    fn register_def(
        items: &mut Vec<parse::Item>,
        resolutions: &mut [FileResolutions],
        file_id: usize,
        item: &parse::Item,
        name: Identifier,
        vis: &parse::Visibility,
    ) {
        items.push(item.clone());
        resolutions[file_id].insert(name, vis.clone());
    }

    /// Constructs the final flattened `Program` structure using the calculated C3 order.
    ///
    /// Iterates through the modules in the exact order specified by the C3 algorithm.
    /// It resolves `use` imports, registers definitions, and enforces visibility rules,
    /// combining everything into a single, one-dimensional `Program` structure.
    // TODO: @LesterEvSe, consider processing more than one error at a time
    fn build_program(&self, order: &Vec<usize>) -> Result<Program, String> {
        let mut items: Vec<parse::Item> = Vec::new();
        let mut resolutions: Vec<FileResolutions> = vec![BTreeMap::new(); order.len()];

        for &file_id in order {
            let program_items = self.modules[file_id].parsed_program.items();

            for elem in program_items {
                match elem {
                    parse::Item::Use(use_decl) => {
                        let full_path = get_full_path(&self.config, use_decl)?;
                        let source_full_path = SourceName::Real(full_path);
                        let ind = self.lookup[&source_full_path];
                        let visibility = use_decl.visibility();

                        let use_targets = match use_decl.items() {
                            parse::UseItems::Single(elem) => std::slice::from_ref(elem),
                            parse::UseItems::List(elems) => elems.as_slice(),
                        };

                        for target in use_targets {
                            ProjectGraph::process_use_item(
                                &mut resolutions,
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
                            &mut resolutions,
                            file_id,
                            elem,
                            alias.name().clone().into(),
                            alias.visibility(),
                        );
                    }
                    parse::Item::Function(function) => {
                        Self::register_def(
                            &mut items,
                            &mut resolutions,
                            file_id,
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
            paths: self.paths.clone(),
            resolutions: resolutions.into(),
            span: *self.modules[0].parsed_program.as_ref(),
        })
    }

    /// Resolves the final compilation order and builds the `Program`.
    pub fn resolve_complication_order(&self) -> Result<Program, String> {
        // TODO: @LesterEvSe, resolve errors more appropriately
        let mut order = self.c3_linearize().unwrap();
        order.reverse();
        self.build_program(&order)
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // 1. Print the actual program code first
        for item in self.items.iter() {
            writeln!(f, "{item}")?;
        }

        // 2. Open the Resolution Table block
        writeln!(f, "\n/* --- RESOLUTION TABLE ---")?;

        // 3. Logic: Empty vs Populated
        if self.resolutions.is_empty() {
            writeln!(f, "             EMPTY")?;
        } else {
            for (file_id, scope) in self.resolutions.iter().enumerate() {
                if scope.is_empty() {
                    writeln!(f, "   File ID {}: (No resolutions)", file_id)?;
                    continue;
                }

                writeln!(f, "   File ID {}:", file_id)?;

                for (ident, resolution) in scope {
                    writeln!(f, "     {}: {:?}", ident, resolution)?;
                }
            }
        }

        // 4. Close the block (This runs for both empty and non-empty cases)
        writeln!(f, "*/")?;

        Ok(())
    }
}

impl AsRef<Span> for Program {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}
