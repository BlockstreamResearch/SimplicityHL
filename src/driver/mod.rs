#[cfg(test)]
pub mod tests;

use std::collections::{HashMap, VecDeque};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::error::{ErrorCollector, Span};
use crate::parse::{self, ParseFromStrWithErrors, Visibility};
use crate::resolution::LibConfig;
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
    pub config: Arc<LibConfig>,

    /// Fast lookup: File Path -> Module ID.
    /// A reverse index mapping absolute file paths to their internal IDs.
    /// This solves the duplication problem, ensuring each file is only parsed once.
    pub lookup: HashMap<PathBuf, usize>,

    /// Fast lookup: Module ID -> File Path.
    /// A direct index mapping internal IDs back to their absolute file paths.
    /// This serves as the exact inverse of the `lookup` map.
    pub paths: Vec<PathBuf>,

    /// The Adjacency List: Defines the Directed acyclic Graph (DAG) of imports.
    ///
    /// The Key (`usize`) is the ID of a "Parent" module (the file doing the importing).
    /// The Value (`Vec<usize>`) is a list of IDs of the "Child" modules it relies on.
    ///
    /// Example: If `main.simf` (ID: 0) has `use lib::math;` (ID: 1) and `use lib::io;` (ID: 2),
    /// this map will contain: `{ 0: [1, 2] }`.
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

    // TODO: @LesterEvSe, consider processing more than one error at a time
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
        // TODO: @LesterEvSe, resolve errors more appropriately
        let mut order = self.c3_linearize().unwrap();
        order.reverse();
        self.build_program(&order)
    }
}
