use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

use crate::driver::DependencyGraph;
use crate::error::{Error, ErrorCollector, RichError, Span};
use crate::impl_eq_hash;
use crate::parse::{self, Visibility};
use crate::resolution::CanonPath;

/// The final, flattened representation of a SimplicityHL program.
///
/// This struct holds the fully resolved sequence of items, paths, and scope
/// resolutions, ready to be passed to the next stage of the compiler.
#[derive(Clone, Debug)]
pub struct Program {
    /// The linear sequence of compiled items (`Functions`, `TypeAliases`, etc.).
    items: Arc<[parse::Item]>,

    /// The files that make up this program, along with their scoping rules.
    files: Arc<[ResolvedFile]>,

    span: Span,
}

impl Program {
    pub fn items(&self) -> &[parse::Item] {
        &self.items
    }

    pub fn files(&self) -> &[ResolvedFile] {
        &self.files
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(Program; items, files);

/// Represents a single source file alongside its resolved scoping and visibility rules.
#[derive(Clone, Debug)]
pub struct ResolvedFile {
    path: CanonPath,

    /// The set of resolved item names available within this file's scope.
    // Use BTreeSet instead of HashMap for the impl_eq_hash! macro.
    resolutions: BTreeSet<Arc<str>>,
}

impl ResolvedFile {
    pub fn path(&self) -> &CanonPath {
        &self.path
    }

    pub fn resolutions(&self) -> &BTreeSet<Arc<str>> {
        &self.resolutions
    }
}

impl_eq_hash!(ResolvedFile; path, resolutions);

/// This is a core component of the [`DependencyGraph`].
impl DependencyGraph {
    /// Resolves the dependency graph and constructs the final AST program.
    pub fn linearize_and_build(
        &self,
        handler: &mut ErrorCollector,
    ) -> Result<Option<Program>, String> {
        match self.linearize() {
            Ok(order) => Ok(self.build_program(&order, handler)),
            Err(err) => Err(err.to_string()),
        }
    }

    /// Constructs the unified AST for the entire program.
    fn build_program(&self, order: &[usize], handler: &mut ErrorCollector) -> Option<Program> {
        let mut items: Vec<parse::Item> = Vec::new();
        let mut resolutions: Vec<HashMap<Arc<str>, Visibility>> =
            vec![HashMap::new(); self.modules.len()];

        for &source_id in order {
            let module = &self.modules[source_id];
            let source = &module.source;

            for elem in module.parsed_program.items() {
                // Handle Uses (Early Continue flattens the nesting)
                if let parse::Item::Use(use_decl) = elem {
                    let resolve_path =
                        match self.dependency_map.resolve_path(source.name(), use_decl) {
                            Ok(path) => path,
                            Err(err) => {
                                handler.push(err.with_source(source.clone()));
                                continue;
                            }
                        };

                    let ind = self.lookup[&resolve_path];
                    let use_decl_items = match use_decl.items() {
                        parse::UseItems::Single(elem) => std::slice::from_ref(elem),
                        parse::UseItems::List(elems) => elems.as_slice(),
                    };

                    for item in use_decl_items {
                        if let Err(err) = Self::process_use_item(
                            &mut resolutions,
                            source_id,
                            ind,
                            Arc::from(item.as_inner()),
                            use_decl,
                        ) {
                            handler.push(err.with_source(source.clone()));
                        }
                    }
                    continue;
                }

                // Handle Types & Functions
                let (name, vis) = match elem {
                    parse::Item::TypeAlias(a) => (a.name().as_inner(), a.visibility()),
                    parse::Item::Function(f) => (f.name().as_inner(), f.visibility()),

                    // Safe to skip: `Use` items are handled earlier in the loop, and `Module` currently has no functionality.
                    parse::Item::Module | parse::Item::Use(_) => continue,
                };

                items.push(elem.clone());
                resolutions[source_id].insert(Arc::from(name), vis.clone());
            }
        }

        (!handler.has_errors()).then(|| Program {
            items: items.into(),
            files: construct_resolved_file_array(&self.paths, &resolutions),
            span: *self.modules[0].parsed_program.as_ref(),
        })
    }

    /// Processes a single imported item during the module resolution phase.
    ///
    /// # Arguments
    ///
    /// * `resolutions` - A mutable slice of hash maps, where each index corresponds to a module's ID and holds its resolved items and their visibilities.
    /// * `source_id` - The `usize` identifier of the destination source.
    /// * `ind` - The unique identifier (`usize`) of the source module being imported *from*.
    /// * `name` - The specific item name (`Arc<str>`) being imported from the source.
    /// * `use_decl` - The AST node of the `use` statement. This dictates the visibility of the newly imported item in the destination module.
    ///
    /// # Returns
    ///
    /// Returns `None` on success. Returns `Some(RichError)` if:
    /// * [`Error::UnresolvedItem`]: The target `name` does not exist in the source module (`ind`).
    /// * [`Error::PrivateItem`]: The target exists in the source module, but its visibility is expl
    fn process_use_item(
        resolutions: &mut [HashMap<Arc<str>, Visibility>],
        source_id: usize,
        ind: usize,
        name: Arc<str>,
        use_decl: &parse::UseDecl,
    ) -> Result<(), RichError> {
        let span = *use_decl.span();

        let visibility = resolutions[ind]
            .get(&name)
            .ok_or_else(|| RichError::new(Error::UnresolvedItem(name.to_string()), span))?;

        if matches!(visibility, parse::Visibility::Private) {
            return Err(RichError::new(Error::PrivateItem(name.to_string()), span));
        }

        resolutions[source_id].insert(name, use_decl.visibility().clone());
        Ok(())
    }
}

fn construct_resolved_file_array(
    paths: &[CanonPath],
    resolutions: &[HashMap<Arc<str>, Visibility>],
) -> Arc<[ResolvedFile]> {
    let mut result = Vec::with_capacity(paths.len());

    for i in 0..paths.len() {
        let file_resolutions: BTreeSet<Arc<str>> = resolutions[i].keys().cloned().collect();

        result.push(ResolvedFile {
            path: paths[i].clone(),
            resolutions: file_resolutions,
        });
    }

    result.into()
}

#[cfg(test)]
mod tests {
    use crate::driver::tests::setup_graph;

    use super::*;

    #[test]
    fn test_local_definitions_visibility() {
        // main.simf defines a private function and a public function.
        // Expected: Both should appear in the scope with correct visibility.

        let (graph, ids, _dir) = setup_graph(vec![(
            "main.simf",
            "fn private_fn() {} pub fn public_fn() {}",
        )]);

        let mut error_handler = ErrorCollector::new();
        let program_option = graph.linearize_and_build(&mut error_handler).unwrap();

        let Some(program) = program_option else {
            panic!("{}", error_handler);
        };

        let root_id = ids["main"];
        let resolutions = &program.files[root_id].resolutions;

        resolutions
            .get(&Arc::from("private_fn"))
            .expect("private_fn missing");

        resolutions
            .get(&Arc::from("public_fn"))
            .expect("public_fn missing");
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

        let mut error_handler = ErrorCollector::new();
        let program_option = graph.linearize_and_build(&mut error_handler).unwrap();

        let Some(program) = program_option else {
            panic!("{}", error_handler);
        };

        let id_b = ids["B"];
        let id_root = ids["main"];

        // Check B's scope
        program.files[id_b]
            .resolutions
            .get(&Arc::from("foo"))
            .expect("foo missing in B");

        // Check Root's scope
        program.files[id_root]
            .resolutions
            .get(&Arc::from("foo"))
            .expect("foo missing in Root");
    }

    #[test]
    fn test_private_import_encapsulation_error() {
        // Scenario: Access violation.
        // 1. A.simf defines `pub fn foo`.
        // 2. B.simf imports it via `use` (Private import).
        // 3. main.simf tries to import `foo` from B.
        // Expected: Error, because B did not re-export foo.

        let (graph, _ids, _dir) = setup_graph(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("libs/lib/B.simf", "use lib::A::foo;"), // <--- Private binding!
            ("main.simf", "use lib::B::foo;"),       // <--- Should fail
        ]);

        let mut error_handler = ErrorCollector::new();
        let program_option = graph.linearize_and_build(&mut error_handler).unwrap();

        assert!(
            program_option.is_none(),
            "Build should fail and return None when importing a private binding"
        );
        assert!(error_handler
            .to_string()
            .contains(&"Item `foo` is private".to_string()));
    }
}
