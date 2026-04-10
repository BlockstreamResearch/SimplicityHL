use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use crate::driver::DependencyGraph;
use crate::error::{Error, ErrorCollector, RichError, Span};
use crate::impl_eq_hash;
use crate::parse::{self, AliasedIdentifier, Visibility};
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

    import_aliases: AliasRegistry,

    span: Span,
}

impl Program {
    pub fn items(&self) -> &[parse::Item] {
        &self.items
    }

    pub fn files(&self) -> &[ResolvedFile] {
        &self.files
    }

    pub fn import_aliases(&self) -> &AliasRegistry {
        &self.import_aliases
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(Program; items, files, import_aliases);

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

/// A registry mapping an alias [`ItemNameWithFileId`] to its target item across different files.
///
/// We use a type alias here to provide a convenient abstraction for the `AST::analyze`
/// phase, making it easier to modify the underlying structure in the future if needed.
pub type AliasMap = BTreeMap<ItemNameWithFileId, ItemNameWithFileId>;
pub type ItemNameWithFileId = (Arc<str>, usize);

/// Manages the resolution of import aliases across the entire program.
#[derive(Clone, Debug, Default)]
pub struct AliasRegistry {
    /// Maps an alias to its immediate target.
    /// (e.g., `use B as C;` stores C -> B)
    direct_targets: AliasMap,

    /// Caches the final, original definition of an alias to avoid walking the chain.
    /// (e.g., If C -> B and B -> A, this stores C -> A)
    resolved_roots: AliasMap,
}

impl AliasRegistry {
    pub fn direct_targets(&self) -> &AliasMap {
        &self.direct_targets
    }

    pub fn resolved_roots(&self) -> &AliasMap {
        &self.resolved_roots
    }
}

impl_eq_hash!(AliasRegistry; direct_targets, resolved_roots);

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
        let mut import_aliases = AliasRegistry::default();
        let mut items_registry = BTreeSet::<ItemNameWithFileId>::new();

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

                    for aliased_item in use_decl_items {
                        if let Err(err) = Self::process_use_item(
                            &mut items_registry,
                            &mut import_aliases,
                            &mut resolutions,
                            source_id,
                            ind,
                            aliased_item,
                            use_decl,
                        ) {
                            handler.push(err.with_source(source.clone()));
                        }
                    }
                    continue;
                }

                // Handle Types & Functions
                let (name, vis, span) = match elem {
                    parse::Item::TypeAlias(a) => (a.name().as_inner(), a.visibility(), *a.span()),
                    parse::Item::Function(f) => (f.name().as_inner(), f.visibility(), *f.span()),

                    // Safe to skip: `Use` items are handled earlier in the loop, and `Module` currently has no functionality.
                    parse::Item::Module | parse::Item::Use(_) => continue,
                };

                let item_name = (Arc::from(name), source_id);
                if items_registry.contains(&item_name) {
                    handler.push(
                        RichError::new(Error::RedefinedItem(name.to_string()), span)
                            .with_source(source.clone()),
                    );
                }
                items_registry.insert(item_name);

                items.push(elem.clone());
                resolutions[source_id].insert(Arc::from(name), vis.clone());
            }
        }

        (!handler.has_errors()).then(|| Program {
            items: items.into(),
            files: construct_resolved_file_array(&self.paths, &resolutions),
            import_aliases,
            span: *self.modules[0].parsed_program.as_ref(),
        })
    }

    /// Processes a single imported item (or alias) during the module resolution phase.
    ///
    /// This function verifies that the requested item exists in the source module and
    /// that it has the appropriate public visibility to be imported. If validation passes,
    /// the item is registered in the importing module's resolution table and global alias registry.
    ///
    /// # Arguments
    ///
    /// * `import_aliases` - The global registry tracking alias chains and their canonical roots.
    /// * `resolutions` - The global, mutable array mapping each `file_id` to its localized `FileResolutions` table.
    /// * `source_id` - The `usize` identifier of the destination source.
    /// * `ind` - The unique identifier of the source module being imported *from*.
    /// * `aliased_identifier` - The specific identifier (and potential alias) being imported from the source.
    /// * `use_decl` - The node of the `use` statement. This dictates the visibility of the new import
    ///   (e.g., `pub use` re-exports the item publicly).
    ///
    /// # Returns
    ///
    /// Returns `None` on success. Returns `Some(RichError)` if:
    /// * [`Error::UnresolvedItem`]: The target `elem` does not exist in the source module (`ind`).
    /// * [`Error::PrivateItem`]: The target exists, but its visibility is explicitly `Private`,
    /// * [`Error::DuplicateAlias`]: The target `alias` (or imported name) has already been used in the current module.
    fn process_use_item(
        items_registry: &mut BTreeSet<ItemNameWithFileId>,
        import_aliases: &mut AliasRegistry,
        resolutions: &mut [HashMap<Arc<str>, Visibility>],
        source_id: usize,
        ind: usize,
        (name, alias): &AliasedIdentifier,
        use_decl: &parse::UseDecl,
    ) -> Result<(), RichError> {
        // NOTE: The order of errors is important!
        let span = *use_decl.span();

        let name: Arc<str> = Arc::from(name.as_inner());
        let orig_id = (name.clone(), ind);

        // 1. Verify Existence: Does the item exist in the source file?
        let visibility = resolutions[ind]
            .get(&name)
            .ok_or_else(|| RichError::new(Error::UnresolvedItem(name.to_string()), span))?;

        // 2. Verify Visibility: Are we allowed to see it?
        if matches!(visibility, parse::Visibility::Private) {
            return Err(RichError::new(Error::PrivateItem(name.to_string()), span));
        }

        // 3. Determine the local name and ID up front
        let local_name = if let Some(alias) = alias {
            Arc::from(alias.as_inner())
        } else {
            name.clone()
        };
        let local_id = (local_name.clone(), source_id);

        // 4. Check for collisions
        if import_aliases.direct_targets.contains_key(&local_id) {
            return Err(RichError::new(
                Error::DuplicateAlias(local_name.to_string()),
                span,
            ));
        }

        if items_registry.contains(&local_id) {
            return Err(RichError::new(
                Error::RedefinedItem(local_name.to_string()),
                span,
            ));
        }
        items_registry.insert(local_id.clone());

        // 5. Update the registers
        import_aliases
            .direct_targets
            .insert(local_id.clone(), orig_id.clone());

        // 6. Find the true root using a single lookup!
        // If `orig_id` exists in resolved_roots, it means it's an alias and we get its true root.
        // If it returns None, it means `orig_id` is the original item, so it IS the root.
        let true_root = import_aliases
            .resolved_roots
            .get(&orig_id)
            .cloned()
            .unwrap_or_else(|| orig_id.clone());

        // Always cache the final root for instant O(1) lookups later
        import_aliases.resolved_roots.insert(local_id, true_root);

        // 7. Register the item in the local  module's namespace
        resolutions[source_id].insert(local_name, use_decl.visibility().clone());
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
mod resolve_order_tests {
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

#[cfg(test)]
mod alias_tests {
    use super::*;
    use crate::driver::tests::setup_graph;
    use std::sync::Arc;

    #[test]
    fn test_renaming_with_use() {
        // Scenario: Renaming imports.
        // main.simf: use lib::A::foo as bar;
        // Expected: Scope should contain "bar", but not "foo".

        let (graph, ids, _dir) = setup_graph(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("main.simf", "use lib::A::foo as bar;"),
        ]);

        let mut error_handler = ErrorCollector::new();
        let program_option = graph.linearize_and_build(&mut error_handler).unwrap();

        let Some(program) = program_option else {
            panic!("{}", error_handler);
        };

        let id_root = ids["main"];
        let scope = &program.files[id_root].resolutions;

        assert!(
            scope.get(&Arc::from("foo")).is_none(),
            "Original name 'foo' should not be in scope"
        );
        assert!(
            scope.get(&Arc::from("bar")).is_some(),
            "Alias 'bar' should be in scope"
        );
    }

    #[test]
    fn test_multiple_aliases_in_list() {
        // Scenario: Renaming multiple imports inside brackets.
        let (graph, ids, _dir) = setup_graph(vec![
            ("libs/lib/A.simf", "pub fn foo() {} pub fn baz() {}"),
            ("main.simf", "use lib::A::{foo as bar, baz as qux};"),
        ]);

        let mut error_handler = ErrorCollector::new();
        let program_option = graph.linearize_and_build(&mut error_handler).unwrap();

        let Some(program) = program_option else {
            panic!("{}", error_handler);
        };

        let id_root = ids["main"];
        let scope = &program.files[id_root].resolutions;

        // The original names should NOT be in scope
        assert!(scope.get(&Arc::from("foo")).is_none());
        assert!(scope.get(&Arc::from("baz")).is_none());

        // The aliases MUST be in scope
        assert!(scope.get(&Arc::from("bar")).is_some());
        assert!(scope.get(&Arc::from("qux")).is_some());
    }

    #[test]
    fn test_alias_private_item_fails() {
        // Scenario: Attempting to alias a private item should fail.
        let (graph, _ids, _dir) = setup_graph(vec![
            ("libs/lib/A.simf", "fn secret() {}"), // Note: Missing `pub`
            ("main.simf", "use lib::A::secret as my_secret;"),
        ]);

        let mut error_handler = ErrorCollector::new();
        let program_option = graph.linearize_and_build(&mut error_handler).unwrap();

        assert!(
            program_option.is_none(),
            "Compiler should emit an error and return None when aliasing a private item"
        );

        assert!(
            error_handler
                .to_string()
                .contains("Item `secret` is private"),
            "Error should mention the private item restriction"
        );
    }

    #[test]
    fn test_deep_reexport_with_aliases() {
        // Scenario: Chaining aliases across multiple files.
        let (graph, ids, _dir) = setup_graph(vec![
            ("libs/lib/A.simf", "pub fn original() {}"),
            ("libs/lib/B.simf", "pub use lib::A::original as middle;"),
            ("main.simf", "use lib::B::middle as final_name;"),
        ]);

        let mut error_handler = ErrorCollector::new();
        let program_option = graph.linearize_and_build(&mut error_handler).unwrap();

        let Some(program) = program_option else {
            panic!("{}", error_handler);
        };

        let id_b = ids["B"];
        let id_root = ids["main"];

        // Assert Main Scope
        let main_scope = &program.files[id_root].resolutions;
        assert!(main_scope.get(&Arc::from("original")).is_none());
        assert!(main_scope.get(&Arc::from("middle")).is_none());
        assert!(
            main_scope.get(&Arc::from("final_name")).is_some(),
            "Main must see the final alias"
        );

        // Assert B Scope (It should have the intermediate alias!)
        let b_scope = &program.files[id_b].resolutions;
        assert!(
            b_scope.get(&Arc::from("middle")).is_some(),
            "File B must contain its own public alias"
        );
    }

    #[test]
    fn test_deep_reexport_private_link_fails() {
        // Scenario: Main tries to import an alias from B, but B's alias is private!
        let (graph, _ids, _dir) = setup_graph(vec![
            ("libs/lib/A.simf", "pub fn target() {}"),
            // Note: Missing `pub` keyword here! This makes `hidden_alias` private to B.
            ("libs/lib/B.simf", "use lib::A::target as hidden_alias;"),
            ("main.simf", "use lib::B::hidden_alias;"),
        ]);

        let mut error_handler = ErrorCollector::new();
        let program_option = graph.linearize_and_build(&mut error_handler).unwrap();

        assert!(
            program_option.is_none(),
            "Compiler must return None when trying to import a private alias from an intermediate module"
        );

        assert!(
            error_handler
                .to_string()
                .contains("Item `hidden_alias` is private"),
            "Error should correctly identify the private intermediate alias"
        );
    }

    #[test]
    fn test_alias_cycle_detection() {
        // Scenario: A malicious or confused user creates an infinite alias/import loop.
        let (graph, _ids, _dir) = setup_graph(vec![
            // A imports from B, B imports from A. This creates a file-level cycle!
            ("libs/lib/A.simf", "pub use lib::B::pong as ping;"),
            ("libs/lib/B.simf", "pub use lib::A::ping as pong;"),
            ("main.simf", "use lib::A::ping;"),
        ]);

        let mut error_handler = ErrorCollector::new();

        // Because A and B depend on each other, `linearize()` should catch the cycle
        // and return an Err(...) directly, rather than causing a Stack Overflow.
        let result = graph.linearize_and_build(&mut error_handler);

        match result {
            Err(e) => {
                println!("{e}");
                assert!(
                    e.contains("Cycle") || e.contains("Circular"),
                    "DFS Linearizer must catch infinite alias cycles"
                );
            }
            Ok(None) => {
                assert!(
                    error_handler.has_errors(),
                    "If linearization passes, the builder must catch the cycle"
                );
            }
            Ok(Some(_)) => {
                panic!("Expected compilation to fail due to a dependency cycle, but it succeeded!")
            }
        }
    }

    #[test]
    fn test_plain_import_and_alias_to_same_name_is_rejected() {
        let (graph, _ids, _dir) = setup_graph(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("libs/lib/B.simf", "pub fn foo() {}"),
            ("main.simf", "use lib::A::foo; use lib::B::foo as foo;"),
        ]);

        let mut error_handler = ErrorCollector::new();
        let program_option = graph.linearize_and_build(&mut error_handler).unwrap();

        assert!(
            program_option.is_none(),
            "build should fail when two imports bind the same local name"
        );
        assert!(
            error_handler
                .to_string()
                .contains("The alias `foo` was defined multiple times"),
            "expected a duplicate-alias diagnostic"
        );
    }

    #[test]
    fn test_failed_alias_import_does_not_poison_following_imports() {
        let (graph, _ids, _dir) = setup_graph(vec![
            ("libs/lib/A.simf", "pub fn nope() {}"),
            ("libs/lib/B.simf", "pub fn bar() {}"),
            (
                "main.simf",
                "use lib::A::missing as foo; use lib::B::bar as foo;",
            ),
        ]);

        let mut error_handler = ErrorCollector::new();
        let program_option = graph.linearize_and_build(&mut error_handler).unwrap();
        let errors = error_handler.to_string();

        assert!(
            program_option.is_none(),
            "build should fail on the unresolved import"
        );
        assert!(errors.contains("Item `missing` could not be found"));
        assert!(
            !errors.contains("The alias `foo` was defined multiple times"),
            "a failed import must not reserve the alias name"
        );
    }

    #[test]
    fn test_alias_cannot_reuse_local_definition_name() {
        let (graph, _ids, _dir) = setup_graph(vec![
            ("libs/lib/A.simf", "pub fn bar() {}"),
            ("main.simf", "pub fn foo() {} use lib::A::bar as foo;"),
        ]);

        let mut error_handler = ErrorCollector::new();
        let program_option = graph.linearize_and_build(&mut error_handler).unwrap();

        dbg!(&error_handler.to_string());

        assert!(
            program_option.is_none(),
            "build should fail when an alias reuses a local definition name"
        );
        assert!(
            error_handler
                .to_string()
                .contains("Item `foo` was defined multiple times"),
            "expected a redefined-item diagnostic"
        );
    }

    #[test]
    fn test_local_definition_cannot_reuse_alias_name() {
        let (graph, _ids, _dir) = setup_graph(vec![
            ("libs/lib/A.simf", "pub fn bar() {}"),
            ("main.simf", "use lib::A::bar as foo; pub fn foo() {}"),
        ]);

        let mut error_handler = ErrorCollector::new();
        let program_option = graph.linearize_and_build(&mut error_handler).unwrap();

        assert!(
            program_option.is_none(),
            "build should fail when a local definition reuses an alias name"
        );
        assert!(
            error_handler
                .to_string()
                .contains("Item `foo` was defined multiple times"),
            "expected a redefined-item diagnostic"
        );
    }
}
