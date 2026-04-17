use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use crate::driver::DependencyGraph;
use crate::error::{Error, ErrorCollector, RichError, Span};
use crate::impl_eq_hash;
use crate::parse::{self, AliasedSymbolName, Visibility};
use crate::str::{AliasName, FunctionName, SymbolName};

/// The final, flattened representation of a SimplicityHL program.
///
/// This struct holds the fully resolved sequence of items, paths, and scope
/// resolutions, ready to be passed to the next stage of the compiler.
#[derive(Clone, Debug)]
pub struct Program {
    /// The linear sequence of compiled items (`Functions`, `TypeAliases`, etc.).
    items: Arc<[parse::Item]>,

    /// Contains all resolved aliases for the local scopes and the global import registry.
    aliases: SymbolTable<AliasName>,

    /// Contains all resolved functions for the local scopes and the global import registry.
    functions: SymbolTable<FunctionName>,

    span: Span,
}

impl Program {
    pub fn items(&self) -> &[parse::Item] {
        &self.items
    }

    pub fn aliases(&self) -> &SymbolTable<AliasName> {
        &self.aliases
    }

    pub fn functions(&self) -> &SymbolTable<FunctionName> {
        &self.functions
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(Program; items, aliases, functions);

/// Holds all scoping and import data for a specific namespace (e.g., Functions or Aliases).
#[derive(Clone, Debug)]
pub struct SymbolTable<T> {
    /// The items available in each file's local scope.
    /// The index of the array corresponds to the file ID.
    local_scopes: Arc<[BTreeSet<T>]>,

    /// The cross-file import mappings and cached roots.
    imports: ImportRegistry<T>,
}

impl<T> SymbolTable<T> {
    pub fn local_scopes(&self) -> &[BTreeSet<T>] {
        &self.local_scopes
    }

    pub fn imports(&self) -> &ImportRegistry<T> {
        &self.imports
    }
}

impl_eq_hash!(SymbolTable<T>; local_scopes, imports);

/// Represents an item name alongside its originating file ID.
pub type FileScoped<T> = (T, usize);

/// A registry mapping an alias [`FileScoped<T>`] to its target item across different files.
///
/// We use a type alias here to provide a convenient abstraction for the `AST::analyze`
/// phase, making it easier to modify the underlying structure in the future if needed.
pub type ImportMap<T> = BTreeMap<FileScoped<T>, FileScoped<T>>;

/// Manages the resolution of import aliases across the entire program.
#[derive(Clone, Debug, Default)]
pub struct ImportRegistry<T> {
    direct_targets: ImportMap<T>,
    resolved_roots: ImportMap<T>,
}

impl<T> ImportRegistry<T> {
    pub fn direct_targets(&self) -> &ImportMap<T> {
        &self.direct_targets
    }

    pub fn resolved_roots(&self) -> &ImportMap<T> {
        &self.resolved_roots
    }
}

impl_eq_hash!(ImportRegistry<T>; direct_targets, resolved_roots);

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

        let mut aliases = NamespaceTracker::<AliasName>::new(self.modules.len());
        let mut functions = NamespaceTracker::<FunctionName>::new(self.modules.len());

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
                        let alias_err = Self::process_use_item(
                            &mut aliases,
                            source_id,
                            ind,
                            aliased_item,
                            use_decl,
                        );

                        let function_err = Self::process_use_item(
                            &mut functions,
                            source_id,
                            ind,
                            aliased_item,
                            use_decl,
                        );

                        if let Err(err) =
                            Self::resolve_processing_use_items_error(alias_err, function_err)
                        {
                            handler.push(err.with_source(source.clone()));
                        }
                    }
                    continue;
                }

                items.push(elem.clone());

                // Handle Types & Functions by inserting them into their STRICT namespaces
                // Architectural Note:
                // The code may seem duplicated. To prevent this, the best approach
                // would be to add a `NamedItem` trait. However, doing so would require
                // duplicating getter methods for both `Function` and `TypeAlias`.
                // As a result, it is better to leave it as is.
                match elem {
                    parse::Item::TypeAlias(type_alias) => {
                        let name = type_alias.name();
                        let local_id = (name.clone(), source_id);

                        if aliases.memo.contains(&local_id) {
                            handler.push(
                                RichError::new(
                                    Error::RedefinedAlias(name.clone()),
                                    *type_alias.span(),
                                )
                                .with_source(source.clone()),
                            );
                        }
                        aliases.memo.insert(local_id);
                        aliases.resolutions[source_id]
                            .insert(name.clone(), type_alias.visibility().clone());
                    }
                    parse::Item::Function(function) => {
                        let name = function.name();
                        let local_id = (name.clone(), source_id);

                        if functions.memo.contains(&local_id) {
                            handler.push(
                                RichError::new(
                                    Error::FunctionRedefined(name.clone()),
                                    *function.span(),
                                )
                                .with_source(source.clone()),
                            );
                        }
                        functions.memo.insert(local_id);
                        functions.resolutions[source_id]
                            .insert(name.clone(), function.visibility().clone());
                    }

                    // Safe to skip: `Use` items are handled earlier in the loop, and `Module` currently has no functionality.
                    parse::Item::Module | parse::Item::Use(_) => continue,
                }
            }
        }

        (!handler.has_errors()).then(|| Program {
            items: items.into(),
            aliases: aliases.into_symbol_table(),
            functions: functions.into_symbol_table(),
            span: *self.modules[0].parsed_program.as_ref(),
        })
    }

    /// Attempts to pick the most helpful error when an import fails in both namespaces.
    ///
    /// Since SimplicityHL supports separated namespaces, a single `use` statement
    /// may successfully load a `Function`, a `TypeAlias`, or both simultaneously.
    fn resolve_processing_use_items_error(
        alias: Result<(), RichError>,
        function: Result<(), RichError>,
    ) -> Result<(), RichError> {
        match (alias, function) {
            (Ok(()), _) | (_, Ok(())) => Ok(()),

            (Err(err_alias), Err(err_func)) => {
                let alias_is_missing = matches!(err_alias.error(), Error::UnresolvedItem(_));
                let func_is_missing = matches!(err_func.error(), Error::UnresolvedItem(_));

                if !alias_is_missing || func_is_missing {
                    // If it's missing everywhere, OR if the function is missing
                    // but the alias has a specific error (like PrivateItem).
                    Err(err_alias)
                } else {
                    Err(err_func)
                }
            }
        }
    }

    /// Processes a single imported item (or alias) and registers it within a specific namespace.
    ///
    /// This function verifies that the requested item exists in the source module and has the appropriate public
    /// visibility. If validation passes and no local naming collisions are found, the item is registered
    /// in the destination module's local scope and the global import registry.
    ///
    /// # Arguments
    ///
    /// * `namespace` - The generic tracker (e.g., for Functions or Aliases) that holds
    ///   the local file scopes, the global import registry, and the memoization set to prevent collisions.
    /// * `source_id` - The `usize` identifier of the destination module where the item is being imported *to*.
    /// * `ind` - The unique identifier of the source module being imported *from*.
    /// * `aliased_symbol_name` - The specific identifier (and potential alias) being imported from the source.
    /// * `use_decl` - The node of the `use` statement. This dictates the visibility of the new import
    ///   (e.g., `pub use` re-exports the item publicly).
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` on success. Returns `Err(RichError)` if:
    /// * [`Error::UnresolvedItem`]: The target name does not exist in the source module (`ind`).
    /// * [`Error::PrivateItem`]: The target exists, but its visibility is explicitly `Private`.
    /// * [`Error::DuplicateAlias`]: The local name (or alias) has already been used in another import statement.
    /// * [`Error::RedefinedItem`]: The local name conflicts with an existing item already defined in this module.
    fn process_use_item<T>(
        namespace: &mut NamespaceTracker<T>,
        source_id: usize,
        ind: usize,
        (name, alias): &AliasedSymbolName,
        use_decl: &parse::UseDecl,
    ) -> Result<(), RichError>
    where
        T: From<SymbolName> + std::fmt::Display + Clone + Eq + std::hash::Hash + std::cmp::Ord,
    {
        // NOTE: The order of errors is important!
        let span = *use_decl.span();

        // 1. Convert the unresolved SymbolName into our strict type T
        let target_name: T = name.clone().into();
        let orig_id = (target_name.clone(), ind);

        // 2. Verify Existence using T
        let visibility = namespace.resolutions[ind]
            .get(&target_name)
            .ok_or_else(|| RichError::new(Error::UnresolvedItem(name.to_string()), span))?;

        // 3. Verify Visibility
        if matches!(visibility, parse::Visibility::Private) {
            return Err(RichError::new(Error::PrivateItem(name.to_string()), span));
        }

        // 4. Determine the local name and ID up front
        // We figure out the raw symbol first, so we can use it for error messages
        let local_symbol = alias.as_ref().unwrap_or(name);

        // Then convert that raw symbol to T
        let local_name: T = local_symbol.clone().into();
        let local_id = (local_name.clone(), source_id);

        // 5. Check for collisions using `namespace` fields
        if namespace.registry.direct_targets.contains_key(&local_id) {
            return Err(RichError::new(
                Error::DuplicateAlias(local_symbol.to_string()),
                span,
            ));
        }

        if namespace.memo.contains(&local_id) {
            return Err(RichError::new(
                Error::RedefinedItem(local_symbol.to_string()),
                span,
            ));
        }
        namespace.memo.insert(local_id.clone());

        // 6. Update the registers
        namespace
            .registry
            .direct_targets
            .insert(local_id.clone(), orig_id.clone());

        // 7. Find the true root
        let true_root = namespace
            .registry
            .resolved_roots
            .get(&orig_id)
            .cloned()
            .unwrap_or_else(|| orig_id.clone());

        namespace
            .registry
            .resolved_roots
            .insert(local_id, true_root);

        // 8. Register the item in the local module's namespace
        namespace.resolutions[source_id].insert(local_name, use_decl.visibility().clone());
        Ok(())
    }
}

/// Helper struct, that tracks the resolution state, imports, and memoization for a single namespace.
#[derive(Clone, Debug)]
struct NamespaceTracker<T> {
    /// Local resolutions per file.
    resolutions: Vec<HashMap<T, Visibility>>,

    /// Global registry for `use` imports and aliasing.
    registry: ImportRegistry<T>,

    /// Tracks processed items to prevent infinite loops or redefinitions.
    memo: BTreeSet<FileScoped<T>>,
}

impl<T: Ord + Clone + Default + std::hash::Hash> NamespaceTracker<T> {
    pub fn new(module_count: usize) -> Self {
        Self {
            resolutions: vec![HashMap::new(); module_count],
            registry: ImportRegistry::<T>::default(),
            memo: BTreeSet::new(),
        }
    }

    pub fn into_symbol_table(self) -> SymbolTable<T> {
        SymbolTable {
            local_scopes: self
                .resolutions
                .into_iter()
                .map(|map| map.into_keys().collect::<BTreeSet<_>>())
                .collect::<Vec<_>>()
                .into(),
            imports: self.registry,
        }
    }
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
        let resolutions = &program.functions.local_scopes[root_id];

        resolutions
            .get(&FunctionName::from_str_unchecked("private_fn"))
            .expect("private_fn missing");

        resolutions
            .get(&FunctionName::from_str_unchecked("public_fn"))
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
        program.functions.local_scopes[id_b]
            .get(&FunctionName::from_str_unchecked("foo"))
            .expect("foo missing in B");

        // Check Root's scope
        program.functions.local_scopes[id_root]
            .get(&FunctionName::from_str_unchecked("foo"))
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

    #[test]
    fn test_separated_type_aliases_and_functions() {
        let (graph, ids, _dir) = setup_graph(vec![
            ("libs/lib/A.simf", "pub type bar = u32; pub fn bar() {}"),
            ("main.simf", "use lib::A::bar;"),
        ]);

        let mut error_handler = ErrorCollector::new();
        let program_option = graph.linearize_and_build(&mut error_handler).unwrap();

        let Some(program) = program_option else {
            panic!("{}", error_handler);
        };

        let root_id = ids["main"];

        // Check B's scope
        program.functions.local_scopes[root_id]
            .get(&FunctionName::from_str_unchecked("bar"))
            .expect("Function bar missing in main");

        // Check Root's scope
        program.aliases.local_scopes[root_id]
            .get(&AliasName::from_str_unchecked("bar"))
            .expect("Type alias missing in main");
    }

    #[test]
    fn test_private_alias_error_does_not_mask_duplicate_function_import() {
        // Scenario:
        // main.simf: load function `foo` from A.simf.
        // Then try to load both `fn foo` and `type foo`.
        // However, we have already loade `fn foo` and `type foo` is private, so an error occurs.
        let (graph, _ids, _dir) = setup_graph(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("libs/lib/B.simf", "pub fn foo() {} type foo = u32;"),
            ("main.simf", "use lib::A::foo; use lib::B::foo;"),
        ]);

        let mut error_handler = ErrorCollector::new();
        let program_option = graph.linearize_and_build(&mut error_handler).unwrap();
        let _errors = error_handler.to_string();

        assert!(
            program_option.is_none(),
            "build should fail when a second import reuses the function name `foo`"
        );
    }
}

#[cfg(test)]
mod alias_tests {
    use super::*;
    use crate::driver::tests::setup_graph;

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
        let scope = &program.functions.local_scopes[id_root];

        assert!(
            scope
                .get(&FunctionName::from_str_unchecked("foo"))
                .is_none(),
            "Original name 'foo' should not be in scope"
        );
        assert!(
            scope
                .get(&FunctionName::from_str_unchecked("bar"))
                .is_some(),
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
        let scope = &program.functions.local_scopes[id_root];

        // The original names should NOT be in scope
        assert!(scope
            .get(&FunctionName::from_str_unchecked("foo"))
            .is_none());
        assert!(scope
            .get(&FunctionName::from_str_unchecked("baz"))
            .is_none());

        // The aliases MUST be in scope
        assert!(scope
            .get(&FunctionName::from_str_unchecked("bar"))
            .is_some());
        assert!(scope
            .get(&FunctionName::from_str_unchecked("qux"))
            .is_some());
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
        let main_scope = &program.functions.local_scopes[id_root];
        assert!(main_scope
            .get(&FunctionName::from_str_unchecked("original"))
            .is_none());
        assert!(main_scope
            .get(&FunctionName::from_str_unchecked("middle"))
            .is_none());
        assert!(
            main_scope
                .get(&FunctionName::from_str_unchecked("final_name"))
                .is_some(),
            "Main must see the final alias"
        );

        // Assert B Scope (It should have the intermediate alias!)
        let b_scope = &program.functions.local_scopes[id_b];
        assert!(
            b_scope
                .get(&FunctionName::from_str_unchecked("middle"))
                .is_some(),
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
    fn test_local_function_cannot_reuse_alias_name() {
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
                .contains("Function `foo` was defined multiple times"),
            "expected a redefined-item diagnostic"
        );
    }

    #[test]
    fn test_local_type_alias_cannot_reuse_alias_name() {
        let (graph, _ids, _dir) = setup_graph(vec![
            ("libs/lib/A.simf", "pub type bar = u32;"),
            ("main.simf", "use lib::A::bar as foo; type foo = u64;"),
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
                .contains("Type alias `foo` was defined multiple times"),
            "expected a redefined-item diagnostic"
        );
    }
}
