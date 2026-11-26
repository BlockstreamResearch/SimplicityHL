use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::ast::CustomFunction;
use crate::driver::{CRATE_STR, MAIN_STR};
use crate::error::Error;
use crate::parse::{self, UseDecl, Visibility};
use crate::str::{AliasName, FunctionName, Identifier, ModuleName, SymbolName};
use crate::types::{AliasedType, EnumInfo, EnumVariantInfo, ResolvedType};

/// A single module namespace. Handles arbitrary nesting via `submodules`.
#[derive(Clone, Debug, Eq, PartialEq, Default)]
struct ModuleScope {
    aliases: HashMap<AliasName, (ResolvedType, Visibility)>,
    functions: HashMap<FunctionName, (CustomFunction, Visibility)>,
    /// Nested inling `mod` blocks, each becoming a child scope.
    submodules: HashMap<ModuleName, (ModuleScope, Visibility)>,
    /// Names of failed imports, whose uses are not reported again.
    poisoned: HashSet<SymbolName>,
}

/// The modules of the program and the current position inside them.
#[derive(Default)]
pub(super) struct ModuleTree {
    /// Current position in the module tree. Push on `mod` enter, pop on exit.
    /// Empty path means we are at the root (main file) scope.
    path: Vec<ModuleName>,

    /// Global scope where items from the main file that live at the root level.
    root: ModuleScope,
}

impl ModuleTree {
    pub(super) fn path(&self) -> &[ModuleName] {
        &self.path
    }

    /// Enter a named module, pushing it onto the module path.
    ///
    /// ## Errors
    ///
    /// * [`Error::ModuleRedefined`] A module with this name is already defined in the current scope.
    pub(super) fn enter(&mut self, name: ModuleName, visibility: Visibility) -> Result<(), Error> {
        let current = self.current_mut();
        if current.submodules.contains_key(&name) {
            return Err(Error::ModuleRedefined { name });
        }

        current
            .submodules
            .insert(name.clone(), (ModuleScope::default(), visibility));
        self.path.push(name);
        Ok(())
    }

    /// Exit the current module, popping it from the module path.
    ///
    /// ## Panics
    ///
    /// Not inside any module.
    pub(super) fn exit(&mut self) {
        self.path.pop().expect("Not inside any module");
    }

    /// This allows us to perform read-only checks (like redefinitions) and
    /// call `resolve` without taking a premature mutable borrow of `self`.
    fn current(&self) -> &ModuleScope {
        self.path.iter().fold(&self.root, |scope, segment| {
            &scope.submodules.get(segment).expect("Module not found").0
        })
    }

    /// We use iterations and `O(N)` algorithm, because nested block are not so deep.
    /// It will be strange to see 100 nested blocks, so common `.fold()` will be enough for that.
    fn current_mut(&mut self) -> &mut ModuleScope {
        self.path.iter().fold(&mut self.root, |scope, segment| {
            &mut scope
                .submodules
                .get_mut(segment)
                .expect("Module not found")
                .0
        })
    }

    /// Retrieves the resolved type of a type alias in the current module scope.
    ///
    /// ## Errors
    ///
    /// * [`Error::UndefinedAlias`]: The alias is not defined in the current scope.
    pub(super) fn get_alias(&self, name: &AliasName) -> Result<ResolvedType, Error> {
        let current = self.current();

        match current.aliases.get(name) {
            Some((ty, _)) => Ok(ty.clone()),
            None if current.poisoned.contains(name.as_str()) => Ok(ResolvedType::never()),
            None => Err(Error::UndefinedAlias { name: name.clone() }),
        }
    }

    /// Check whether `name` comes from a failed import in the current module.
    pub(super) fn is_poisoned(&self, name: &str) -> bool {
        self.current().poisoned.contains(name)
    }

    /// Resolve a type with aliases to a type without aliases.
    ///
    /// ## Errors
    ///
    /// * [`Error::UndefinedAlias`]: The alias is not found in the global registry.
    pub(super) fn resolve(&self, ty: &AliasedType) -> Result<ResolvedType, Error> {
        ty.resolve(|name| self.get_alias(name))
    }

    /// Error if `name` is already defined as an alias in the current module.
    pub(super) fn check_alias_free(&self, name: &AliasName) -> Result<(), Error> {
        if self.current().aliases.contains_key(name) {
            return Err(Error::RedefinedAlias { name: name.clone() });
        }

        Ok(())
    }

    /// Insert a type alias into the current module scope.
    ///
    /// The caller checks [`Self::check_alias_free`] first, before resolving the aliased type.
    pub(super) fn insert_alias(
        &mut self,
        name: AliasName,
        ty: ResolvedType,
        visibility: Visibility,
    ) {
        self.current_mut().aliases.insert(name, (ty, visibility));
    }

    /// Insert an enum declaration into the current module.
    ///
    /// An enum is a type alias for a nominal enum type, so its name resolves as a type
    /// and its identity travels wherever the alias is imported.
    ///
    /// Enums may only be declared at the top level of the program's own files
    /// (the parser rejects declarations inside `mod` blocks, the driver rejects them in dependency files),
    /// so the bare name is unique program-wide and identifies the enum in the ABI.
    ///
    /// ## Errors
    ///
    /// * [`Error::RedefinedAlias`]: The name is already defined in the current module.
    pub(super) fn insert_enum(
        &mut self,
        name: AliasName,
        visibility: Visibility,
        variants: Arc<[EnumVariantInfo]>,
    ) -> Result<(), Error> {
        self.check_alias_free(&name)?;

        let info = EnumInfo::new(Arc::clone(name.as_inner()), variants);
        let resolved = ResolvedType::enumeration(info);

        self.current_mut()
            .aliases
            .insert(name, (resolved, visibility));

        Ok(())
    }

    /// Insert a custom function into the global map.
    ///
    /// ## Errors
    ///
    /// * [`Error::FunctionRedefined`] The function has already been defined.
    pub(super) fn insert_function(
        &mut self,
        name: FunctionName,
        visibility: Visibility,
        function: CustomFunction,
    ) -> Result<(), Error> {
        if self.current().functions.contains_key(&name) {
            return Err(Error::FunctionRedefined { name });
        }

        self.current_mut()
            .functions
            .insert(name, (function, visibility));
        Ok(())
    }

    /// Retrieves the definition of a custom function, enforcing strict error prioritization.
    ///
    /// ## Errors
    ///
    /// * [`Error::FunctionUndefined`]: The function is not found in the global registry.
    pub(super) fn get_function(&self, name: &FunctionName) -> Result<CustomFunction, Error> {
        self.current()
            .functions
            .get(name)
            .map(|(func, _)| func.clone())
            .ok_or_else(|| Error::FunctionUndefined { name: name.clone() })
    }
}

impl ModuleTree {
    // TODO: Consider to optimize it (we definitely can do it)
    /// Resolves a `use` declaration by navigating the module tree, checking visibility,
    /// and importing matching items into the current scope.
    ///
    /// Returns every error instead of stopping at the first one.
    ///
    /// ## Errors
    ///
    /// * [`Error::MissingCrateKeyword`] The import path does not start with the `crate` keyword.
    /// * [`Error::ModuleNotFound`] A module segment in the target path does not exist.
    /// * [`Error::ModuleIsPrivate`] Attempted to navigate into a private module from an unauthorized scope.
    /// * [`Error::MainCannotBeAlias`] Attempted to alias an imported item to the reserved `main` identifier.
    /// * May also return errors propagated from item collection and insertion, such as [`Error::PrivateItem`] or [`Error::RedefinedItem`].
    pub(super) fn resolve_use(&mut self, use_decl: &UseDecl) -> Vec<Error> {
        let use_vis = use_decl.visibility().clone();
        let use_decl_items = match use_decl.items() {
            parse::UseItems::Single(elem) => std::slice::from_ref(elem),
            parse::UseItems::List(elems) => elems.as_slice(),
        };

        let mut errors = Vec::new();
        // Phase 1: navigate to the target module. If it cannot be reached, every imported name is poisoned.
        let Some(target_scope) = self.find_use_target(use_decl.path(), &mut errors) else {
            let local_names = use_decl_items
                .iter()
                .map(|(name, aliased)| aliased.as_ref().unwrap_or(name).clone());
            self.current_mut().poisoned.extend(local_names);
            return errors;
        };

        // Phase 2: stage each item. A failed item is reported, then poisoned or imported anyway.
        let current = self.current();
        let mut pending = ModuleScope::default();
        for (name, aliased) in use_decl_items {
            if aliased.as_ref().is_some_and(|a| a == MAIN_STR) {
                errors.push(Error::MainCannotBeAlias);
                continue;
            }

            let local_name = aliased.as_ref().unwrap_or(name);
            let stage = |pending: &mut ModuleScope, ignore_privacy: bool| {
                Self::resolve_processing_use_items_error(&[
                    Self::stage_collected(
                        Self::try_collect_item(
                            name,
                            local_name,
                            &target_scope.aliases,
                            &use_vis,
                            ignore_privacy,
                        ),
                        &current.aliases,
                        &mut pending.aliases,
                    ),
                    Self::stage_collected(
                        Self::try_collect_item(
                            name,
                            local_name,
                            &target_scope.functions,
                            &use_vis,
                            ignore_privacy,
                        ),
                        &current.functions,
                        &mut pending.functions,
                    ),
                    Self::stage_collected(
                        Self::try_collect_item(
                            name,
                            local_name,
                            &target_scope.submodules,
                            &use_vis,
                            ignore_privacy,
                        ),
                        &current.submodules,
                        &mut pending.submodules,
                    ),
                ])
            };

            let Err(error) = stage(&mut pending, false) else {
                continue;
            };

            match error {
                Error::UnresolvedItem { .. } => {
                    pending.poisoned.insert(local_name.clone());
                    if target_scope.poisoned.contains(name) {
                        continue;
                    }
                }
                Error::PrivateItem { .. } => {
                    let _ = stage(&mut pending, true);
                }
                _ => {}
            }
            errors.push(error);
        }

        // Phase 3: commit everything that was staged, including the poisoned names.
        let current = self.current_mut();
        current.aliases.extend(pending.aliases);
        current.functions.extend(pending.functions);
        current.submodules.extend(pending.submodules);
        current.poisoned.extend(pending.poisoned);

        errors
    }

    /// Navigate to the module that a `use` path names.
    ///
    /// A private module is reported but still entered, because its items are known.
    /// Returns `None` if the module does not exist.
    fn find_use_target(
        &self,
        path: &[Identifier],
        errors: &mut Vec<Error>,
    ) -> Option<&ModuleScope> {
        if path.first().map(|id| id.as_str()) != Some(CRATE_STR) {
            errors.push(Error::MissingCrateKeyword);
            return None;
        }

        // TODO: Part, that can be optimized
        // How many segments do the caller's path and the target's path have in common?
        let shared_prefix_len = self
            .path
            .iter()
            .zip(&path[1..])
            .take_while(|(curr, nav)| curr.as_str() == nav.as_str())
            .count();

        let mut target_scope = &self.root;

        for (ind, segment) in path[1..].iter().enumerate() {
            let name = ModuleName::from_ident(segment);

            let Some((inner, visibility)) = target_scope.submodules.get(&name) else {
                if !target_scope.poisoned.contains(name.as_str()) {
                    errors.push(Error::ModuleNotFound { name });
                }
                return None;
            };

            if matches!(visibility, Visibility::Private) && shared_prefix_len < ind {
                errors.push(Error::ModuleIsPrivate { name });
            }

            target_scope = inner;
        }

        Some(target_scope)
    }

    /// Attempts to find `name` in `target_map` and prepare it for import into another scope.
    ///
    /// ## Errors
    ///
    /// * [`Error::UnresolvedItem`] The requested `name` was not found in the `target_map`.
    /// * [`Error::PrivateItem`] The requested item exists in the map, but its visibility is restricted to private.
    fn try_collect_item<K, V>(
        name: &SymbolName,
        local_name: &SymbolName,
        target_map: &HashMap<K, (V, Visibility)>,
        use_vis: &Visibility,
        ignore_privacy: bool,
    ) -> Result<(K, (V, Visibility)), Error>
    where
        K: Eq + std::hash::Hash + From<SymbolName> + Clone,
        V: Clone,
    {
        let (value, vis) =
            target_map
                .get(&K::from(name.clone()))
                .ok_or_else(|| Error::UnresolvedItem {
                    name: name.to_string(),
                })?;

        if matches!(vis, Visibility::Private) && !ignore_privacy {
            return Err(Error::PrivateItem {
                name: name.to_string(),
            });
        }

        Ok((
            K::from(local_name.clone()),
            (value.clone(), use_vis.clone()),
        ))
    }

    /// Stages a collected item, checking existing bindings and earlier staged names.
    ///
    /// ## Errors
    ///
    /// * [`Error::RedefinedItem`] An item with the same name is already defined in the target scope.
    /// * Propagates any upstream resolution error passed into the `res` argument.
    fn stage_collected<K, V>(
        res: Result<(K, (V, Visibility)), Error>,
        existing: &HashMap<K, (V, Visibility)>,
        pending: &mut HashMap<K, (V, Visibility)>,
    ) -> Result<(), Error>
    where
        K: Eq + std::hash::Hash + std::fmt::Display,
    {
        res.and_then(|(k, v)| {
            if existing.contains_key(&k) {
                return Err(Error::RedefinedItem {
                    name: k.to_string(),
                });
            }
            match pending.entry(k) {
                Entry::Occupied(entry) => Err(Error::RedefinedItem {
                    name: entry.key().to_string(),
                }),
                Entry::Vacant(entry) => {
                    entry.insert(v);
                    Ok(())
                }
            }
        })
    }

    // TODO: Consider to use better error handling
    /// Evaluates the results of attempting to collect an item from multiple namespaces
    /// (aliases, functions, submodules) and resolves the final error state.
    ///
    /// ## Errors
    ///
    /// * Returns a specific error (e.g., [`Error::PrivateItem`], [`Error::RedefinedItem`]) if one occurred.
    /// * Returns a fallback [`Error::UnresolvedItem`] if the item could not be found in any of the checked namespaces.
    fn resolve_processing_use_items_error(results: &[Result<(), Error>]) -> Result<(), Error> {
        if results.iter().any(|res| res.is_ok()) {
            return Ok(());
        }

        let errors: Vec<&Error> = results
            .iter()
            .filter_map(|res| res.as_ref().err())
            .collect();

        if let Some(&specific_err) = errors
            .iter()
            .find(|e| !matches!(e, Error::UnresolvedItem { .. }))
        {
            return Err(specific_err.clone());
        }

        // Fallback to the first `UnresolvedItem` error
        Err(errors[0].clone())
    }
}

#[cfg(test)]
mod use_tests {
    use crate::parse::ParseFromStr;
    use crate::str::AliasName;
    use crate::types::{ResolvedType, TypeConstructible};

    use super::*;

    fn resolve(scope: &mut ModuleTree, source: &str) -> Vec<String> {
        let program = parse::Program::parse_from_str(source).unwrap();
        let parse::Item::Use(decl) = &program.items()[0] else {
            panic!("expected use declaration");
        };

        scope
            .resolve_use(decl)
            .iter()
            .map(ToString::to_string)
            .collect()
    }

    fn alias(scope: &ModuleTree, name: &str) -> Option<ResolvedType> {
        scope.get_alias(&AliasName::from_str_unchecked(name)).ok()
    }

    fn scope() -> ModuleTree {
        let mut scope = ModuleTree::default();
        scope
            .enter(ModuleName::from_str_unchecked("source"), Visibility::Public)
            .unwrap();

        scope.current_mut().aliases.insert(
            AliasName::from_str_unchecked("Good"),
            (ResolvedType::u32(), Visibility::Public),
        );

        scope.current_mut().aliases.insert(
            AliasName::from_str_unchecked("Secret"),
            (ResolvedType::u16(), Visibility::Private),
        );

        scope.exit();
        scope
    }

    #[test]
    fn failed_imports_keep_the_rest_of_the_declaration() {
        let missing = Error::UnresolvedItem {
            name: "Missing".into(),
        };
        let secret = Error::PrivateItem {
            name: "Secret".into(),
        };
        let same = Error::RedefinedItem {
            name: "Same".into(),
        };
        let taken = Error::RedefinedItem {
            name: "Taken".into(),
        };
        let module = Error::ModuleNotFound {
            name: ModuleName::from_str_unchecked("nowhere"),
        };

        for (source, expected, bound) in [
            (
                "use crate::source::{Good, Missing};",
                vec![missing],
                vec![
                    ("Good", ResolvedType::u32()),
                    ("Missing", ResolvedType::never()),
                ],
            ),
            (
                "use crate::source::{Good, Secret};",
                vec![secret],
                vec![
                    ("Good", ResolvedType::u32()),
                    ("Secret", ResolvedType::u16()),
                ],
            ),
            (
                "use crate::source::{Good as Same, Good as Same};",
                vec![same],
                vec![("Same", ResolvedType::u32())],
            ),
            (
                "use crate::source::{Good, Good as main};",
                vec![Error::MainCannotBeAlias],
                vec![("Good", ResolvedType::u32())],
            ),
            (
                "use crate::source::{Good, Good as Taken};",
                vec![taken],
                vec![("Good", ResolvedType::u32()), ("Taken", ResolvedType::u8())],
            ),
            (
                "use crate::nowhere::{Good, Other};",
                vec![module],
                vec![
                    ("Good", ResolvedType::never()),
                    ("Other", ResolvedType::never()),
                ],
            ),
        ] {
            for nested in [false, true] {
                let mut scope = scope();
                if nested {
                    scope
                        .enter(
                            ModuleName::from_str_unchecked("consumer"),
                            Visibility::Private,
                        )
                        .unwrap();
                }

                scope.current_mut().aliases.insert(
                    AliasName::from_str_unchecked("Taken"),
                    (ResolvedType::u8(), Visibility::Private),
                );

                let path = scope.path.clone();
                let errors = resolve(&mut scope, source);

                let expected: Vec<_> = expected.iter().map(ToString::to_string).collect();
                assert_eq!(errors, expected, "{source}");
                for (name, ty) in &bound {
                    assert_eq!(alias(&scope, name).as_ref(), Some(ty), "{name} in {source}");
                }
                assert_eq!(scope.path, path, "{source}");
            }
        }
    }

    #[test]
    fn uses_of_poisoned_names_are_not_reported() {
        let mut scope = scope();
        scope
            .enter(
                ModuleName::from_str_unchecked("reexport"),
                Visibility::Public,
            )
            .unwrap();
        assert_eq!(
            resolve(&mut scope, "pub use crate::source::Missing;").len(),
            1
        );
        scope.exit();

        for source in [
            "use crate::reexport::Missing;",
            "use crate::reexport::Missing::Inner;",
        ] {
            let mut scope = ModuleTree {
                root: scope.root.clone(),
                path: Vec::new(),
            };
            assert_eq!(
                resolve(&mut scope, source),
                Vec::<String>::new(),
                "{source}"
            );
        }
    }

    #[test]
    fn successful_import_commits_all_namespaces_and_visibility() {
        let mut scope = scope();
        let source = &mut scope
            .root
            .submodules
            .get_mut(&ModuleName::from_str_unchecked("source"))
            .unwrap()
            .0;
        source.submodules.insert(
            ModuleName::from_str_unchecked("Good"),
            (ModuleScope::default(), Visibility::Public),
        );
        assert!(resolve(&mut scope, "pub use crate::source::Good as Renamed;").is_empty());

        assert_eq!(
            scope
                .root
                .aliases
                .get(&AliasName::from_str_unchecked("Renamed")),
            Some(&(ResolvedType::u32(), Visibility::Public))
        );
        assert!(matches!(
            scope
                .root
                .submodules
                .get(&ModuleName::from_str_unchecked("Renamed")),
            Some((_, Visibility::Public))
        ));
    }
}
