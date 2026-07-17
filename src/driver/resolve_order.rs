use crate::driver::{DependencyGraph, CRATE_STR, MAIN_MODULE, MAIN_STR};
use crate::error::{Error, ErrorCollector, RichError};
use crate::parse::{self, Visibility};
use crate::str::{Identifier, ModuleName};

/// This is a core component of the [`DependencyGraph`].
impl DependencyGraph {
    /// Resolves the dependency graph and constructs the final AST program.
    pub fn linearize_and_build(&self, handler: &mut ErrorCollector) -> Option<parse::Program> {
        match self.linearize() {
            Ok(order) => self.build_program(&order, handler),
            Err(err) => {
                handler.push(err);
                None
            }
        }
    }

    /// Constructs the unified array of items for the entire multi-program.
    ///
    /// The main file's items are spliced at the root, as in a single-file
    /// program. Every other file mounts at its logical module path
    /// (`lib::A` for `libs/lib/A.simf` mapped as `lib`), so names in the
    /// flattened tree are the names the user wrote. Files of packages that
    /// the root program has no remapping for keep a synthetic `unit_N`
    /// mount.
    fn build_program(
        &self,
        order: &[usize],
        handler: &mut ErrorCollector,
    ) -> Option<parse::Program> {
        let mut mounts = MountTree::default();
        let mut root_items = Vec::new();

        for &source_id in order {
            let module = &self.modules[source_id];

            let local_items: Vec<parse::Item> = module
                .program
                .items()
                .iter()
                .filter_map(|item| self.rewrite_item(item))
                .collect();

            if source_id == MAIN_MODULE {
                let has_main = local_items.iter().any(|item| {
                    matches!(item, parse::Item::Function(f) if f.name().as_inner() == MAIN_STR)
                });

                if !has_main {
                    handler.push(RichError::parsing_error(
                        &Error::MainOutOfEntryFile.to_string(),
                    ));
                }

                root_items.push((source_id, local_items));
                continue;
            }

            mounts.insert(&self.mount_segments(source_id), source_id, local_items);
        }

        let mut items = mounts.into_items();
        for (_, local_items) in root_items {
            items.extend(local_items);
        }

        (!handler.has_errors())
            .then(|| parse::Program::new(&items, *self.modules[MAIN_MODULE].program.as_ref()))
    }

    /// The logical mount path of `source_id`, if the root program has a
    /// name for its package.
    fn root_mount(&self, source_id: usize) -> Option<Vec<Identifier>> {
        let main = self.modules[MAIN_MODULE].source.name();
        let file = self.modules[source_id].source.name();
        self.dependency_map.root_mount(main, file)
    }

    /// The module path under which `source_id` mounts in the flattened
    /// tree: empty for the main file, the logical path for root-named
    /// packages, a synthetic `unit_N` for transitive-only packages.
    fn mount_segments(&self, source_id: usize) -> Vec<Identifier> {
        if source_id == MAIN_MODULE {
            return Vec::new();
        }
        self.root_mount(source_id)
            .unwrap_or_else(|| vec![Self::get_module_name(source_id)])
    }

    /// Rewrites a single item for the flattened single-file representation.
    fn rewrite_item(&self, item: &parse::Item) -> Option<parse::Item> {
        match item {
            parse::Item::Use(use_decl) => Some(self.rewrite_use(use_decl)),
            parse::Item::Module(module) => {
                let items: Vec<parse::Item> = module
                    .items()
                    .iter()
                    .filter_map(|inner_item| self.rewrite_item(inner_item))
                    .collect();

                Some(parse::Item::Module(parse::Module::new(
                    module.span().file_id,
                    module.visibility().clone(),
                    module.name().clone(),
                    &items,
                )))
            }
            parse::Item::TypeAlias(_) | parse::Item::Function(_) => Some(item.clone()),
            parse::Item::Ignored => None,
        }
    }

    /// Rewrites a `use` declaration to its canonical `crate`-rooted form.
    ///
    /// The resolved path becomes `crate::<mount...>::<mod_path...>`, where
    /// `<mount>` is the target file's logical mount path — empty for the
    /// main file, e.g. `lib::A` for a root-named dependency file.
    ///
    /// ## Examples
    ///
    /// - `use base_math::simple_op::hash` → `use crate::base_math::simple_op::hash`
    /// - `use some_dep::item` (target = main file) → `use crate::item`
    fn rewrite_use(&self, use_decl: &parse::UseDecl) -> parse::Item {
        let resolved = &self.use_cache[use_decl.span()];
        let target_id = self
            .source_map
            .id(&resolved.path)
            .expect("resolved path must be registered");

        let mount = self.mount_segments(target_id);
        let mut new_path = Vec::with_capacity(resolved.mod_path.len() + mount.len() + 1);
        new_path.push(Identifier::from_str_unchecked(CRATE_STR));
        new_path.extend(mount);
        new_path.extend(resolved.mod_path.iter().cloned());

        let mut use_decl = use_decl.clone();
        use_decl.set_path(&new_path);
        parse::Item::Use(use_decl)
    }

    fn get_module_name(source_id: usize) -> Identifier {
        Identifier::from_str_unchecked(format!("unit_{}", source_id).as_str())
    }
}

/// Tree of module mounts for non-main source files, preserving insertion
/// order so the flattened program is deterministic.
#[derive(Default)]
struct MountTree {
    children: Vec<(Identifier, MountTree)>,
    items: Vec<parse::Item>,
    /// File id of the first source mounted at or below this node, used for
    /// the synthetic module's span.
    file_id: Option<usize>,
}

impl MountTree {
    fn insert(&mut self, segments: &[Identifier], file_id: usize, items: Vec<parse::Item>) {
        self.file_id.get_or_insert(file_id);
        let Some((first, rest)) = segments.split_first() else {
            self.items.extend(items);
            return;
        };
        let child = match self.children.iter_mut().find(|(name, _)| name == first) {
            Some((_, child)) => child,
            None => {
                self.children.push((first.clone(), MountTree::default()));
                &mut self
                    .children
                    .last_mut()
                    .expect("just pushed a child")
                    .1
            }
        };
        child.insert(rest, file_id, items);
    }

    fn into_items(self) -> Vec<parse::Item> {
        let file_id = self.file_id.unwrap_or(MAIN_MODULE);
        let mut items: Vec<parse::Item> = self
            .children
            .into_iter()
            .map(|(name, child)| {
                let child_file_id = child.file_id.unwrap_or(file_id);
                let child_items = child.into_items();
                parse::Item::Module(parse::Module::new(
                    child_file_id,
                    Visibility::Public,
                    ModuleName::from_str_unchecked(name.as_inner()),
                    &child_items,
                ))
            })
            .collect();
        items.extend(self.items);
        items
    }
}

#[cfg(test)]
mod flattening_tests {
    use crate::driver::tests::setup_graph;
    use crate::driver::CRATE_STR;
    use crate::error::ErrorCollector;
    use crate::parse::{self, Visibility};

    use std::collections::HashMap;

    // Helper to get the built program
    fn build_flattened_program(
        files: Vec<(&str, &str)>,
    ) -> (parse::Program, HashMap<String, usize>) {
        let (graph, ids, _dir) = setup_graph(files);
        let mut error_handler = ErrorCollector::new();

        let Some(program) = graph.linearize_and_build(&mut error_handler) else {
            panic!("{}", &error_handler.to_string());
        };

        (program, ids)
    }

    #[test]
    fn test_dependency_mounts_at_logical_path() {
        // Scenario: A root-named dependency file mounts at its logical
        // module path (`lib::A` for `libs/lib/A.simf` mapped as `lib`),
        // and the main file's items are spliced at the root.
        let (program, _ids) = build_flattened_program(vec![
            ("libs/lib/A.simf", "pub fn dep_func() {}"),
            ("main.simf", "use lib::A::dep_func; fn main() {}"),
        ]);

        let lib = program
            .items()
            .iter()
            .find_map(|item| match item {
                parse::Item::Module(m) if m.name().as_inner() == "lib" => Some(m),
                _ => None,
            })
            .expect("dependency package should mount as `mod lib`");
        let file_a = lib
            .items()
            .iter()
            .find_map(|item| match item {
                parse::Item::Module(m) if m.name().as_inner() == "A" => Some(m),
                _ => None,
            })
            .expect("dependency file should mount as `mod A` inside `mod lib`");

        let has_dep_func = file_a.items().iter().any(
            |item| matches!(item, parse::Item::Function(f) if f.name().as_inner() == "dep_func"),
        );
        assert!(
            has_dep_func,
            "the mounted module must contain the dependency's items"
        );

        let main_at_root = program
            .items()
            .iter()
            .any(|item| matches!(item, parse::Item::Function(f) if f.name().as_inner() == "main"));
        assert!(main_at_root, "the main file's items live at the root");
    }

    #[test]
    fn test_use_paths_are_rewritten_to_canonical_files() {
        // Scenario: When main.simf says `use lib::A::foo`, the AST flattener
        // rewrites this path to `use crate::lib::A::foo` — the mount path
        // matches the names the user wrote.
        let (program, _ids) = build_flattened_program(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("main.simf", "use lib::A::foo; fn main() {}"),
        ]);

        // The main file's items are spliced at the root.
        let use_decl = program
            .items()
            .iter()
            .find_map(|item| match item {
                parse::Item::Use(u) => Some(u),
                _ => None,
            })
            .expect("the root should contain the main file's use declaration");

        let path: Vec<&str> = use_decl.path().iter().map(|s| s.as_inner()).collect();
        assert_eq!(
            path,
            [CRATE_STR, "lib", "A"],
            "the rewritten path routes through the logical mount"
        );
    }

    #[test]
    fn dependency_main_does_not_satisfy_missing_root_main() {
        let (graph, _ids, _dir) = setup_graph(vec![
            ("main.simf", "use lib::A::helper;"),
            (
                "libs/lib/A.simf",
                "fn main() { assert!(false); } pub fn helper() {}",
            ),
        ]);

        let mut error_handler = ErrorCollector::new();
        let driver_program = graph.linearize_and_build(&mut error_handler);

        assert!(
            driver_program.is_none(),
            "Expected the build to fail and return None, but got: {:?}",
            driver_program
        );

        assert!(
            error_handler.has_errors(),
            "a dependency `fn main` must not satisfy a missing entrypoint `fn main`"
        );
    }
}

#[cfg(test)]
mod dependency_map_tests {
    use crate::driver::tests::setup_graph;
    use crate::error::ErrorCollector;

    // Helper to run the driver and return the error collector so we can inspect it.
    fn run_driver(files: Vec<(&str, &str)>) -> ErrorCollector {
        let (graph, _ids, _dir) = setup_graph(files);
        let mut error_handler = ErrorCollector::new();
        let _ = graph.linearize_and_build(&mut error_handler).unwrap();
        error_handler
    }

    #[test]
    fn test_crate_path_resolves_to_physical_file() {
        // Scenario: `crate::utils::math` should map to the physical `utils/math.simf` file.
        let errors = run_driver(vec![
            ("utils/math.simf", "pub fn add() {}"),
            ("main.simf", "use crate::utils::math::add; fn main() {}"),
        ]);

        assert!(
            !errors.has_errors(),
            "Driver should successfully find the physical file 'utils/math.simf'. Errors: {errors}"
        );
    }

    #[test]
    fn test_crate_path_fallback_to_inline_module() {
        // Scenario: `brother.simf` does NOT exist. `crate::brother` must fallback
        // to `main.simf` and treat `brother` as an inline mod_path.
        let errors = run_driver(vec![(
            "main.simf",
            "
                mod brother { pub fn toy() {} }
                use crate::brother::toy; 
                fn main() {}
            ",
        )]);

        assert!(!errors.has_errors(), "Driver must fallback to main.simf for inline modules without throwing FileNotFound. Errors: {errors}");
    }

    #[test]
    fn test_crate_path_deeply_nested_inline_fallback() {
        // Scenario: A physical file exists (`utils.simf`), but the REST of the path is inline modules!
        let errors = run_driver(vec![
            (
                "utils.simf",
                "pub mod deeply { pub mod nested { pub fn func() {} } }",
            ),
            (
                "main.simf",
                "use crate::utils::deeply::nested::func; fn main() {}",
            ),
        ]);

        assert!(
            !errors.has_errors(),
            "Driver must split the path at the file boundary correctly. Errors: {errors}"
        );
    }

    #[test]
    fn test_external_dependency_resolution() {
        // Scenario: Resolving `use lib::A::foo` across the remapping boundary.
        let errors = run_driver(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("main.simf", "use lib::A::foo; fn main() {}"),
        ]);

        assert!(
            !errors.has_errors(),
            "External dependency resolution via drp_name failed. Errors: {errors}"
        );
    }
}
