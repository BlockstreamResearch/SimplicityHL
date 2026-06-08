use crate::driver::{DependencyGraph, CRATE_STR, MAIN_MODULE, MAIN_STR};
use crate::error::{Error, ErrorCollector, RichError};
use crate::parse::{self, Visibility};
use crate::str::{Identifier, ModuleName};

/// This is a core component of the [`DependencyGraph`].
impl DependencyGraph {
    /// Resolves the dependency graph and constructs the final AST program.
    pub fn linearize_and_build(
        &self,
        handler: &mut ErrorCollector,
    ) -> Result<Option<parse::Program>, String> {
        match self.linearize() {
            Ok(order) => Ok(self.build_program(&order, handler)),
            Err(err) => Err(err.to_string()),
        }
    }

    fn get_module_name(source_id: usize) -> Identifier {
        Identifier::from_str_unchecked(format!("unit_{}", source_id).as_str())
    }

    /// Constructs the unified array of items for the entire multi-program.
    fn build_program(
        &self,
        order: &[usize],
        handler: &mut ErrorCollector,
    ) -> Option<parse::Program> {
        let mut items = Vec::with_capacity(order.len());

        for &source_id in order {
            let module = &self.modules[source_id];

            let local_items: Vec<parse::Item> = module
                .program
                .items()
                .iter()
                .filter_map(|item| self.rewrite_item(source_id, item))
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
            }

            let name = ModuleName::from_str_unchecked(Self::get_module_name(source_id).as_inner());
            items.push(parse::Item::Module(parse::Module::new(
                source_id,
                Visibility::Private,
                name,
                &local_items,
            )));
        }

        (!handler.has_errors())
            .then(|| parse::Program::new(&items, *self.modules[MAIN_MODULE].program.as_ref()))
    }

    /// Rewrites a single item for the flattened single-file representation.
    fn rewrite_item(&self, source_id: usize, item: &parse::Item) -> Option<parse::Item> {
        match item {
            parse::Item::TypeAlias(alias) => {
                let mut alias = alias.clone();
                alias.set_file_id(source_id);
                Some(parse::Item::TypeAlias(alias))
            }
            parse::Item::Function(function) => {
                let mut function = function.clone();
                function.set_file_id(source_id);
                Some(parse::Item::Function(function))
            }
            parse::Item::Use(use_decl) => Some(self.rewrite_use(source_id, use_decl)),
            parse::Item::Module(module) => {
                let items: Vec<parse::Item> = module
                    .items()
                    .iter()
                    .filter_map(|inner_item| self.rewrite_item(source_id, inner_item))
                    .collect();

                Some(parse::Item::Module(parse::Module::new(
                    source_id,
                    module.visibility().clone(),
                    module.name().clone(),
                    &items,
                )))
            }
            parse::Item::Ignored => None,
        }
    }

    /// Rewrites a `use` declaration by replacing the drp alias with the canonical
    /// `file_N` module name, prepending it to the remaining `mod_path` from the cache.
    /// If the target is the `MAIN_MODULE`, the `file_N` segment is safely omitted.
    ///
    /// ## Example
    ///
    /// `use base_math::simple_op::hash` into `use file_2::hash`
    /// `use crate::inline_mod::item` into `use crate::inline_mod::item`
    fn rewrite_use(&self, source_id: usize, use_decl: &parse::UseDecl) -> parse::Item {
        let mut use_decl = use_decl.clone();
        use_decl.set_file_id(source_id);
        let resolved = &self.use_cache[&use_decl];
        let target_id = self.lookup[&resolved.path];

        let mut new_path = Vec::with_capacity(resolved.mod_path.len() + 2);
        new_path.push(Identifier::from_str_unchecked(CRATE_STR));

        new_path.push(Self::get_module_name(target_id));
        new_path.extend(resolved.mod_path.iter().cloned());

        use_decl.set_path(&new_path);
        parse::Item::Use(use_decl)
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

        let program = graph
            .linearize_and_build(&mut error_handler)
            .expect("Linearize should not fail in this test")
            .expect("Build should succeed and return Some(Program)");

        (program, ids)
    }

    #[test]
    fn test_dependency_is_wrapped_in_file_module() {
        // Scenario: A dependency file MUST be wrapped in a `mod file_N` block,
        // and its visibility must be Private to prevent leaking.
        let (program, ids) = build_flattened_program(vec![
            ("libs/lib/A.simf", "pub fn dep_func() {}"),
            ("main.simf", "use lib::A::dep_func; fn main() {}"),
        ]);

        let file_a_id = ids["A"];
        let expected_mod_name = format!("unit_{}", file_a_id);

        let wrapped_module = program
            .items()
            .iter()
            .find_map(|item| {
                if let parse::Item::Module(m) = item {
                    if m.name().as_inner() == expected_mod_name.as_str() {
                        return Some(m);
                    }
                }
                None
            })
            .expect("Dependency should be wrapped in a file_N module");

        assert!(
            matches!(wrapped_module.visibility(), Visibility::Private),
            "The file wrapper module must be strictly private"
        );

        let has_dep_func = wrapped_module.items().iter().any(
            |item| matches!(item, parse::Item::Function(f) if f.name().as_inner() == "dep_func"),
        );
        assert!(
            has_dep_func,
            "The file_N module must contain the dependency's items"
        );
    }

    #[test]
    fn test_use_paths_are_rewritten_to_canonical_files() {
        // Scenario: When main.simf says `use lib::A::foo`, the AST flattener
        // must rewrite this path to `use crate::file_N::foo`.
        let (program, ids) = build_flattened_program(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("main.simf", "use lib::A::foo; fn main() {}"),
        ]);

        let file_a_id = ids["A"];
        let expected_file_segment = format!("unit_{}", file_a_id);

        // Flatten the modules and search their inner contents
        let use_decl = program
            .items()
            .iter()
            .filter_map(|item| {
                if let parse::Item::Module(module) = item {
                    Some(module.items()) // Get the slice of inner items
                } else {
                    None
                }
            })
            .flatten() // Unpack all the inner slices into a single stream
            .find_map(|inner_item| {
                if let parse::Item::Use(u) = inner_item {
                    Some(u)
                } else {
                    None
                }
            })
            .expect("Main module should contain a use declaration");

        // Get the segments of the rewritten path
        let path = use_decl.path();

        assert!(
            path.len() >= 2,
            "Rewritten path must have at least 2 segments"
        );
        assert_eq!(
            path[0].as_inner(),
            CRATE_STR,
            "Path must start with `crate`"
        );
        assert_eq!(
            path[1].as_inner(),
            expected_file_segment.as_str(),
            "Path must route through the canonical `unit_N`"
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
            matches!(driver_program, Ok(None)),
            "Expected the build to fail and return Ok(None), but got: {:?}",
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
