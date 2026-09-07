use std::collections::HashMap;

use crate::driver::{DependencyGraph, CRATE_STR, MAIN_MODULE, MAIN_STR};
use crate::error::{Diagnostic, DiagnosticManager, Error, Span};
use crate::parse::{self, Visibility};
use crate::str::{Identifier, ModuleName};

/// All enum declarations among `items`, recursing into `mod` blocks.
fn enum_declarations(items: &[parse::Item]) -> Vec<&parse::EnumDeclaration> {
    let mut found = Vec::new();
    for item in items {
        match item {
            parse::Item::EnumDeclaration(decl) => found.push(decl),
            parse::Item::Module(module) => found.extend(enum_declarations(module.items())),
            _ => {}
        }
    }
    found
}

// TODO: allow enums in deps when mentioned problems are resolved
/// Enums by design are nominative, therefore to reason about same named enums in different modules
/// we have to have a stable ABI with the suport of "qualified name".
/// Currently, there is no support of "qualified name" concpet, therefore at the time of creating
/// enums, it is forbidden to decler them in dependencies.
///
/// If we used current ABI we would face following problems:
/// 1. Adding or removing an unrelated dependency renumbers the files, so the same enum's ABI
///    name changes between builds even though no source changed.
///    The whole point of "identity is the qualified name" is that serialized forms can identify an enum across builds.
/// 2. Unwritable witness files. A user filling in a witness would have
///    to write `unit_2::Action::Cold` (a name that appears nowhere in their source and that they can't predict).
/// 3. Meaningless nominal distinctness. `a::Action` vs `b::Action` being distinct types only makes
///    sense if a and b are the user's module names, not compiler-generated counters.
fn forbid_enum_dec_in_deps(
    source_id: usize,
    local_items: &[parse::Item],
    diagnostics: &mut DiagnosticManager,
) {
    if source_id == MAIN_MODULE {
        return;
    }

    for decl in enum_declarations(local_items) {
        diagnostics.push(Diagnostic::new(
            Error::Grammar {
                msg: format!(
                    "enum `{}` is declared in a dependency file; \
                     enums may only be declared in the program's own files",
                    decl.name()
                ),
            },
            *decl.as_ref(),
        ));
    }
}

/// This is a core component of the [`DependencyGraph`].
impl DependencyGraph {
    /// Resolves the dependency graph and constructs the final AST program.
    pub(crate) fn linearize_and_assemble(
        &self,
        diagnostics: &mut DiagnosticManager,
    ) -> Option<parse::Program> {
        match self.linearize() {
            Ok(order) => {
                diagnostics.with_source_order(&order);
                self.assemble_program(&order, diagnostics)
            }
            Err(err) => {
                diagnostics.push(err);
                None
            }
        }
    }

    /// Constructs the unified array of items for the entire multi-program.
    fn assemble_program(
        &self,
        order: &[usize],
        diagnostics: &mut DiagnosticManager,
    ) -> Option<parse::Program> {
        let mut items = Vec::with_capacity(order.len());

        let target_ids: HashMap<Span, usize> = self
            .use_cache
            .iter()
            .map(|(span, resolved)| {
                let id = self
                    .sources
                    .id(&resolved.path)
                    .expect("resolved path must be registered in source map");
                (*span, id)
            })
            .collect();

        for &source_id in order {
            let module = &self.modules[&source_id];

            let local_items: Vec<parse::Item> = module
                .program
                .items()
                .iter()
                .filter_map(|item| self.rewrite_item(item, &target_ids))
                .collect();

            if source_id == MAIN_MODULE {
                let has_main = local_items
                    .iter()
                    .any(|item| matches!(item, parse::Item::Function(f) if f.name() == MAIN_STR));

                if !has_main {
                    diagnostics.push(Diagnostic::global(Error::CannotParse {
                        msg: Error::MainOutOfEntryFile.to_string(),
                    }));
                }
            }

            forbid_enum_dec_in_deps(source_id, &local_items, diagnostics);

            // TODO(enums): the flattened output wraps every file — the
            // entry file included — in a generated module, but enum
            // declarations are only valid at the top level of a file, so
            // flattening an enum program produces source that no longer
            // re-parses (`TemplateAst::flatten`). Splice the entry
            // file's items at the root instead of wrapping them.
            let name = ModuleName::from_ident(&Self::get_module_name(source_id));
            items.push(parse::Item::Module(parse::Module::new(
                source_id,
                Visibility::Private,
                name,
                &local_items,
            )));
        }

        (!diagnostics.has_errors())
            .then(|| parse::Program::new(&items, *self.modules[&MAIN_MODULE].program.as_ref()))
    }

    /// Rewrites a single item for the flattened single-file representation.
    fn rewrite_item(
        &self,
        item: &parse::Item,
        target_ids: &HashMap<Span, usize>,
    ) -> Option<parse::Item> {
        match item {
            parse::Item::Use(use_decl) => Some(self.rewrite_use(use_decl, target_ids)),
            parse::Item::Module(module) => {
                let items: Vec<parse::Item> = module
                    .items()
                    .iter()
                    .filter_map(|inner_item| self.rewrite_item(inner_item, target_ids))
                    .collect();

                Some(parse::Item::Module(parse::Module::new(
                    module.span().file_id,
                    module.visibility().clone(),
                    module.name().clone(),
                    &items,
                )))
            }
            parse::Item::TypeAlias(_)
            | parse::Item::Function(_)
            | parse::Item::EnumDeclaration(_) => Some(item.clone()),
            parse::Item::Ignored => None,
        }
    }

    /// Rewrites a `use` declaration into its canonical `crate`-rooted form.
    ///
    /// The resolved path becomes `crate::unit_<N>::<mod_path...>`, where `N` is
    /// the source id of the file that owns the imported item.
    ///
    /// ## Example
    ///
    /// - `use base_math::simple_op::hash` → `use crate::unit_2::hash`
    fn rewrite_use(
        &self,
        use_decl: &parse::UseDecl,
        target_ids: &HashMap<Span, usize>,
    ) -> parse::Item {
        let span = *use_decl.span();
        let resolved = &self.use_cache[&span];
        let target_id = target_ids[&span];

        let mut new_path = Vec::with_capacity(resolved.mod_path.len() + 2);
        new_path.push(Identifier::from_str_unchecked(CRATE_STR));
        new_path.push(Self::get_module_name(target_id));
        new_path.extend(resolved.mod_path.iter().cloned());

        let mut use_decl = use_decl.clone();
        use_decl.set_path(&new_path);
        parse::Item::Use(use_decl)
    }

    fn get_module_name(source_id: usize) -> Identifier {
        Identifier::from_str_unchecked(format!("unit_{}", source_id).as_str())
    }
}

#[cfg(test)]
mod flattening_tests {
    use crate::driver::tests::setup_graph;
    use crate::driver::CRATE_STR;
    use crate::error::{Diagnostic, Error, Location, Span};
    use crate::parse::{self, Visibility};

    use std::collections::HashMap;

    // Helper to get the built program
    fn build_flattened_program(
        files: Vec<(&str, &str)>,
    ) -> (parse::Program, HashMap<String, usize>) {
        let (graph, ids, _dir, mut diagnostics) = setup_graph(files);

        let Some(program) = graph.linearize_and_assemble(&mut diagnostics) else {
            panic!("{}", &diagnostics);
        };

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
                    if *m.name() == *expected_mod_name {
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

        let has_dep_func = wrapped_module
            .items()
            .iter()
            .any(|item| matches!(item, parse::Item::Function(f) if f.name() == "dep_func"));
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
        assert_eq!(path[0], *CRATE_STR, "Path must start with `crate`");
        assert_eq!(
            path[1],
            *expected_file_segment.as_str(),
            "Path must route through the canonical `unit_N`"
        );
    }

    #[test]
    fn dependency_main_does_not_satisfy_missing_root_main() {
        let (graph, _ids, _dir, mut diagnostics) = setup_graph(vec![
            ("main.simf", "use lib::A::helper;"),
            (
                "libs/lib/A.simf",
                "fn main() { assert!(false); } pub fn helper() {}",
            ),
        ]);

        let driver_program = graph.linearize_and_assemble(&mut diagnostics);

        assert!(
            driver_program.is_none(),
            "Expected the build to fail and return None, but got: {:?}",
            driver_program
        );

        assert!(
            diagnostics.has_errors(),
            "a dependency `fn main` must not satisfy a missing entrypoint `fn main`"
        );
    }

    #[test]
    fn driver_supplies_dependency_order_for_diagnostic_presentation() {
        let (graph, ids, _dir, mut diagnostics) = setup_graph(vec![
            ("libs/lib/A.simf", "pub fn helper() {}"),
            ("main.simf", "use lib::A::helper; fn main() {}"),
        ]);
        let main_id = ids["main"];
        let dependency_id = ids["A"];

        diagnostics.push(Diagnostic::new(
            Error::CannotParse {
                msg: "entry".to_owned(),
            },
            Span::new(main_id, 0..1),
        ));
        diagnostics.push(Diagnostic::new(
            Error::CannotParse {
                msg: "dependency".to_owned(),
            },
            Span::new(dependency_id, 0..1),
        ));

        let _ = graph.linearize_and_assemble(&mut diagnostics);
        assert!(matches!(
            diagnostics.diagnostics()[0].location(),
            Location::Code(span) if span.file_id == main_id
        ));
        assert!(matches!(
            diagnostics.presentation_order()[0].location(),
            Location::Code(span) if span.file_id == dependency_id
        ));
    }
}

#[cfg(test)]
mod dependency_map_tests {
    use crate::driver::tests::setup_graph;
    use crate::error::DiagnosticManager;

    // Helper to run the driver and return the error collector so we can inspect it.
    fn run_driver(files: Vec<(&str, &str)>) -> DiagnosticManager {
        let (graph, _ids, _dir, mut diagnostics) = setup_graph(files);
        let _ = graph.linearize_and_assemble(&mut diagnostics).unwrap();
        diagnostics
    }

    #[test]
    fn test_crate_path_resolves_to_physical_file() {
        // Scenario: `crate::utils::math` should map to the physical `utils/math.simf` file.
        let diagnostics = run_driver(vec![
            ("utils/math.simf", "pub fn add() {}"),
            ("main.simf", "use crate::utils::math::add; fn main() {}"),
        ]);

        assert!(
            !diagnostics.has_errors(),
            "Driver should successfully find the physical file 'utils/math.simf'. Errors: {}",
            diagnostics
        );
    }

    #[test]
    fn test_crate_path_fallback_to_inline_module() {
        // Scenario: `brother.simf` does NOT exist. `crate::brother` must fallback
        // to `main.simf` and treat `brother` as an inline mod_path.
        let diagnostics = run_driver(vec![(
            "main.simf",
            "
                mod brother { pub fn toy() {} }
                use crate::brother::toy;
                fn main() {}
            ",
        )]);

        assert!(
            !diagnostics.has_errors(),
            "Driver must fallback to main.simf for inline modules without throwing FileNotFound. Errors: {}",
            diagnostics
        );
    }

    #[test]
    fn test_crate_path_deeply_nested_inline_fallback() {
        // Scenario: A physical file exists (`utils.simf`), but the REST of the path is inline modules!
        let diagnostics = run_driver(vec![
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
            !diagnostics.has_errors(),
            "Driver must split the path at the file boundary correctly. Errors: {}",
            diagnostics
        );
    }

    #[test]
    fn test_external_dependency_resolution() {
        // Scenario: Resolving `use lib::A::foo` across the remapping boundary.
        let diagnostics = run_driver(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("main.simf", "use lib::A::foo; fn main() {}"),
        ]);

        assert!(
            !diagnostics.has_errors(),
            "External dependency resolution via drp_name failed. Errors: {}",
            diagnostics
        );
    }
}
