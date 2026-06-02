use crate::driver::{DependencyGraph, CRATE_STR, MAIN_MODULE};
use crate::error::ErrorCollector;
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
                items.extend(local_items);
                continue;
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
            parse::Item::Use(use_decl) => Some(self.rewrite_use(use_decl)),
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
    fn rewrite_use(&self, use_decl: &parse::UseDecl) -> parse::Item {
        let resolved = &self.use_cache[use_decl];
        let target_id = self.lookup[&resolved.path];

        let mut new_path = Vec::with_capacity(resolved.mod_path.len() + 2);
        new_path.push(Identifier::from_str_unchecked(CRATE_STR));

        if target_id != MAIN_MODULE {
            new_path.push(Self::get_module_name(target_id));
        }
        new_path.extend(resolved.mod_path.iter().cloned());

        parse::Item::Use(parse::UseDecl::new(
            use_decl.visibility().clone(),
            &new_path,
            use_decl.items().clone(),
            *use_decl.span(),
        ))
    }
}
