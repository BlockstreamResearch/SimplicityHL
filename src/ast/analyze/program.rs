use std::collections::HashSet;
use std::sync::Arc;

use crate::driver::MAIN_STR;
use crate::error::{DiagnosticManager, Error, WithSpan};
use crate::parse::{self, Visibility};
use crate::str::FunctionName;
use crate::types::{EnumVariantInfo, ResolvedType, TypeConstructible, TypeDeconstructible};

use super::super::recovery::Failure;
use super::super::scope::Scope;
use super::super::{CustomFunction, Expression, Function, FunctionParam, Item, JetHinter, Program};
use super::AbstractSyntaxTree;

impl Program {
    /// Analyze the given parse tree.
    ///
    /// Errors are added to `diagnostics`. Returns `None` if any error was
    /// reported: a program with errors must never be compiled.
    pub fn analyze(
        from: &parse::Program,
        jet_hinter: Box<dyn JetHinter>,
        diagnostics: &mut DiagnosticManager,
    ) -> Option<Self> {
        let mut scope = Scope::new(jet_hinter);
        let main = Self::analyze_main(from, &mut scope);
        scope.try_into_program(main, diagnostics)
    }

    /// Analyze every item and return the body of the single main function.
    fn analyze_main(from: &parse::Program, scope: &mut Scope) -> Result<Expression, Failure> {
        let items = Item::analyze_items(from.items(), scope)?;
        debug_assert!(scope.is_outside_function());
        debug_assert!(
            scope.module_path().is_empty(),
            "Unclosed module scopes remain"
        );

        // If we find a duplicate of main function
        match Self::extract_single_main(&items).with_span(from)? {
            Some(main) => Ok(main),
            // `main` is defined, but its failure was already reported
            None if Self::defines_main(from.items()) => Err(Failure::Reported),
            None => Err(Error::MainRequired).with_span(from)?,
        }
    }

    /// Check if the items define a main function, including inside modules.
    fn defines_main(items: &[parse::Item]) -> bool {
        items.iter().any(|item| match item {
            parse::Item::Function(function) => function.name() == MAIN_STR,
            parse::Item::Module(module) => Self::defines_main(module.items()),
            _ => false,
        })
    }

    fn extract_single_main(items: &[Item]) -> Result<Option<Expression>, Error> {
        let mut main_expr = None;

        for item in items {
            let extracted = match item {
                Item::Function(Function::Main(expr)) => Some(expr.clone()),
                Item::Module(items) => Self::extract_single_main(items)?,
                _ => None,
            };

            let Some(expr) = extracted else {
                continue;
            };

            if main_expr.replace(expr).is_some() {
                return Err(Error::FunctionRedefined {
                    name: FunctionName::main(),
                });
            }
        }

        Ok(main_expr)
    }
}

impl Item {
    /// Analyze the items of a module in order.
    fn analyze_items(from: &[parse::Item], scope: &mut Scope) -> Result<Vec<Self>, Failure> {
        let unit = ResolvedType::unit();
        let mut items = Vec::with_capacity(from.len());

        for item in from {
            match Self::analyze(item, &unit, scope) {
                Ok(item) => items.push(item),
                Err(failure) if matches!(item, parse::Item::Function(f) if f.name() == MAIN_STR) => {
                    scope.report(failure);
                }
                Err(failure) => return Err(failure),
            }
        }

        Ok(items)
    }
}

impl AbstractSyntaxTree for Item {
    type From = parse::Item;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, Failure> {
        assert!(ty.is_unit(), "Items cannot return anything");
        assert!(
            scope.is_outside_function(),
            "Variables live only inside the function"
        );

        match from {
            parse::Item::TypeAlias(alias) => {
                scope.insert_alias(alias.clone()).with_span(alias)?;
                Ok(Self::TypeAlias)
            }
            parse::Item::Function(function) => {
                Function::analyze(function, ty, scope).map(Self::Function)
            }
            parse::Item::Use(use_decl) => {
                scope.resolve_use(use_decl);
                Ok(Self::Use)
            }
            parse::Item::EnumDeclaration(decl) => {
                if decl.variants().is_empty() {
                    // A sum of zero types would be uninhabited, which
                    // Simplicity's type algebra cannot express.
                    Err(Error::Grammar {
                        msg: format!("enum '{}' must have at least one variant", decl.name()),
                    })
                    .with_span(decl)?;
                }

                let mut seen_names = HashSet::new();
                scope.analyze_all(decl.variants(), |v, _scope| {
                    if seen_names.insert(v.name()) {
                        return Ok(());
                    }
                    Err(Error::Grammar {
                        msg: format!(
                            "enum '{}' has duplicate variant name '{}'",
                            decl.name(),
                            v.name()
                        ),
                    })
                    .with_span(v)
                    .map_err(Failure::from)
                })?;

                let variants = decl
                    .variants()
                    .iter()
                    .map(|v| {
                        let payload = v
                            .payload()
                            .iter()
                            .map(|ty| scope.resolve_or_never(ty, v))
                            .collect::<Arc<[_]>>();
                        EnumVariantInfo::new(v.name().clone(), payload)
                    })
                    .collect::<Arc<[_]>>();
                scope
                    .insert_enum(decl.name().clone(), decl.visibility().clone(), variants)
                    .with_span(decl)?;

                Ok(Self::EnumDeclaration)
            }
            parse::Item::Module(module) => scope
                .in_module(
                    module.name().clone(),
                    module.visibility().clone(),
                    |scope| Item::analyze_items(module.items(), scope).map(Self::Module),
                )
                .with_span(module)?,
            parse::Item::Ignored => Ok(Self::Ignored),
        }
    }
}

impl AbstractSyntaxTree for Function {
    type From = parse::Function;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, Failure> {
        assert!(ty.is_unit(), "Function definitions cannot return anything");
        assert!(
            scope.is_outside_function(),
            "Variables live only inside the function"
        );

        if from.name() != MAIN_STR {
            let mut seen_params = HashSet::new();

            // A broken type in the signature becomes `!`, so the function is still
            // registered and its calls do not report it as undefined.
            let params = from
                .params()
                .iter()
                .map(|param| {
                    if !seen_params.insert(param.identifier()) {
                        scope.report(
                            Error::ParameterRedefined {
                                identifier: param.identifier().clone(),
                            }
                            .with_span(*param.span()),
                        );
                    }

                    FunctionParam {
                        identifier: param.identifier().clone(),
                        ty: scope.resolve_or_never(param.ty(), from),
                        span: *param.span(),
                    }
                })
                .collect::<Arc<[FunctionParam]>>();
            let ret = from
                .ret()
                .as_ref()
                .map_or_else(ResolvedType::unit, |aliased| {
                    scope.resolve_or_never(aliased, from)
                });

            let body = scope.in_function(|scope| {
                for param in params.iter() {
                    scope.insert_variable(param.identifier().clone(), param.ty().clone());
                }
                Expression::analyze(from.body(), &ret, scope).map(Arc::new)
            });

            // A broken body does not change the declared signature,
            // so later items can still call the function.
            let body = body.map_err(|failure| scope.report(failure)).ok();
            let function = CustomFunction {
                params,
                ret,
                body,
                span: *from.span(),
            };
            scope
                .insert_function(from.name().clone(), from.visibility().clone(), function)
                .with_span(from)?;

            return Ok(Self::Custom);
        }

        if matches!(from.visibility(), Visibility::Public) {
            scope.report(Error::MainCannotBePublic.with_span(*from.span()));
        }

        if !from.params().is_empty() {
            return Err(Error::MainNoInputs).with_span(from)?;
        }

        if let Some(aliased) = from.ret() {
            let resolved = scope.resolve_or_never(aliased, from);
            if !resolved.compatible(&ResolvedType::unit()) {
                return Err(Error::MainNoOutput).with_span(from)?;
            }
        }

        let body = scope.in_main(|scope| Expression::analyze(from.body(), ty, scope))?;
        Ok(Self::Main(body))
    }
}
