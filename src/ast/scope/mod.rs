mod locals;
mod modules;
mod program_inputs;

use std::convert::Infallible;
use std::sync::Arc;

use crate::ast::scope::modules::ModuleTree;
use crate::debug::TrackedCallName;
use crate::error::{Diagnostic, DiagnosticManager, Error, Span};
use crate::parse::{self, UseDecl, Visibility};
use crate::str::{AliasName, FunctionName, Identifier, ModuleName};
use crate::types::{AliasedType, EnumVariantInfo, ResolvedType};
use crate::TemplateProgramWitness;

use self::locals::Locals;
use self::program_inputs::ProgramInputs;
use super::recovery::{mentions_never, Failure};
use super::{CustomFunction, ElementsJetHinter, Expression, JetHinter, Program};

/// Scope for generating the abstract syntax tree.
///
/// The scope is used for:
/// 1. Assigning types to each variable
/// 2. Resolving type aliases
/// 3. Assigning types to each witness expression
/// 4. Resolving calls to custom functions
pub(super) struct Scope {
    modules: ModuleTree,
    locals: Locals,
    inputs: ProgramInputs,

    is_main: bool,
    /// Allow enum constructions to name an enum by its declared name even
    /// when that name is not an alias in scope. Enabled only for value
    /// parsing (witness and argument files), which runs without a scope.
    unscoped_enum_names: bool,
    jet_hinter: Box<dyn JetHinter>,
    /// Errors reported during analysis that did not stop it.
    diagnostics: Vec<Diagnostic>,
}

impl Default for Scope {
    fn default() -> Self {
        Self::new(
            // TODO: Should be passed in global configuration
            Box::new(ElementsJetHinter),
        )
    }
}

impl Scope {
    pub(super) fn new(jet_hinter: Box<dyn JetHinter>) -> Self {
        Self {
            modules: ModuleTree::default(),
            locals: Locals::default(),
            inputs: ProgramInputs::default(),
            is_main: false,
            unscoped_enum_names: false,
            jet_hinter,
            diagnostics: Vec::new(),
        }
    }

    /// Record an error without stopping analysis.
    ///
    /// A failure that was already reported is not recorded again.
    pub(super) fn report(&mut self, failure: impl Into<Failure>) {
        if let Failure::New(diagnostic) = failure.into() {
            // Like rustc, an error about a type with `!` is left until the error
            // that created `!` is fixed.
            if !mentions_never(diagnostic.error()) {
                self.diagnostics.push(diagnostic);
            }
        }
    }

    /// Report the error of a failed check that does not prevent building the node.
    pub(super) fn report_err(&mut self, result: Result<(), Diagnostic>) {
        if let Err(error) = result {
            self.report(error);
        }
    }

    /// Analyze every item, even if some of them fail.
    ///
    /// Every error is reported as soon as it is found. If any item fails,
    /// the caller receives [`Failure::Reported`] and stops as before.
    pub(super) fn analyze_all<A, T>(
        &mut self,
        items: impl IntoIterator<Item = A>,
        mut analyze: impl FnMut(A, &mut Self) -> Result<T, Failure>,
    ) -> Result<Vec<T>, Failure> {
        let mut results = Vec::new();
        let mut failed = false;

        for item in items {
            match analyze(item, self) {
                Ok(result) => results.push(result),
                Err(failure) => {
                    self.report(failure);
                    failed = true;
                }
            }
        }

        if failed {
            Err(Failure::Reported)
        } else {
            Ok(results)
        }
    }

    /// Scope for parsing values from witness and argument files: empty,
    /// except that enum constructions may name an enum by its declared name.
    pub(super) fn for_value_parsing() -> Self {
        Self {
            unscoped_enum_names: true,
            ..Self::default()
        }
    }

    pub(super) fn unscoped_enum_names(&self) -> bool {
        self.unscoped_enum_names
    }

    pub(super) fn jet_hinter(&self) -> &dyn JetHinter {
        self.jet_hinter.as_ref()
    }

    /// Consume the scope and return the errors reported during analysis.
    pub(super) fn into_diagnostics(self) -> Vec<Diagnostic> {
        self.diagnostics
    }

    pub(super) fn is_outside_function(&self) -> bool {
        // Entering a function body pushes a new map of variables,
        // and every nested block inside it pushes another one.
        // The stack is empty only when we are not inside any function.
        self.locals.depth() == 0
    }

    /// Analyze within a nested block scope and restore the previous scope afterwards
    pub(super) fn in_block<T>(&mut self, analyze: impl FnOnce(&mut Self) -> T) -> T {
        let outer_depth = self.locals.depth();
        self.locals.enter_block();
        let result = analyze(self);
        debug_assert_eq!(
            self.locals.depth(),
            outer_depth + 1,
            "Unbalanced nested block scopes"
        );
        self.locals.exit_block();
        debug_assert_eq!(
            self.locals.depth(),
            outer_depth,
            "Block scope was not restored"
        );
        result
    }

    /// Analyze within a function scope and restore the outside-function state afterwards
    pub(super) fn in_function<T>(&mut self, analyze: impl FnOnce(&mut Self) -> T) -> T {
        debug_assert!(self.is_outside_function(), "Already inside a function body");
        let result = self.in_block(analyze);
        debug_assert!(
            self.is_outside_function(),
            "Function scope was not restored"
        );
        result
    }

    /// Analyze within a match-arm scope and restore the enclosing scope afterwards
    pub(super) fn in_match_arm<T>(&mut self, analyze: impl FnOnce(&mut Self) -> T) -> T {
        self.in_block(analyze)
    }

    /// Push the scope of the main function onto the stack.
    ///
    /// ## Panics
    ///
    /// - Already inside the main function.
    /// - Already inside a function body.
    fn enter_main(&mut self) {
        assert!(!self.is_main, "Already inside main function");
        assert!(self.is_outside_function(), "Already inside a function body");
        self.locals.enter_block();
        self.is_main = true;
    }

    /// Analyze within the main-function scope and restore the outside-function state afterwards.
    pub(super) fn in_main<T>(&mut self, analyze: impl FnOnce(&mut Self) -> T) -> T {
        self.enter_main();
        let result = analyze(self);

        debug_assert!(self.is_main, "Main scope was exited during analysis");
        debug_assert_eq!(
            self.locals.depth(),
            1,
            "Unbalanced nested blocks in main scope"
        );

        self.exit_main();
        debug_assert!(!self.is_main, "Main scope was not restored");
        debug_assert!(
            self.is_outside_function(),
            "Main function scope was not restored"
        );
        result
    }

    /// Pop the scope of the main function from the stack.
    ///
    /// ## Panics
    ///
    /// - Not inside the main function.
    /// - Unclosed nested blocks remain.
    fn exit_main(&mut self) {
        assert!(self.is_main, "Current scope is not inside main function");
        self.locals.exit_block();
        self.is_main = false;
        assert!(
            self.is_outside_function(),
            "Current scope is not nested in topmost scope"
        )
    }

    /// Analyze within a named module and restore the enclosing module afterwards.
    pub(super) fn in_module<T>(
        &mut self,
        name: ModuleName,
        visibility: Visibility,
        analyze: impl FnOnce(&mut Self) -> T,
    ) -> Result<T, Error> {
        let outer_depth = self.modules.path().len();
        self.modules.enter(name.clone(), visibility)?;
        let result = analyze(self);
        debug_assert_eq!(
            self.modules.path().len(),
            outer_depth + 1,
            "Unbalanced nested module scopes"
        );
        debug_assert_eq!(
            self.modules.path().last(),
            Some(&name),
            "Current module changed during analysis"
        );
        self.modules.exit();
        debug_assert_eq!(
            self.modules.path().len(),
            outer_depth,
            "Module scope was not restored"
        );
        Ok(result)
    }

    pub(super) fn module_path(&self) -> &[ModuleName] {
        self.modules.path()
    }

    pub(super) fn resolve_use(&mut self, use_decl: &UseDecl) {
        let span = Span::from(use_decl);

        for error in self.modules.resolve_use(use_decl) {
            self.report(error.with_span(span));
        }
    }

    pub(super) fn get_alias(&self, name: &AliasName) -> Result<ResolvedType, Error> {
        self.modules.get_alias(name)
    }

    pub(super) fn resolve(&self, ty: &AliasedType) -> Result<ResolvedType, Error> {
        self.modules.resolve(ty)
    }

    pub(super) fn insert_enum(
        &mut self,
        name: AliasName,
        visibility: Visibility,
        variants: Arc<[EnumVariantInfo]>,
    ) -> Result<(), Error> {
        self.modules.insert_enum(name, visibility, variants)
    }

    pub(super) fn insert_function(
        &mut self,
        name: FunctionName,
        visibility: Visibility,
        function: CustomFunction,
    ) -> Result<(), Error> {
        self.modules.insert_function(name, visibility, function)
    }

    pub(super) fn get_function(
        &self,
        name: &FunctionName,
        span: impl Into<Span>,
    ) -> Result<CustomFunction, Failure> {
        match self.modules.get_function(name) {
            Ok(function) => Ok(function),
            Err(_) if self.modules.is_poisoned(name.as_str()) => Err(Failure::Reported),
            Err(error) => Err(error.with_span(span.into()).into()),
        }
    }

    /// Insert a variable into the current block.
    ///
    /// ## Panics
    ///
    /// - No active block.
    pub(super) fn insert_variable(&mut self, identifier: Identifier, ty: ResolvedType) {
        self.locals.insert(identifier, ty);
    }

    /// Get the type of the variable.
    pub(super) fn get_variable(&self, identifier: &Identifier) -> Option<&ResolvedType> {
        self.locals.get(identifier)
    }

    /// Resolve a type, reporting every undefined alias and replacing it with `!`.
    ///
    /// This is the only place where analysis creates `!`, so every `!` has a reported error.
    pub(super) fn resolve_or_never(
        &mut self,
        ty: &AliasedType,
        span: impl Into<Span>,
    ) -> ResolvedType {
        let mut errors = Vec::new();
        let resolved = ty
            .resolve(|name| {
                Ok::<_, Infallible>(self.modules.get_alias(name).unwrap_or_else(|error| {
                    errors.push(error);
                    ResolvedType::never()
                }))
            })
            .unwrap_or_else(|never| match never {});

        let span = span.into();
        for error in errors {
            self.report(error.with_span(span));
        }

        resolved
    }

    /// Insert a type alias into the current module scope.
    ///
    /// ## Errors
    ///
    /// * [`Error::RedefinedAlias`]: The alias name is already defined in the current scope.
    pub(super) fn insert_alias(&mut self, alias: parse::TypeAlias) -> Result<(), Error> {
        self.modules.check_alias_free(alias.name())?;

        let resolved = self.resolve_or_never(alias.ty(), &alias);

        self.modules
            .insert_alias(alias.name().clone(), resolved, alias.visibility().clone());

        Ok(())
    }

    pub(super) fn insert_parameter(
        &mut self,
        name: TemplateProgramWitness,
        ty: ResolvedType,
    ) -> Result<(), Error> {
        self.inputs.insert_parameter(name, ty)
    }

    /// Insert a witness into the global map.
    ///
    /// ## Errors
    ///
    /// * [`Error::WitnessOutsideMain`] The current scope is not inside the main function.
    /// * [`Error::WitnessReused`] A witness with the same name has already been defined.
    pub(super) fn insert_witness(
        &mut self,
        name: TemplateProgramWitness,
        ty: ResolvedType,
    ) -> Result<(), Error> {
        if !self.is_main {
            return Err(Error::WitnessOutsideMain);
        }

        self.inputs.insert_witness(name, ty)
    }

    /// Consume the scope and build the analyzed program with the given `main` body.
    pub(super) fn try_into_program(
        mut self,
        main: Result<Expression, Failure>,
        diagnostics: &mut DiagnosticManager,
    ) -> Option<Program> {
        let main = main.map_err(|failure| self.report(failure));
        match main {
            Ok(main) if self.diagnostics.is_empty() => Some(self.inputs.into_program(main)),
            _ => {
                diagnostics.extend(self.diagnostics);
                None
            }
        }
    }

    pub(super) fn track_call<S: AsRef<Span>>(&mut self, span: &S, name: TrackedCallName) {
        self.inputs.track_call(span, name);
    }
}

#[cfg(test)]
mod scope_balance_tests {
    use super::*;

    #[test]
    fn scopes_are_restored_after_failed_analysis() {
        let mut scope = Scope::new(Box::new(ElementsJetHinter));

        scope.locals.enter_block();
        let result: Result<(), ()> = scope.in_block(|_| Err(()));
        assert!(result.is_err());
        assert_eq!(scope.locals.depth(), 1);
        scope.locals.exit_block();

        let result: Result<(), ()> = scope.in_main(|_| Err(()));
        assert!(result.is_err());
        assert!(!scope.is_main);
        assert!(scope.is_outside_function());

        let result: Result<(), ()> = scope
            .in_module(
                ModuleName::from_str_unchecked("module"),
                Visibility::Private,
                |_| Err(()),
            )
            .expect("module entry succeeds");
        assert!(result.is_err());
        assert!(scope.module_path().is_empty());
    }
}
