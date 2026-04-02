use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::num::NonZeroUsize;
use std::str::FromStr;
use std::sync::Arc;

use either::Either;
use miniscript::iter::{Tree, TreeLike};
use simplicity::jet::Elements;

use crate::debug::{CallTracker, DebugSymbols, TrackedCallName};
use crate::error::{Error, RichError, Span, WithSpan};
use crate::num::{NonZeroPow2Usize, Pow2Usize};
use crate::parse::MatchPattern;
use crate::pattern::Pattern;
use crate::str::{AliasName, FunctionName, Identifier, ModuleName, WitnessName};
use crate::types::{
    AliasedType, ResolvedType, StructuralType, TypeConstructible, TypeDeconstructible, UIntType,
};
use crate::value::{UIntValue, Value};
use crate::warning::Warning;
use crate::witness::{Parameters, WitnessTypes, WitnessValues};
use crate::{impl_eq_hash, parse};

/// A program consists of the main function.
///
/// Other items such as custom functions or type aliases
/// are resolved during the creation of the AST.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Program {
    main: Expression,
    parameters: Parameters,
    witness_types: WitnessTypes,
    call_tracker: Arc<CallTracker>,
}

impl Program {
    /// Access the main function.
    ///
    /// There is exactly one main function for each program.
    pub fn main(&self) -> &Expression {
        &self.main
    }

    /// Access the parameters of the program.
    pub fn parameters(&self) -> &Parameters {
        &self.parameters
    }

    /// Access the witness types of the program.
    pub fn witness_types(&self) -> &WitnessTypes {
        &self.witness_types
    }

    /// Access the debug symbols of the program.
    pub fn debug_symbols(&self, file: &str) -> DebugSymbols {
        self.call_tracker.with_file(file)
    }

    /// Access the tracker of function calls.
    pub(crate) fn call_tracker(&self) -> &Arc<CallTracker> {
        &self.call_tracker
    }
}

/// An item is a component of a program.
///
/// All items except for the main function are resolved during the creation of the AST.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Item {
    /// A type alias.
    ///
    /// A stub because the alias was resolved during the creation of the AST.
    TypeAlias,
    /// A function.
    Function(Function),
    /// A module, which is ignored.
    Module,
}

/// Definition of a function.
///
/// All functions except for the main function are resolved during the creation of the AST.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Function {
    /// A custom function.
    ///
    /// A stub because the definition of the function was moved to its calls in the main function.
    Custom,
    /// The main function.
    ///
    /// An expression that takes no inputs (unit) and that produces no output (unit).
    /// The expression may panic midway through, signalling failure.
    /// Otherwise, the expression signals success.
    ///
    /// This expression is evaluated when the program is run.
    Main(Expression),
}

/// A statement is a component of a block expression.
///
/// Statements can define variables or run validating expressions,
/// but they never return values.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Statement {
    /// Variable assignment.
    Assignment(Assignment),
    /// Expression that returns nothing (the unit value).
    Expression(Expression),
}

/// Assignment of a value to a variable identifier.
#[derive(Clone, Debug)]
pub struct Assignment {
    pattern: Pattern,
    expression: Expression,
    span: Span,
}

impl Assignment {
    /// Access the pattern of the assignment.
    pub fn pattern(&self) -> &Pattern {
        &self.pattern
    }

    /// Access the expression of the assignment.
    pub fn expression(&self) -> &Expression {
        &self.expression
    }

    /// Access the span of the assignment.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(Assignment; pattern, expression);

/// An expression returns a value.
#[derive(Clone, Debug)]
pub struct Expression {
    inner: ExpressionInner,
    ty: ResolvedType,
    span: Span,
}

impl_eq_hash!(Expression; inner, ty);

impl Expression {
    /// Access the inner expression.
    pub fn inner(&self) -> &ExpressionInner {
        &self.inner
    }

    /// Access the type of the expression.
    pub fn ty(&self) -> &ResolvedType {
        &self.ty
    }

    /// Access the span of the expression.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

/// Variant of an expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum ExpressionInner {
    /// A single expression directly returns a value.
    Single(SingleExpression),
    /// A block expression first executes a series of statements inside a local scope.
    /// Then, the block returns the value of its final expression.
    /// The block returns nothing (unit) if there is no final expression.
    Block(Arc<[Statement]>, Option<Arc<Expression>>),
}

/// A single expression directly returns its value.
#[derive(Clone, Debug)]
pub struct SingleExpression {
    inner: SingleExpressionInner,
    ty: ResolvedType,
    span: Span,
}

impl SingleExpression {
    /// Create a tuple expression from the given arguments and span.
    pub fn tuple(args: Arc<[Expression]>, span: Span) -> Self {
        let ty = ResolvedType::tuple(
            args.iter()
                .map(Expression::ty)
                .cloned()
                .collect::<Vec<ResolvedType>>(),
        );
        let inner = SingleExpressionInner::Tuple(args);
        Self { inner, ty, span }
    }

    /// Access the inner expression.
    pub fn inner(&self) -> &SingleExpressionInner {
        &self.inner
    }

    /// Access the type of the expression.
    pub fn ty(&self) -> &ResolvedType {
        &self.ty
    }

    /// Access the span of the expression.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(SingleExpression; inner, ty);

/// Variant of a single expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum SingleExpressionInner {
    /// Constant value.
    Constant(Value),
    /// Witness value.
    Witness(WitnessName),
    /// Parameter value.
    Parameter(WitnessName),
    /// Variable that has been assigned a value.
    Variable(Identifier),
    /// Expression in parentheses.
    Expression(Arc<Expression>),
    /// Tuple expression.
    Tuple(Arc<[Expression]>),
    /// Array expression.
    Array(Arc<[Expression]>),
    /// Bounded list of expressions.
    List(Arc<[Expression]>),
    /// Either expression.
    Either(Either<Arc<Expression>, Arc<Expression>>),
    /// Option expression.
    Option(Option<Arc<Expression>>),
    /// Call expression.
    Call(Call),
    /// Match expression.
    Match(Match),
}

/// Call of a user-defined or of a builtin function.
#[derive(Clone, Debug)]
pub struct Call {
    name: CallName,
    args: Arc<[Expression]>,
    span: Span,
}

impl Call {
    /// Access the name of the call.
    pub fn name(&self) -> &CallName {
        &self.name
    }

    /// Access the arguments of the call.
    pub fn args(&self) -> &Arc<[Expression]> {
        &self.args
    }

    /// Access the span of the call.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(Call; name, args);

/// Name of a called function.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum CallName {
    /// Elements jet.
    Jet(Elements),
    /// [`Either::unwrap_left`].
    UnwrapLeft(ResolvedType),
    /// [`Either::unwrap_right`].
    UnwrapRight(ResolvedType),
    /// [`Option::is_none`].
    IsNone(ResolvedType),
    /// [`Option::unwrap`].
    Unwrap,
    /// [`assert!`].
    Assert,
    /// [`panic!`] without error message.
    Panic,
    /// [`dbg!`].
    Debug,
    /// Cast from the given source type.
    TypeCast(ResolvedType),
    /// A custom function that was defined previously.
    ///
    /// We effectively copy the function body into every call of the function.
    /// We use [`Arc`] for cheap clones during this process.
    Custom(CustomFunction),
    /// Fold of a bounded list with the given function.
    Fold(CustomFunction, NonZeroPow2Usize),
    /// Fold of an array with the given function.
    ArrayFold(CustomFunction, NonZeroUsize),
    /// Loop over the given function a bounded number of times until it returns success.
    ForWhile(CustomFunction, Pow2Usize),
}

/// Definition of a custom function.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct CustomFunction {
    params: Arc<[FunctionParam]>,
    body: Arc<Expression>,
}

impl CustomFunction {
    /// Access the identifiers of the parameters of the function.
    pub fn params(&self) -> &[FunctionParam] {
        &self.params
    }

    /// Access the body of the function.
    pub fn body(&self) -> &Expression {
        &self.body
    }

    /// Return a pattern for the parameters of the function.
    pub fn params_pattern(&self) -> Pattern {
        Pattern::tuple(
            self.params()
                .iter()
                .map(FunctionParam::identifier)
                .cloned()
                .map(Pattern::Identifier),
        )
    }
}

/// Parameter of a function.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct FunctionParam {
    identifier: Identifier,
    ty: ResolvedType,
}

impl FunctionParam {
    /// Access the identifier of the parameter.
    pub fn identifier(&self) -> &Identifier {
        &self.identifier
    }

    /// Access the type of the parameter.
    pub fn ty(&self) -> &ResolvedType {
        &self.ty
    }
}

/// Match expression.
#[derive(Clone, Debug)]
pub struct Match {
    scrutinee: Arc<Expression>,
    left: MatchArm,
    right: MatchArm,
    span: Span,
}

impl Match {
    /// Access the expression whose output is destructed in the match statement.
    pub fn scrutinee(&self) -> &Expression {
        &self.scrutinee
    }

    /// Access the branch that handles structural left values.
    pub fn left(&self) -> &MatchArm {
        &self.left
    }

    /// Access the branch that handles structural right values.
    pub fn right(&self) -> &MatchArm {
        &self.right
    }

    /// Access the span of the match statement.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(Match; scrutinee, left, right);

/// Arm of a [`Match`] expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct MatchArm {
    pattern: MatchPattern,
    expression: Arc<Expression>,
}

impl MatchArm {
    /// Access the pattern of the match arm.
    pub fn pattern(&self) -> &MatchPattern {
        &self.pattern
    }

    /// Access the expression of the match arm.
    pub fn expression(&self) -> &Expression {
        &self.expression
    }
}

/// Item when analyzing modules.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum ModuleItem {
    Ignored,
    Module(Module),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Module {
    name: ModuleName,
    assignments: Arc<[ModuleAssignment]>,
    span: Span,
}

impl Module {
    /// Access the assignments of the module.
    pub fn assignments(&self) -> &[ModuleAssignment] {
        &self.assignments
    }

    /// Access the span of the module.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct ModuleAssignment {
    name: WitnessName,
    value: Value,
    span: Span,
}

impl ModuleAssignment {
    /// Access the assigned witness name.
    pub fn name(&self) -> &WitnessName {
        &self.name
    }

    /// Access the assigned witness value.
    pub fn value(&self) -> &Value {
        &self.value
    }

    /// Access the span of the module.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum ExprTree<'a> {
    Expression(&'a Expression),
    Block(&'a [Statement], &'a Option<Arc<Expression>>),
    Statement(&'a Statement),
    Assignment(&'a Assignment),
    Single(&'a SingleExpression),
    Call(&'a Call),
    Match(&'a Match),
}

impl TreeLike for ExprTree<'_> {
    fn as_node(&self) -> Tree<Self> {
        use SingleExpressionInner as S;

        match self {
            Self::Expression(expr) => match expr.inner() {
                ExpressionInner::Block(statements, maybe_expr) => {
                    Tree::Unary(Self::Block(statements, maybe_expr))
                }
                ExpressionInner::Single(single) => Tree::Unary(Self::Single(single)),
            },
            Self::Block(statements, maybe_expr) => Tree::Nary(
                statements
                    .iter()
                    .map(Self::Statement)
                    .chain(maybe_expr.iter().map(Arc::as_ref).map(Self::Expression))
                    .collect(),
            ),
            Self::Statement(statement) => match statement {
                Statement::Assignment(assignment) => Tree::Unary(Self::Assignment(assignment)),
                Statement::Expression(expression) => Tree::Unary(Self::Expression(expression)),
            },
            Self::Assignment(assignment) => Tree::Unary(Self::Expression(assignment.expression())),
            Self::Single(single) => match single.inner() {
                S::Constant(_)
                | S::Witness(_)
                | S::Parameter(_)
                | S::Variable(_)
                | S::Option(None) => Tree::Nullary,
                S::Expression(l)
                | S::Either(Either::Left(l))
                | S::Either(Either::Right(l))
                | S::Option(Some(l)) => Tree::Unary(Self::Expression(l)),
                S::Tuple(elements) | S::Array(elements) | S::List(elements) => {
                    Tree::Nary(elements.iter().map(Self::Expression).collect())
                }
                S::Call(call) => Tree::Unary(Self::Call(call)),
                S::Match(match_) => Tree::Unary(Self::Match(match_)),
            },
            Self::Call(call) => Tree::Nary(call.args().iter().map(Self::Expression).collect()),
            Self::Match(match_) => Tree::Nary(Arc::new([
                Self::Expression(match_.scrutinee()),
                Self::Expression(match_.left().expression()),
                Self::Expression(match_.right().expression()),
            ])),
        }
    }
}

/// Scope for generating the abstract syntax tree.
///
/// The scope is used for:
/// 1. Assigning types to each variable
/// 2. Resolving type aliases
/// 3. Assigning types to each witness expression
/// 4. Resolving calls to custom functions
#[derive(Clone, Debug, Eq, PartialEq, Default)]
struct Scope {
    variables: Vec<HashMap<Identifier, ResolvedType>>,
    /// Spans of variables bound via `let` assignment patterns, per scope level.
    bound_spans: Vec<HashMap<Identifier, Span>>,
    /// Variables that have been referenced (used) in each scope level.
    used_variables: Vec<HashSet<Identifier>>,
    aliases: HashMap<AliasName, ResolvedType>,
    parameters: HashMap<WitnessName, ResolvedType>,
    witnesses: HashMap<WitnessName, ResolvedType>,
    functions: HashMap<FunctionName, CustomFunction>,
    is_main: bool,
    call_tracker: CallTracker,
}

impl Scope {
    /// Check if the current scope is topmost.
    pub fn is_topmost(&self) -> bool {
        self.variables.is_empty()
    }

    /// Push a new scope onto the stack.
    pub fn push_scope(&mut self) {
        self.variables.push(HashMap::new());
        self.bound_spans.push(HashMap::new());
        self.used_variables.push(HashSet::new());
    }

    /// Push the scope of the main function onto the stack.
    ///
    /// ## Panics
    ///
    /// - The current scope is already inside the main function.
    /// - The current scope is not topmost.
    pub fn push_main_scope(&mut self) {
        assert!(!self.is_main, "Already inside main function");
        assert!(self.is_topmost(), "Current scope is not topmost");
        self.push_scope();
        self.is_main = true;
    }

    /// Pop the current scope from the stack.
    ///
    /// Returns warnings for any variables that were bound but never used.
    ///
    /// ## Panics
    ///
    /// The stack is empty.
    pub fn pop_scope(&mut self) -> Vec<Warning> {
        self.variables.pop().expect("Stack is empty");
        let bound = self.bound_spans.pop().expect("Stack is empty");
        let used = self.used_variables.pop().expect("Stack is empty");
        let mut unused: Vec<(Identifier, Span)> = bound
            .into_iter()
            .filter(|(id, _)| !used.contains(id) && !id.as_inner().starts_with('_'))
            .collect();
        unused.sort_by_key(|(_, span)| span.start);
        unused
            .into_iter()
            .map(|(id, span)| Warning::variable_unused(id, span))
            .collect()
    }

    /// Pop the scope of the main function from the stack.
    ///
    /// Returns warnings for any variables that were bound but never used.
    ///
    /// ## Panics
    ///
    /// - The current scope is not inside the main function.
    /// - The current scope is not nested in the topmost scope.
    pub fn pop_main_scope(&mut self) -> Vec<Warning> {
        assert!(self.is_main, "Current scope is not inside main function");
        let warnings = self.pop_scope();
        self.is_main = false;
        assert!(
            self.is_topmost(),
            "Current scope is not nested in topmost scope"
        );
        warnings
    }

    /// Insert a variable into the current scope **without** tracking it for unused-variable warnings.
    ///
    /// Use this only when re-inserting a variable that is being referenced (i.e. consumed in an
    /// expression), where the reference itself is the evidence of use. For new binding sites
    /// (`let`, function parameters, match arm patterns) use [`bind_variable`] instead so that
    /// unused-variable warnings are emitted correctly.
    ///
    /// [`bind_variable`]: Scope::bind_variable
    ///
    /// ## Panics
    ///
    /// The stack is empty.
    pub fn insert_variable_usage(&mut self, identifier: Identifier, ty: ResolvedType) {
        self.variables
            .last_mut()
            .expect("Stack is empty")
            .insert(identifier, ty);
    }

    /// Bind a variable from a new binding site (`let`, function parameter, match arm pattern),
    /// tracking its span so an unused-variable warning can be emitted if it is never referenced.
    ///
    /// ## Panics
    ///
    /// The stack is empty.
    pub fn bind_variable(&mut self, identifier: Identifier, ty: ResolvedType, span: Span) {
        self.insert_variable_usage(identifier.clone(), ty);
        self.bound_spans
            .last_mut()
            .expect("Stack is empty")
            .insert(identifier, span);
    }

    /// Mark a variable as used in the scope where it was bound.
    pub fn mark_variable_used(&mut self, identifier: &Identifier) {
        for (scope_vars, used) in self
            .variables
            .iter()
            .zip(self.used_variables.iter_mut())
            .rev()
        {
            if scope_vars.contains_key(identifier) {
                used.insert(identifier.clone());
                return;
            }
        }
    }

    /// Get the type of the variable.
    pub fn get_variable(&self, identifier: &Identifier) -> Option<&ResolvedType> {
        self.variables
            .iter()
            .rev()
            .find_map(|scope| scope.get(identifier))
    }

    /// Resolve a type with aliases to a type without aliases.
    ///
    /// ## Errors
    ///
    /// There are any undefined aliases.
    pub fn resolve(&self, ty: &AliasedType) -> Result<ResolvedType, Error> {
        let get_alias =
            |name: &AliasName| -> Option<ResolvedType> { self.aliases.get(name).cloned() };
        ty.resolve(get_alias).map_err(Error::UndefinedAlias)
    }

    /// Push a type alias into the global map.
    ///
    /// ## Errors
    ///
    /// There are any undefined aliases.
    pub fn insert_alias(&mut self, name: AliasName, ty: AliasedType) -> Result<(), Error> {
        if self.aliases.contains_key(&name) {
            return Err(Error::RedefinedAlias(name));
        }

        let _ = self.aliases.insert(name, self.resolve(&ty)?);
        Ok(())
    }

    /// Insert a parameter into the global map.
    ///
    /// ## Errors
    ///
    /// A parameter of the same name has already been defined as a different type.
    pub fn insert_parameter(&mut self, name: WitnessName, ty: ResolvedType) -> Result<(), Error> {
        match self.parameters.entry(name.clone()) {
            Entry::Occupied(entry) if entry.get() == &ty => Ok(()),
            Entry::Occupied(entry) => Err(Error::ExpressionTypeMismatch(entry.get().clone(), ty)),
            Entry::Vacant(entry) => {
                entry.insert(ty);
                Ok(())
            }
        }
    }

    /// Insert a witness into the global map.
    ///
    /// ## Errors
    ///
    /// - The current scope is not inside the main function.
    /// - A witness with the same name has already been defined.
    pub fn insert_witness(&mut self, name: WitnessName, ty: ResolvedType) -> Result<(), Error> {
        if !self.is_main {
            return Err(Error::WitnessOutsideMain);
        }

        match self.witnesses.entry(name.clone()) {
            Entry::Occupied(_) => Err(Error::WitnessReused(name)),
            Entry::Vacant(entry) => {
                entry.insert(ty);
                Ok(())
            }
        }
    }

    /// Consume the scope and return its contents:
    ///
    /// 1. The map of parameter types.
    /// 2. The map of witness types.
    /// 3. The function call tracker.
    pub fn destruct(self) -> (Parameters, WitnessTypes, CallTracker) {
        (
            Parameters::from(self.parameters),
            WitnessTypes::from(self.witnesses),
            self.call_tracker,
        )
    }

    /// Insert a custom function into the global map.
    ///
    /// ## Errors
    ///
    /// The function has already been defined.
    pub fn insert_function(
        &mut self,
        name: FunctionName,
        function: CustomFunction,
    ) -> Result<(), Error> {
        match self.functions.entry(name.clone()) {
            Entry::Occupied(_) => Err(Error::FunctionRedefined(name)),
            Entry::Vacant(entry) => {
                entry.insert(function);
                Ok(())
            }
        }
    }

    /// Get the definition of a custom function.
    pub fn get_function(&self, name: &FunctionName) -> Option<&CustomFunction> {
        self.functions.get(name)
    }

    /// Track a call expression with its span.
    pub fn track_call<S: AsRef<Span>>(&mut self, span: &S, name: TrackedCallName) {
        self.call_tracker.track_call(*span.as_ref(), name);
    }
}

/// Part of the abstract syntax tree that can be generated from a precursor in the parse tree.
trait AbstractSyntaxTree: Sized {
    /// Component of the parse tree.
    type From;

    /// Analyze a component from the parse tree
    /// and convert it into a component of the abstract syntax tree.
    ///
    /// Check if the analyzed expression is of the expected type.
    /// Statements return no values so their expected type is always unit.
    fn analyze(
        from: &Self::From,
        ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<(Self, Vec<Warning>), RichError>;
}

impl Program {
    pub fn analyze(from: &parse::Program) -> Result<(Self, Vec<Warning>), RichError> {
        let unit = ResolvedType::unit();
        let mut scope = Scope::default();
        let items: Vec<(Item, Vec<Warning>)> = from
            .items()
            .iter()
            .map(|s| Item::analyze(s, &unit, &mut scope))
            .collect::<Result<_, RichError>>()?;
        debug_assert!(scope.is_topmost());
        let (parameters, witness_types, call_tracker) = scope.destruct();

        let mut all_warnings: Vec<Warning> = vec![];
        let mut main_expr = None;
        let mut main_seen = false;
        for (item, mut warnings) in items {
            all_warnings.append(&mut warnings);
            if let Item::Function(Function::Main(expr)) = item {
                if main_seen {
                    return Err(Error::FunctionRedefined(FunctionName::main())).with_span(from);
                }
                main_seen = true;
                main_expr = Some(expr);
            }
        }
        let main = main_expr.ok_or(Error::MainRequired).with_span(from)?;

        Ok((
            Self {
                main,
                parameters,
                witness_types,
                call_tracker: Arc::new(call_tracker),
            },
            all_warnings,
        ))
    }
}

impl AbstractSyntaxTree for Item {
    type From = parse::Item;

    fn analyze(
        from: &Self::From,
        ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<(Self, Vec<Warning>), RichError> {
        assert!(ty.is_unit(), "Items cannot return anything");
        assert!(scope.is_topmost(), "Items live in the topmost scope only");

        match from {
            parse::Item::TypeAlias(alias) => {
                scope
                    .insert_alias(alias.name().clone(), alias.ty().clone())
                    .with_span(alias)?;
                Ok((Self::TypeAlias, vec![]))
            }
            parse::Item::Function(function) => Function::analyze(function, ty, scope)
                .map(|(f, warnings)| (Self::Function(f), warnings)),
            parse::Item::Module => Ok((Self::Module, vec![])),
        }
    }
}

impl AbstractSyntaxTree for Function {
    type From = parse::Function;

    fn analyze(
        from: &Self::From,
        ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<(Self, Vec<Warning>), RichError> {
        assert!(ty.is_unit(), "Function definitions cannot return anything");
        assert!(scope.is_topmost(), "Items live in the topmost scope only");

        if from.name().as_inner() != "main" {
            let params = from
                .params()
                .iter()
                .map(|param| {
                    let identifier = param.identifier().clone();
                    let ty = scope.resolve(param.ty())?;
                    Ok(FunctionParam { identifier, ty })
                })
                .collect::<Result<Arc<[FunctionParam]>, Error>>()
                .with_span(from)?;
            let ret = from
                .ret()
                .as_ref()
                .map(|aliased| scope.resolve(aliased).with_span(from))
                .transpose()?
                .unwrap_or_else(ResolvedType::unit);
            scope.push_scope();
            for (param, parse_param) in params.iter().zip(from.params().iter()) {
                scope.bind_variable(
                    param.identifier().clone(),
                    param.ty().clone(),
                    parse_param.span(),
                );
            }
            let (body_expr, mut warnings) = Expression::analyze(from.body(), &ret, scope)?;
            let body = Arc::new(body_expr);
            warnings.extend(scope.pop_scope());
            debug_assert!(scope.is_topmost());
            let function = CustomFunction { params, body };
            scope
                .insert_function(from.name().clone(), function)
                .with_span(from)?;

            return Ok((Self::Custom, warnings));
        }

        if !from.params().is_empty() {
            return Err(Error::MainNoInputs).with_span(from);
        }
        if let Some(aliased) = from.ret() {
            let resolved = scope.resolve(aliased).with_span(from)?;
            if !resolved.is_unit() {
                return Err(Error::MainNoOutput).with_span(from);
            }
        }

        scope.push_main_scope();
        let (body, mut warnings) = Expression::analyze(from.body(), ty, scope)?;
        warnings.extend(scope.pop_main_scope());
        Ok((Self::Main(body), warnings))
    }
}

impl AbstractSyntaxTree for Statement {
    type From = parse::Statement;

    fn analyze(
        from: &Self::From,
        ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<(Self, Vec<Warning>), RichError> {
        assert!(ty.is_unit(), "Statements cannot return anything");
        match from {
            parse::Statement::Assignment(assignment) => Assignment::analyze(assignment, ty, scope)
                .map(|(a, warnings)| (Self::Assignment(a), warnings)),
            parse::Statement::Expression(expression) => Expression::analyze(expression, ty, scope)
                .map(|(e, warnings)| (Self::Expression(e), warnings)),
        }
    }
}

impl AbstractSyntaxTree for Assignment {
    type From = parse::Assignment;

    fn analyze(
        from: &Self::From,
        ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<(Self, Vec<Warning>), RichError> {
        assert!(ty.is_unit(), "Assignments cannot return anything");
        // The assignment is a statement that returns nothing.
        //
        // However, the expression evaluated in the assignment does have a type,
        // namely the type specified in the assignment.
        let ty_expr = scope.resolve(from.ty()).with_span(from)?;
        let (expression, warnings) = Expression::analyze(from.expression(), &ty_expr, scope)?;
        let typed_variables = from.pattern().is_of_type(&ty_expr).with_span(from)?;
        let pattern_span = from.pattern_span();
        for (identifier, ty) in typed_variables {
            scope.bind_variable(identifier, ty, pattern_span);
        }

        Ok((
            Self {
                pattern: from.pattern().clone(),
                expression,
                span: *from.as_ref(),
            },
            warnings,
        ))
    }
}

impl Expression {
    /// Analyze an expression from the parse tree in a const context without predefined variables.
    ///
    /// Check if the expression is of the given type.
    ///
    /// ## Const evaluation
    ///
    /// The returned expression might not be evaluable at compile time.
    /// The details depend on the current state of the SimplicityHL compiler.
    pub fn analyze_const(from: &parse::Expression, ty: &ResolvedType) -> Result<Self, RichError> {
        let mut empty_scope = Scope::default();
        // Constant expressions are literal values — no `let` bindings, so no
        // unused-variable warnings can arise. Warnings are intentionally discarded here.
        Self::analyze(from, ty, &mut empty_scope).map(|(e, _warnings)| e)
    }
}

impl AbstractSyntaxTree for Expression {
    type From = parse::Expression;

    fn analyze(
        from: &Self::From,
        ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<(Self, Vec<Warning>), RichError> {
        match from.inner() {
            parse::ExpressionInner::Single(single) => {
                let (ast_single, warnings) = SingleExpression::analyze(single, ty, scope)?;
                Ok((
                    Self {
                        ty: ty.clone(),
                        inner: ExpressionInner::Single(ast_single),
                        span: *from.as_ref(),
                    },
                    warnings,
                ))
            }
            parse::ExpressionInner::Block(statements, expression) => {
                scope.push_scope();
                let ast_statements_with_warnings = statements
                    .iter()
                    .map(|s| Statement::analyze(s, &ResolvedType::unit(), scope))
                    .collect::<Result<Vec<(Statement, Vec<Warning>)>, RichError>>()?;
                let (ast_expression, expr_warnings) = match expression {
                    Some(expression) => Expression::analyze(expression, ty, scope)
                        .map(|(e, warnings)| (Some(Arc::new(e)), warnings)),
                    None if ty.is_unit() => Ok((None, vec![])),
                    None => Err(Error::ExpressionTypeMismatch(
                        ty.clone(),
                        ResolvedType::unit(),
                    ))
                    .with_span(from),
                }?;
                let mut all_warnings: Vec<Warning> = scope.pop_scope();

                let (all_statements, stmt_warnings): (Vec<_>, Vec<_>) =
                    ast_statements_with_warnings.into_iter().unzip();
                all_warnings.extend(stmt_warnings.into_iter().flatten());
                all_warnings.extend(expr_warnings);

                Ok((
                    Self {
                        ty: ty.clone(),
                        inner: ExpressionInner::Block(all_statements.into(), ast_expression),
                        span: *from.as_ref(),
                    },
                    all_warnings,
                ))
            }
        }
    }
}

impl AbstractSyntaxTree for SingleExpression {
    type From = parse::SingleExpression;

    fn analyze(
        from: &Self::From,
        ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<(Self, Vec<Warning>), RichError> {
        let (inner, warnings) = match from.inner() {
            parse::SingleExpressionInner::Boolean(bit) => {
                if !ty.is_boolean() {
                    return Err(Error::ExpressionTypeMismatch(
                        ty.clone(),
                        ResolvedType::boolean(),
                    ))
                    .with_span(from);
                }
                (SingleExpressionInner::Constant(Value::from(*bit)), vec![])
            }
            parse::SingleExpressionInner::Decimal(decimal) => {
                let ty = ty
                    .as_integer()
                    .ok_or(Error::ExpressionUnexpectedType(ty.clone()))
                    .with_span(from)?;
                (
                    UIntValue::parse_decimal(decimal, ty)
                        .with_span(from)
                        .map(Value::from)
                        .map(SingleExpressionInner::Constant)?,
                    vec![],
                )
            }
            parse::SingleExpressionInner::Binary(bits) => {
                let ty = ty
                    .as_integer()
                    .ok_or(Error::ExpressionUnexpectedType(ty.clone()))
                    .with_span(from)?;
                let value = UIntValue::parse_binary(bits, ty).with_span(from)?;
                (SingleExpressionInner::Constant(Value::from(value)), vec![])
            }
            parse::SingleExpressionInner::Hexadecimal(bytes) => {
                let value = Value::parse_hexadecimal(bytes, ty).with_span(from)?;
                (SingleExpressionInner::Constant(value), vec![])
            }
            parse::SingleExpressionInner::Witness(name) => {
                scope
                    .insert_witness(name.clone(), ty.clone())
                    .with_span(from)?;
                (SingleExpressionInner::Witness(name.clone()), vec![])
            }
            parse::SingleExpressionInner::Parameter(name) => {
                scope
                    .insert_parameter(name.shallow_clone(), ty.clone())
                    .with_span(from)?;
                (
                    SingleExpressionInner::Parameter(name.shallow_clone()),
                    vec![],
                )
            }
            parse::SingleExpressionInner::Variable(identifier) => {
                let bound_ty = scope
                    .get_variable(identifier)
                    .ok_or(Error::UndefinedVariable(identifier.clone()))
                    .with_span(from)?;
                if ty != bound_ty {
                    return Err(Error::ExpressionTypeMismatch(ty.clone(), bound_ty.clone()))
                        .with_span(from);
                }
                scope.mark_variable_used(identifier);
                scope.insert_variable_usage(identifier.clone(), ty.clone());
                (SingleExpressionInner::Variable(identifier.clone()), vec![])
            }
            parse::SingleExpressionInner::Expression(parse) => {
                Expression::analyze(parse, ty, scope).map(|(e, warnings)| {
                    (SingleExpressionInner::Expression(Arc::new(e)), warnings)
                })?
            }
            parse::SingleExpressionInner::Tuple(tuple) => {
                let types = ty
                    .as_tuple()
                    .ok_or(Error::ExpressionUnexpectedType(ty.clone()))
                    .with_span(from)?;
                if tuple.len() != types.len() {
                    return Err(Error::ExpressionUnexpectedType(ty.clone())).with_span(from);
                }
                let results = tuple
                    .iter()
                    .zip(types.iter())
                    .map(|(el_parse, el_ty)| Expression::analyze(el_parse, el_ty, scope))
                    .collect::<Result<Vec<(Expression, Vec<Warning>)>, RichError>>()?;
                let (all_expressions, warnings): (Vec<_>, Vec<_>) = results.into_iter().unzip();
                let all_warnings: Vec<Warning> = warnings.into_iter().flatten().collect();
                (
                    SingleExpressionInner::Tuple(all_expressions.into()),
                    all_warnings,
                )
            }
            parse::SingleExpressionInner::Array(array) => {
                let (el_ty, size) = ty
                    .as_array()
                    .ok_or(Error::ExpressionUnexpectedType(ty.clone()))
                    .with_span(from)?;
                if array.len() != size {
                    return Err(Error::ExpressionUnexpectedType(ty.clone())).with_span(from);
                }
                let results = array
                    .iter()
                    .map(|el_parse| Expression::analyze(el_parse, el_ty, scope))
                    .collect::<Result<Vec<(Expression, Vec<Warning>)>, RichError>>()?;
                let (all_expressions, warnings): (Vec<_>, Vec<_>) = results.into_iter().unzip();
                let all_warnings: Vec<Warning> = warnings.into_iter().flatten().collect();
                (
                    SingleExpressionInner::Array(all_expressions.into()),
                    all_warnings,
                )
            }
            parse::SingleExpressionInner::List(list) => {
                let (el_ty, bound) = ty
                    .as_list()
                    .ok_or(Error::ExpressionUnexpectedType(ty.clone()))
                    .with_span(from)?;
                if bound.get() <= list.len() {
                    return Err(Error::ExpressionUnexpectedType(ty.clone())).with_span(from);
                }
                let results = list
                    .iter()
                    .map(|e| Expression::analyze(e, el_ty, scope))
                    .collect::<Result<Vec<(Expression, Vec<Warning>)>, RichError>>()?;
                let (all_expressions, warnings): (Vec<_>, Vec<_>) = results.into_iter().unzip();
                let all_warnings: Vec<Warning> = warnings.into_iter().flatten().collect();
                (
                    SingleExpressionInner::List(all_expressions.into()),
                    all_warnings,
                )
            }
            parse::SingleExpressionInner::Either(either) => {
                let (ty_l, ty_r) = ty
                    .as_either()
                    .ok_or(Error::ExpressionUnexpectedType(ty.clone()))
                    .with_span(from)?;
                match either {
                    Either::Left(parse_l) => Expression::analyze(parse_l, ty_l, scope)
                        .map(|(l, warnings)| (Either::Left(Arc::new(l)), warnings)),
                    Either::Right(parse_r) => Expression::analyze(parse_r, ty_r, scope)
                        .map(|(r, warnings)| (Either::Right(Arc::new(r)), warnings)),
                }
                .map(|(e, warnings)| (SingleExpressionInner::Either(e), warnings))?
            }
            parse::SingleExpressionInner::Option(maybe_parse) => {
                let ty = ty
                    .as_option()
                    .ok_or(Error::ExpressionUnexpectedType(ty.clone()))
                    .with_span(from)?;
                match maybe_parse {
                    Some(parse) => Expression::analyze(parse, ty, scope)
                        .map(|(e, warnings)| (Some(Arc::new(e)), warnings)),
                    None => Ok((None, vec![])),
                }
                .map(|(o, warnings)| (SingleExpressionInner::Option(o), warnings))?
            }
            parse::SingleExpressionInner::Call(call) => Call::analyze(call, ty, scope)
                .map(|(c, warnings)| (SingleExpressionInner::Call(c), warnings))?,
            parse::SingleExpressionInner::Match(match_) => Match::analyze(match_, ty, scope)
                .map(|(m, warnings)| (SingleExpressionInner::Match(m), warnings))?,
        };

        Ok((
            Self {
                inner,
                ty: ty.clone(),
                span: *from.as_ref(),
            },
            warnings,
        ))
    }
}

impl AbstractSyntaxTree for Call {
    type From = parse::Call;

    fn analyze(
        from: &Self::From,
        ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<(Self, Vec<Warning>), RichError> {
        fn check_argument_types(
            parse_args: &[parse::Expression],
            expected_tys: &[ResolvedType],
        ) -> Result<(), Error> {
            if parse_args.len() == expected_tys.len() {
                Ok(())
            } else {
                Err(Error::InvalidNumberOfArguments(
                    expected_tys.len(),
                    parse_args.len(),
                ))
            }
        }

        fn check_output_type(
            observed_ty: &ResolvedType,
            expected_ty: &ResolvedType,
        ) -> Result<(), Error> {
            if observed_ty == expected_ty {
                Ok(())
            } else {
                Err(Error::ExpressionTypeMismatch(
                    expected_ty.clone(),
                    observed_ty.clone(),
                ))
            }
        }

        fn analyze_arguments(
            parse_args: &[parse::Expression],
            args_tys: &[ResolvedType],
            scope: &mut Scope,
        ) -> Result<(Arc<[Expression]>, Vec<Warning>), RichError> {
            let results = parse_args
                .iter()
                .zip(args_tys.iter())
                .map(|(arg_parse, arg_ty)| Expression::analyze(arg_parse, arg_ty, scope))
                .collect::<Result<Vec<(Expression, Vec<Warning>)>, RichError>>()?;
            let (all_args, warnings): (Vec<_>, Vec<_>) = results.into_iter().unzip();
            let all_warnings: Vec<Warning> = warnings.into_iter().flatten().collect();
            Ok((all_args.into(), all_warnings))
        }

        let (name, mut all_warnings) = CallName::analyze(from, ty, scope)?;
        let args = match name.clone() {
            CallName::Jet(jet) => {
                let args_tys = crate::jet::source_type(jet)
                    .iter()
                    .map(AliasedType::resolve_builtin)
                    .collect::<Result<Vec<ResolvedType>, AliasName>>()
                    .map_err(Error::UndefinedAlias)
                    .with_span(from)?;
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                let out_ty = crate::jet::target_type(jet)
                    .resolve_builtin()
                    .map_err(Error::UndefinedAlias)
                    .with_span(from)?;
                check_output_type(&out_ty, ty).with_span(from)?;
                scope.track_call(from, TrackedCallName::Jet);
                let (args, mut warnings) = analyze_arguments(from.args(), &args_tys, scope)?;
                all_warnings.append(&mut warnings);
                args
            }
            CallName::UnwrapLeft(right_ty) => {
                let args_tys = [ResolvedType::either(ty.clone(), right_ty)];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                let (args, mut warnings) = analyze_arguments(from.args(), &args_tys, scope)?;
                all_warnings.append(&mut warnings);
                let [arg_ty] = args_tys;
                scope.track_call(from, TrackedCallName::UnwrapLeft(arg_ty));
                args
            }
            CallName::UnwrapRight(left_ty) => {
                let args_tys = [ResolvedType::either(left_ty, ty.clone())];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                let (args, mut warnings) = analyze_arguments(from.args(), &args_tys, scope)?;
                all_warnings.append(&mut warnings);
                let [arg_ty] = args_tys;
                scope.track_call(from, TrackedCallName::UnwrapRight(arg_ty));
                args
            }
            CallName::IsNone(some_ty) => {
                let args_tys = [ResolvedType::option(some_ty)];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                let out_ty = ResolvedType::boolean();
                check_output_type(&out_ty, ty).with_span(from)?;
                let (args, mut warnings) = analyze_arguments(from.args(), &args_tys, scope)?;
                all_warnings.append(&mut warnings);
                args
            }
            CallName::Unwrap => {
                let args_tys = [ResolvedType::option(ty.clone())];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                scope.track_call(from, TrackedCallName::Unwrap);
                let (args, mut warnings) = analyze_arguments(from.args(), &args_tys, scope)?;
                all_warnings.append(&mut warnings);
                args
            }
            CallName::Assert => {
                let args_tys = [ResolvedType::boolean()];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                let out_ty = ResolvedType::unit();
                check_output_type(&out_ty, ty).with_span(from)?;
                scope.track_call(from, TrackedCallName::Assert);
                let (args, mut warnings) = analyze_arguments(from.args(), &args_tys, scope)?;
                all_warnings.append(&mut warnings);
                args
            }
            CallName::Panic => {
                let args_tys = [];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                // panic! allows every output type because it will never return anything
                scope.track_call(from, TrackedCallName::Panic);
                let (args, mut warnings) = analyze_arguments(from.args(), &args_tys, scope)?;
                all_warnings.append(&mut warnings);
                args
            }
            CallName::Debug => {
                let args_tys = [ty.clone()];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                let (args, mut warnings) = analyze_arguments(from.args(), &args_tys, scope)?;
                all_warnings.append(&mut warnings);
                let [arg_ty] = args_tys;
                scope.track_call(from, TrackedCallName::Debug(arg_ty));
                args
            }
            CallName::TypeCast(source) => {
                if StructuralType::from(&source) != StructuralType::from(ty) {
                    return Err(Error::InvalidCast(source, ty.clone())).with_span(from);
                }

                let args_tys = [source];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                let (args, mut warnings) = analyze_arguments(from.args(), &args_tys, scope)?;
                all_warnings.append(&mut warnings);
                args
            }
            CallName::Custom(function) => {
                let args_ty = function
                    .params()
                    .iter()
                    .map(FunctionParam::ty)
                    .cloned()
                    .collect::<Vec<ResolvedType>>();
                check_argument_types(from.args(), &args_ty).with_span(from)?;
                let out_ty = function.body().ty();
                check_output_type(out_ty, ty).with_span(from)?;
                let (args, mut warnings) = analyze_arguments(from.args(), &args_ty, scope)?;
                all_warnings.append(&mut warnings);
                args
            }
            CallName::Fold(function, bound) => {
                // A list fold has the signature:
                //   fold::<f, N>(list: List<E, N>, initial_accumulator: A) -> A
                // where
                //   fn f(element: E, accumulator: A) -> A
                let element_ty = function.params().first().expect("foldable function").ty();
                let list_ty = ResolvedType::list(element_ty.clone(), bound);
                let accumulator_ty = function
                    .params()
                    .get(1)
                    .expect("foldable function")
                    .ty()
                    .clone();
                let args_ty = [list_ty, accumulator_ty];

                check_argument_types(from.args(), &args_ty).with_span(from)?;
                let out_ty = function.body().ty();
                check_output_type(out_ty, ty).with_span(from)?;
                let (args, mut warnings) = analyze_arguments(from.args(), &args_ty, scope)?;
                all_warnings.append(&mut warnings);
                args
            }
            CallName::ArrayFold(function, size) => {
                // An array fold has the signature:
                //   array_fold::<f, N>(array: [E; N], initial_accumulator: A) -> A
                // where
                //   fn f(element: E, accumulator: A) -> A
                let element_ty = function.params().first().expect("foldable function").ty();
                let array_ty = ResolvedType::array(element_ty.clone(), size.get());
                let accumulator_ty = function
                    .params()
                    .get(1)
                    .expect("foldable function")
                    .ty()
                    .clone();
                let args_ty = [array_ty, accumulator_ty];

                check_argument_types(from.args(), &args_ty).with_span(from)?;
                let out_ty = function.body().ty();
                check_output_type(out_ty, ty).with_span(from)?;
                let (args, mut warnings) = analyze_arguments(from.args(), &args_ty, scope)?;
                all_warnings.append(&mut warnings);
                args
            }
            CallName::ForWhile(function, _bit_width) => {
                // A for-while loop has the signature:
                //   for_while::<f>(initial_accumulator: A, readonly_context: C) -> Either<B, A>
                // where
                //   fn f(accumulator: A, readonly_context: C, counter: u{N}) -> Either<B, A>
                //   N is a power of two
                let accumulator_ty = function
                    .params()
                    .first()
                    .expect("loopable function")
                    .ty()
                    .clone();
                let context_ty = function
                    .params()
                    .get(1)
                    .expect("loopable function")
                    .ty()
                    .clone();
                let args_ty = [accumulator_ty, context_ty];

                check_argument_types(from.args(), &args_ty).with_span(from)?;
                let out_ty = function.body().ty();
                check_output_type(out_ty, ty).with_span(from)?;
                let (args, mut warnings) = analyze_arguments(from.args(), &args_ty, scope)?;
                all_warnings.append(&mut warnings);
                args
            }
        };

        Ok((
            Self {
                name,
                args,
                span: *from.as_ref(),
            },
            all_warnings,
        ))
    }
}

impl AbstractSyntaxTree for CallName {
    // Take parse::Call, so we have access to the span for pretty errors
    type From = parse::Call;

    fn analyze(
        from: &Self::From,
        _ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<(Self, Vec<Warning>), RichError> {
        let name = match from.name() {
            parse::CallName::Jet(name) => match Elements::from_str(name.as_inner()) {
                Ok(Elements::CheckSigVerify | Elements::Verify) | Err(_) => {
                    return Err(Error::JetDoesNotExist(name.clone())).with_span(from);
                }
                Ok(jet) => Self::Jet(jet),
            },
            parse::CallName::UnwrapLeft(right_ty) => scope
                .resolve(right_ty)
                .map(Self::UnwrapLeft)
                .with_span(from)?,
            parse::CallName::UnwrapRight(left_ty) => scope
                .resolve(left_ty)
                .map(Self::UnwrapRight)
                .with_span(from)?,
            parse::CallName::IsNone(some_ty) => {
                scope.resolve(some_ty).map(Self::IsNone).with_span(from)?
            }
            parse::CallName::Unwrap => Self::Unwrap,
            parse::CallName::Assert => Self::Assert,
            parse::CallName::Panic => Self::Panic,
            parse::CallName::Debug => Self::Debug,
            parse::CallName::TypeCast(target) => {
                scope.resolve(target).map(Self::TypeCast).with_span(from)?
            }
            parse::CallName::Custom(name) => scope
                .get_function(name)
                .cloned()
                .map(Self::Custom)
                .ok_or(Error::FunctionUndefined(name.clone()))
                .with_span(from)?,
            parse::CallName::ArrayFold(name, size) => {
                let function = scope
                    .get_function(name)
                    .cloned()
                    .ok_or(Error::FunctionUndefined(name.clone()))
                    .with_span(from)?;
                // A function that is used in a array fold has the signature:
                //   fn f(element: E, accumulator: A) -> A
                if function.params().len() != 2 || function.params()[1].ty() != function.body().ty()
                {
                    return Err(Error::FunctionNotFoldable(name.clone())).with_span(from);
                }
                Self::ArrayFold(function, *size)
            }
            parse::CallName::Fold(name, bound) => {
                let function = scope
                    .get_function(name)
                    .cloned()
                    .ok_or(Error::FunctionUndefined(name.clone()))
                    .with_span(from)?;
                // A function that is used in a list fold has the signature:
                //   fn f(element: E, accumulator: A) -> A
                if function.params().len() != 2 || function.params()[1].ty() != function.body().ty()
                {
                    return Err(Error::FunctionNotFoldable(name.clone())).with_span(from);
                }
                Self::Fold(function, *bound)
            }
            parse::CallName::ForWhile(name) => {
                let function = scope
                    .get_function(name)
                    .cloned()
                    .ok_or(Error::FunctionUndefined(name.clone()))
                    .with_span(from)?;
                // A function that is used in a for-while loop has the signature:
                //   fn f(accumulator: A, readonly_context: C, counter: u{N}) -> Either<B, A>
                // where
                //   N is a power of two
                if function.params().len() != 3 {
                    return Err(Error::FunctionNotLoopable(name.clone())).with_span(from);
                }
                match function.body().ty().as_either() {
                    Some((_, out_r)) if out_r == function.params().first().unwrap().ty() => {}
                    _ => {
                        return Err(Error::FunctionNotLoopable(name.clone())).with_span(from);
                    }
                }
                // Disable loops for u32 or higher since no one will want to run
                // 2^32 = 4294967296 ≈ 4 billion iterations.
                // The resulting Simplicity program will not fit into a Bitcoin block.
                match function.params().get(2).unwrap().ty().as_integer() {
                    Some(
                        int_ty @ (UIntType::U1
                        | UIntType::U2
                        | UIntType::U4
                        | UIntType::U8
                        | UIntType::U16),
                    ) => Self::ForWhile(function, int_ty.bit_width()),
                    _ => return Err(Error::FunctionNotLoopable(name.clone())).with_span(from),
                }
            }
        };
        Ok((name, vec![]))
    }
}

impl AbstractSyntaxTree for Match {
    type From = parse::Match;

    fn analyze(
        from: &Self::From,
        ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<(Self, Vec<Warning>), RichError> {
        let scrutinee_ty = from.scrutinee_type();
        let scrutinee_ty = scope.resolve(&scrutinee_ty).with_span(from)?;
        let (scrutinee_expr, mut all_warnings) =
            Expression::analyze(from.scrutinee(), &scrutinee_ty, scope)?;
        let scrutinee = Arc::new(scrutinee_expr);

        scope.push_scope();
        if let Some((pat_l, ty_l)) = from.left().pattern().as_typed_pattern() {
            let ty_l = scope.resolve(ty_l).with_span(from)?;
            let typed_variables = pat_l.is_of_type(&ty_l).with_span(from)?;
            let span = from.left().pattern_span().unwrap_or(*from.as_ref());
            for (identifier, ty) in typed_variables {
                scope.bind_variable(identifier, ty, span);
            }
        }
        let (ast_l_expr, mut warnings_l) =
            Expression::analyze(from.left().expression(), ty, scope)?;
        let ast_l = Arc::new(ast_l_expr);
        all_warnings.append(&mut warnings_l);
        all_warnings.extend(scope.pop_scope());
        scope.push_scope();
        if let Some((pat_r, ty_r)) = from.right().pattern().as_typed_pattern() {
            let ty_r = scope.resolve(ty_r).with_span(from)?;
            let typed_variables = pat_r.is_of_type(&ty_r).with_span(from)?;
            let span = from.right().pattern_span().unwrap_or(*from.as_ref());
            for (identifier, ty) in typed_variables {
                scope.bind_variable(identifier, ty, span);
            }
        }
        let (ast_r_expr, mut warnings_r) =
            Expression::analyze(from.right().expression(), ty, scope)?;
        let ast_r = Arc::new(ast_r_expr);
        all_warnings.append(&mut warnings_r);
        all_warnings.extend(scope.pop_scope());

        Ok((
            Self {
                scrutinee,
                left: MatchArm {
                    pattern: from.left().pattern().clone(),
                    expression: ast_l,
                },
                right: MatchArm {
                    pattern: from.right().pattern().clone(),
                    expression: ast_r,
                },
                span: *from.as_ref(),
            },
            all_warnings,
        ))
    }
}

fn analyze_named_module(
    name: ModuleName,
    from: &parse::ModuleProgram,
) -> Result<HashMap<WitnessName, Value>, RichError> {
    let unit = ResolvedType::unit();
    let mut scope = Scope::default();
    let items: Vec<(ModuleItem, Vec<Warning>)> = from
        .items()
        .iter()
        .map(|s| ModuleItem::analyze(s, &unit, &mut scope))
        .collect::<Result<_, RichError>>()?;
    debug_assert!(scope.is_topmost());
    // Module assignments only allow constant expressions — there are no `let`
    // bindings, so no unused-variable warnings can arise. Warnings are
    // intentionally discarded here. In future however, there may be
    // other warnings added. Named modules are not really used at the moment
    // and may be substituted for something else in future.
    let mut iter = items
        .into_iter()
        .filter_map(|(item, _warnings)| match item {
            ModuleItem::Module(module) if module.name == name => Some(module),
            _ => None,
        });
    let Some(witness_module) = iter.next() else {
        return Ok(HashMap::new()); // "not present" is equivalent to empty
    };
    if iter.next().is_some() {
        return Err(Error::ModuleRedefined(name)).with_span(from);
    }
    let mut map = HashMap::new();
    for assignment in witness_module.assignments() {
        if map.contains_key(assignment.name()) {
            return Err(Error::WitnessReassigned(assignment.name().shallow_clone()))
                .with_span(assignment);
        }
        map.insert(
            assignment.name().shallow_clone(),
            assignment.value().clone(),
        );
    }
    Ok(map)
}

impl WitnessValues {
    pub fn analyze(from: &parse::ModuleProgram) -> Result<Self, RichError> {
        analyze_named_module(ModuleName::witness(), from).map(Self::from)
    }
}

impl crate::witness::Arguments {
    pub fn analyze(from: &parse::ModuleProgram) -> Result<Self, RichError> {
        analyze_named_module(ModuleName::param(), from).map(Self::from)
    }
}

impl AbstractSyntaxTree for ModuleItem {
    type From = parse::ModuleItem;

    fn analyze(
        from: &Self::From,
        ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<(Self, Vec<Warning>), RichError> {
        assert!(ty.is_unit(), "Items cannot return anything");
        assert!(scope.is_topmost(), "Items live in the topmost scope only");
        match from {
            parse::ModuleItem::Ignored => Ok((Self::Ignored, vec![])),
            parse::ModuleItem::Module(witness_module) => Module::analyze(witness_module, ty, scope)
                .map(|(m, warnings)| (Self::Module(m), warnings)),
        }
    }
}

impl AbstractSyntaxTree for Module {
    type From = parse::Module;

    fn analyze(
        from: &Self::From,
        ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<(Self, Vec<Warning>), RichError> {
        assert!(ty.is_unit(), "Modules cannot return anything");
        assert!(scope.is_topmost(), "Modules live in the topmost scope only");
        let results = from
            .assignments()
            .iter()
            .map(|s| ModuleAssignment::analyze(s, ty, scope))
            .collect::<Result<Vec<(ModuleAssignment, Vec<Warning>)>, RichError>>()?;
        debug_assert!(scope.is_topmost());

        let (all_assignments, warnings): (Vec<_>, Vec<_>) = results.into_iter().unzip();
        let all_warnings: Vec<Warning> = warnings.into_iter().flatten().collect();

        Ok((
            Self {
                name: from.name().shallow_clone(),
                span: *from.as_ref(),
                assignments: all_assignments.into(),
            },
            all_warnings,
        ))
    }
}

impl AbstractSyntaxTree for ModuleAssignment {
    type From = parse::ModuleAssignment;

    fn analyze(
        from: &Self::From,
        ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<(Self, Vec<Warning>), RichError> {
        assert!(ty.is_unit(), "Assignments cannot return anything");
        let ty_expr = scope.resolve(from.ty()).with_span(from)?;
        let (expression, warnings) = Expression::analyze(from.expression(), &ty_expr, scope)?;
        let value = Value::from_const_expr(&expression)
            .ok_or(Error::ExpressionUnexpectedType(ty_expr.clone()))
            .with_span(from.expression())?;

        Ok((
            Self {
                name: from.name().clone(),
                value,
                span: *from.as_ref(),
            },
            warnings,
        ))
    }
}

impl AsRef<Span> for Assignment {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for Expression {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for SingleExpression {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for Call {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for Match {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for Module {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for ModuleAssignment {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}
