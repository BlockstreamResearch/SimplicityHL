use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fmt;
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
    /// Infix operator expression: calls an arithmetic or comparison jet.
    BinaryOp {
        jet: Elements,
        lhs: Arc<Expression>,
        rhs: Arc<Expression>,
        assert_no_carry: bool,
        swap_args: bool,
        negate_result: bool,
        check_nonzero_divisor: bool,
    },
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
                S::BinaryOp { lhs, rhs, .. } => {
                    Tree::Nary(Arc::new([Self::Expression(lhs), Self::Expression(rhs)]))
                }
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
    /// ## Panics
    ///
    /// The stack is empty.
    pub fn pop_scope(&mut self) {
        self.variables.pop().expect("Stack is empty");
    }

    /// Pop the scope of the main function from the stack.
    ///
    /// ## Panics
    ///
    /// - The current scope is not inside the main function.
    /// - The current scope is not nested in the topmost scope.
    pub fn pop_main_scope(&mut self) {
        assert!(self.is_main, "Current scope is not inside main function");
        self.pop_scope();
        self.is_main = false;
        assert!(
            self.is_topmost(),
            "Current scope is not nested in topmost scope"
        )
    }

    /// Push a variable onto the current stack.
    ///
    /// ## Panics
    ///
    /// The stack is empty.
    pub fn insert_variable(&mut self, identifier: Identifier, ty: ResolvedType) {
        self.variables
            .last_mut()
            .expect("Stack is empty")
            .insert(identifier, ty);
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum WarningName {
    ModuleItemIgnored,
    ArithmeticOperationCouldOverflow,
    DivisionCouldPanicOnZero,
}

impl fmt::Display for WarningName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WarningName::ModuleItemIgnored => write!(f, "ModuleItem was ignored"),
            WarningName::ArithmeticOperationCouldOverflow => write!(f, "This operator panics if the result overflows. To handle overflow, use the jet directly and destructure the (bool, uN) result."),
            WarningName::DivisionCouldPanicOnZero => write!(f, "This operator panics if the divisor is zero. To handle division by zero, use a jet and check the divisor before using it."),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Warning {
    /// Canonical name used for allowing and denying specific warnings.
    pub canonical_name: WarningName,
    /// Span in which this warning occured.
    pub span: Span,
}

impl Warning {
    fn module_item_ignored<S: Into<Span>>(span: S) -> Self {
        Warning {
            canonical_name: WarningName::ModuleItemIgnored,
            span: span.into(),
        }
    }

    fn arthimetic_operation_could_overflow<S: Into<Span>>(span: S) -> Self {
        Warning {
            canonical_name: WarningName::ArithmeticOperationCouldOverflow,
            span: span.into(),
        }
    }

    fn division_could_panic_on_zero<S: Into<Span>>(span: S) -> Self {
        Warning {
            canonical_name: WarningName::DivisionCouldPanicOnZero,
            span: span.into(),
        }
    }
}

impl From<Warning> for RichError {
    fn from(value: Warning) -> Self {
        RichError::new(Error::DeniedWarning(value.canonical_name), value.span)
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
            match item {
                Item::Function(Function::Main(expr)) => {
                    if main_seen {
                        return Err(Error::FunctionRedefined(FunctionName::main())).with_span(from);
                    }
                    main_expr = Some(expr);
                    main_seen = true;
                }
                _ => {}
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
            for param in params.iter() {
                scope.insert_variable(param.identifier().clone(), param.ty().clone());
            }
            let (body, warnings) = Expression::analyze(from.body(), &ret, scope)?;
            scope.pop_scope();
            debug_assert!(scope.is_topmost());
            let function = CustomFunction {
                params,
                body: Arc::new(body),
            };
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
        let (body, warnings) = Expression::analyze(from.body(), ty, scope)?;
        scope.pop_main_scope();
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
        for (identifier, ty) in typed_variables {
            scope.insert_variable(identifier, ty);
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
    pub fn analyze_const(
        from: &parse::Expression,
        ty: &ResolvedType,
    ) -> Result<(Self, Vec<Warning>), RichError> {
        let mut empty_scope = Scope::default();
        Self::analyze(from, ty, &mut empty_scope)
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
                let ast_statements: Vec<(Statement, Vec<Warning>)> = statements
                    .iter()
                    .map(|s| Statement::analyze(s, &ResolvedType::unit(), scope))
                    .collect::<Result<_, RichError>>()?;
                let (ast_expression, mut ast_warnings) = match expression {
                    Some(expression) => Expression::analyze(expression, ty, scope)
                        .map(|(e, warnings)| (Some(Arc::new(e)), warnings)),
                    None if ty.is_unit() => Ok((None, vec![])),
                    None => Err(Error::ExpressionTypeMismatch(
                        ty.clone(),
                        ResolvedType::unit(),
                    ))
                    .with_span(from),
                }?;
                scope.pop_scope();

                let mut all_warnings = vec![];
                let mut all_statements = vec![];
                for (statement, mut warnings) in ast_statements {
                    all_warnings.append(&mut warnings);
                    all_statements.push(statement);
                }
                all_warnings.append(&mut ast_warnings);

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

/// Tries to infer the type of a parse expression using the current scope,
/// without performing a full analysis. Returns `None` if the type cannot be determined.
fn peek_expression_type(expr: &parse::Expression, scope: &Scope) -> Option<ResolvedType> {
    match expr.inner() {
        parse::ExpressionInner::Single(single) => peek_single_expression_type(single, scope),
        parse::ExpressionInner::Block(_, Some(end_expr)) => peek_expression_type(end_expr, scope),
        parse::ExpressionInner::Block(_, None) => Some(ResolvedType::unit()),
    }
}

fn peek_single_expression_type(
    expr: &parse::SingleExpression,
    scope: &Scope,
) -> Option<ResolvedType> {
    match expr.inner() {
        parse::SingleExpressionInner::Variable(id) => scope.get_variable(id).cloned(),
        parse::SingleExpressionInner::Expression(inner) => peek_expression_type(inner, scope),
        _ => None,
    }
}

/// Maps a comparison infix operator and operand type to:
/// - the Simplicity jet
/// - whether arguments should be swapped (for `>` and `>=`) Note: there are no GreaterThan jets, so the
///   args must be swapped.
/// - whether the result should be negated (for `!=`)
///
/// Returns `Err` if there is no jet for the given combination.
fn determine_comparison_op_jet(
    op: &parse::InfixOp,
    arg_ty: &ResolvedType,
) -> Result<(Elements, bool, bool), Error> {
    use parse::InfixOp::*;
    use UIntType::*;

    let uint_ty = arg_ty
        .as_integer()
        .ok_or_else(|| Error::ExpressionUnexpectedType(arg_ty.clone()))?;

    match op {
        Eq | Ne => {
            let jet = match uint_ty {
                U1 => Elements::Eq1,
                U8 => Elements::Eq8,
                U16 => Elements::Eq16,
                U32 => Elements::Eq32,
                U64 => Elements::Eq64,
                _ => return Err(Error::ExpressionUnexpectedType(arg_ty.clone())),
            };
            Ok((jet, false, matches!(op, Ne)))
        }
        Lt | Gt => {
            let jet = match uint_ty {
                U8 => Elements::Lt8,
                U16 => Elements::Lt16,
                U32 => Elements::Lt32,
                U64 => Elements::Lt64,
                _ => return Err(Error::ExpressionUnexpectedType(arg_ty.clone())),
            };
            // Gt(a, b) = Lt(b, a) → swap_args=true for Gt
            Ok((jet, matches!(op, Gt), false))
        }
        Le | Ge => {
            let jet = match uint_ty {
                U8 => Elements::Le8,
                U16 => Elements::Le16,
                U32 => Elements::Le32,
                U64 => Elements::Le64,
                _ => return Err(Error::ExpressionUnexpectedType(arg_ty.clone())),
            };
            // Ge(a, b) = Le(b, a) → swap_args=true for Ge
            Ok((jet, matches!(op, Ge), false))
        }
        _ => Err(Error::ExpressionUnexpectedType(arg_ty.clone())),
    }
}

/// Maps an infix operator and the expected output type to the corresponding Simplicity jet,
/// the expected input argument type, and whether the jet's raw output is `(bool, uN)`
/// and requires a carry/overflow assertion.
///
/// Returns `Err` if there is no jet for the given operator + output type combination.
///
/// | Operator | Output type | Jet         | Input type | Assert no carry |
/// |----------|-------------|-------------|------------|-----------------|
/// | `+`      | `uN`        | `AddN`      | `uN`       | yes             |
/// | `-`      | `uN`        | `SubtractN` | `uN`       | yes             |
/// | `*`      | `u(2N)`     | `MultiplyN` | `uN`       | no              |
/// | `/`      | `uN`        | `DivideN`   | `uN`       | no              |
/// | `%`      | `uN`        | `ModuloN`   | `uN`       | no              |
/// Maps a bitwise infix operator and operand type to the corresponding Simplicity jet.
///
/// | Operator | Output type | Jet    | Input type |
/// |----------|-------------|--------|------------|
/// | `&`      | `uN`        | `AndN` | `uN`       |
/// | `\|`     | `uN`        | `OrN`  | `uN`       |
/// | `^`      | `uN`        | `XorN` | `uN`       |
fn determine_infix_bitwise_op_jet(
    op: &parse::InfixOp,
    ty: &ResolvedType,
) -> Result<Elements, Error> {
    use parse::InfixOp::*;
    use UIntType::*;

    let uint_ty = ty
        .as_integer()
        .ok_or_else(|| Error::ExpressionUnexpectedType(ty.clone()))?;

    match (op, uint_ty) {
        (BitAnd, U1) => Ok(Elements::And1),
        (BitAnd, U8) => Ok(Elements::And8),
        (BitAnd, U16) => Ok(Elements::And16),
        (BitAnd, U32) => Ok(Elements::And32),
        (BitAnd, U64) => Ok(Elements::And64),
        (BitOr, U1) => Ok(Elements::Or1),
        (BitOr, U8) => Ok(Elements::Or8),
        (BitOr, U16) => Ok(Elements::Or16),
        (BitOr, U32) => Ok(Elements::Or32),
        (BitOr, U64) => Ok(Elements::Or64),
        (BitXor, U1) => Ok(Elements::Xor1),
        (BitXor, U8) => Ok(Elements::Xor8),
        (BitXor, U16) => Ok(Elements::Xor16),
        (BitXor, U32) => Ok(Elements::Xor32),
        (BitXor, U64) => Ok(Elements::Xor64),
        _ => Err(Error::ExpressionUnexpectedType(ty.clone())),
    }
}

fn determine_infix_arith_op_jet(
    op: &parse::InfixOp,
    ty: &ResolvedType,
) -> Result<(Elements, ResolvedType, bool), Error> {
    use parse::InfixOp::*;
    use UIntType::*;

    match op {
        // Add and Sub: jet produces (bool, uN); assert no carry, then return uN
        Add | Sub => {
            let uint_ty = ty
                .as_integer()
                .ok_or_else(|| Error::ExpressionUnexpectedType(ty.clone()))?;

            let jet = match (op, uint_ty) {
                (Add, U8) => Elements::Add8,
                (Add, U16) => Elements::Add16,
                (Add, U32) => Elements::Add32,
                (Add, U64) => Elements::Add64,
                (Sub, U8) => Elements::Subtract8,
                (Sub, U16) => Elements::Subtract16,
                (Sub, U32) => Elements::Subtract32,
                (Sub, U64) => Elements::Subtract64,
                _ => return Err(Error::ExpressionUnexpectedType(ty.clone())),
            };

            Ok((jet, ResolvedType::from(uint_ty), true))
        }
        // Mul: jet takes (uN, uN) and produces u(2N), no overflow possible
        Mul => {
            let (jet, arg_uint) = match ty.as_integer() {
                Some(U16) => (Elements::Multiply8, U8),
                Some(U32) => (Elements::Multiply16, U16),
                Some(U64) => (Elements::Multiply32, U32),
                Some(U128) => (Elements::Multiply64, U64),
                _ => return Err(Error::ExpressionUnexpectedType(ty.clone())),
            };
            Ok((jet, ResolvedType::from(arg_uint), false))
        }
        // Div and Rem: jet takes (uN, uN) and produces uN, no overflow flag
        Div | Rem => {
            let uint_ty = ty
                .as_integer()
                .ok_or_else(|| Error::ExpressionUnexpectedType(ty.clone()))?;

            let jet = match (op, uint_ty) {
                (Div, U8) => Elements::Divide8,
                (Div, U16) => Elements::Divide16,
                (Div, U32) => Elements::Divide32,
                (Div, U64) => Elements::Divide64,
                (Rem, U8) => Elements::Modulo8,
                (Rem, U16) => Elements::Modulo16,
                (Rem, U32) => Elements::Modulo32,
                (Rem, U64) => Elements::Modulo64,
                _ => return Err(Error::ExpressionUnexpectedType(ty.clone())),
            };
            Ok((jet, ResolvedType::from(uint_ty), false))
        }
        // Comparison ops are handled by comparison_op_jet, not here
        _ => Err(Error::ExpressionUnexpectedType(ty.clone())),
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
                scope.insert_variable(identifier.clone(), ty.clone());
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
                let inner: Vec<(Expression, Vec<Warning>)> = tuple
                    .iter()
                    .zip(types.iter())
                    .map(|(el_parse, el_ty)| Expression::analyze(el_parse, el_ty, scope))
                    .collect::<Result<_, RichError>>()?;

                let mut all_warnings = vec![];
                let mut all_expressions: Vec<Expression> = vec![];
                for i in inner {
                    all_warnings.extend_from_slice(&i.1);
                    all_expressions.push(i.0);
                }

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
                let inner: Vec<(Expression, Vec<Warning>)> = array
                    .iter()
                    .map(|el_parse| Expression::analyze(el_parse, el_ty, scope))
                    .collect::<Result<_, RichError>>()?;

                let mut all_warnings = vec![];
                let mut all_expressions: Vec<Expression> = vec![];
                for i in inner {
                    all_warnings.extend_from_slice(&i.1);
                    all_expressions.push(i.0);
                }

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
                let inner: Vec<(Expression, Vec<Warning>)> = list
                    .iter()
                    .map(|el_parse| Expression::analyze(el_parse, el_ty, scope))
                    .collect::<Result<_, RichError>>()?;

                let mut all_warnings = vec![];
                let mut all_expressions: Vec<Expression> = vec![];
                for i in inner {
                    all_warnings.extend_from_slice(&i.1);
                    all_expressions.push(i.0);
                }

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
            parse::SingleExpressionInner::BinaryOp(binary) => {
                use parse::InfixOp::*;
                match binary.op() {
                    Eq | Ne | Lt | Le | Gt | Ge => {
                        // Comparison operators: output type must be bool
                        if !ty.is_boolean() {
                            return Err(Error::ExpressionUnexpectedType(ty.clone()))
                                .with_span(from);
                        }
                        // Infer operand type from lhs expression
                        let arg_ty = peek_expression_type(binary.lhs(), scope)
                            .ok_or(Error::ExpressionUnexpectedType(ty.clone()))
                            .with_span(from)?;
                        let (jet, swap_args, negate_result) =
                            determine_comparison_op_jet(binary.op(), &arg_ty).with_span(from)?;
                        let (lhs, mut lhs_warnings) =
                            Expression::analyze(binary.lhs(), &arg_ty, scope)?;
                        let (rhs, mut rhs_warnings) =
                            Expression::analyze(binary.rhs(), &arg_ty, scope)?;
                        lhs_warnings.append(&mut rhs_warnings);
                        scope.track_call(from, TrackedCallName::Jet);
                        (
                            SingleExpressionInner::BinaryOp {
                                jet,
                                lhs: Arc::new(lhs),
                                rhs: Arc::new(rhs),
                                assert_no_carry: false,
                                swap_args,
                                negate_result,
                                check_nonzero_divisor: false,
                            },
                            lhs_warnings,
                        )
                    }
                    LogicalAnd | LogicalOr => {
                        // Desugar to a match so the Simplicity `case` combinator
                        // provides natural short-circuit evaluation — only the
                        // taken branch is evaluated.
                        //
                        // a && b  =>  match a { false => false, true => b }
                        // a || b  =>  match a { false => b,     true => true }
                        if !ty.is_boolean() {
                            return Err(Error::ExpressionUnexpectedType(ty.clone()))
                                .with_span(from);
                        }
                        let bool_ty = ResolvedType::boolean();
                        let span = *from.as_ref();
                        let (lhs, mut lhs_warnings) =
                            Expression::analyze(binary.lhs(), &bool_ty, scope)?;
                        let (rhs, mut rhs_warnings) =
                            Expression::analyze(binary.rhs(), &bool_ty, scope)?;
                        lhs_warnings.append(&mut rhs_warnings);

                        let make_bool = |b: bool| -> Expression {
                            Expression {
                                inner: ExpressionInner::Single(SingleExpression {
                                    inner: SingleExpressionInner::Constant(Value::from(b)),
                                    ty: bool_ty.clone(),
                                    span,
                                }),
                                ty: bool_ty.clone(),
                                span,
                            }
                        };

                        let (left_expr, right_expr) = match binary.op() {
                            LogicalAnd => (make_bool(false), rhs),
                            LogicalOr => (rhs, make_bool(true)),
                            _ => unreachable!(),
                        };
                        (
                            SingleExpressionInner::Match(Match {
                                scrutinee: Arc::new(lhs),
                                left: MatchArm {
                                    pattern: MatchPattern::False,
                                    expression: Arc::new(left_expr),
                                },
                                right: MatchArm {
                                    pattern: MatchPattern::True,
                                    expression: Arc::new(right_expr),
                                },
                                span,
                            }),
                            lhs_warnings,
                        )
                    }
                    BitAnd | BitOr | BitXor => {
                        // Bitwise operators: same input and output type, no carry or overflow
                        let jet =
                            determine_infix_bitwise_op_jet(binary.op(), ty).with_span(from)?;
                        let (lhs, mut lhs_warnings) =
                            Expression::analyze(binary.lhs(), ty, scope)?;
                        let (rhs, mut rhs_warnings) =
                            Expression::analyze(binary.rhs(), ty, scope)?;
                        lhs_warnings.append(&mut rhs_warnings);
                        scope.track_call(from, TrackedCallName::Jet);
                        (
                            SingleExpressionInner::BinaryOp {
                                jet,
                                lhs: Arc::new(lhs),
                                rhs: Arc::new(rhs),
                                assert_no_carry: false,
                                swap_args: false,
                                negate_result: false,
                                check_nonzero_divisor: false,
                            },
                            lhs_warnings,
                        )
                    }
                    Add | Sub | Mul | Div | Rem => {
                        // Arithmetic operators
                        let (jet, arg_ty, assert_no_carry) =
                            determine_infix_arith_op_jet(binary.op(), ty).with_span(from)?;
                        let (lhs, mut lhs_warnings) =
                            Expression::analyze(binary.lhs(), &arg_ty, scope)?;
                        let (rhs, mut rhs_warnings) =
                            Expression::analyze(binary.rhs(), &arg_ty, scope)?;
                        lhs_warnings.append(&mut rhs_warnings);
                        if assert_no_carry {
                            lhs_warnings.push(Warning::arthimetic_operation_could_overflow(&from))
                        }
                        if matches!(binary.op(), parse::InfixOp::Div | parse::InfixOp::Rem) {
                            lhs_warnings.push(Warning::division_could_panic_on_zero(&from))
                        }
                        scope.track_call(from, TrackedCallName::Jet);
                        (
                            SingleExpressionInner::BinaryOp {
                                jet,
                                lhs: Arc::new(lhs),
                                rhs: Arc::new(rhs),
                                assert_no_carry,
                                swap_args: false,
                                negate_result: false,
                                check_nonzero_divisor: matches!(
                                    binary.op(),
                                    parse::InfixOp::Div | parse::InfixOp::Rem
                                ),
                            },
                            lhs_warnings,
                        )
                    }
                }
            }
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
            let args: Vec<(Expression, Vec<Warning>)> = parse_args
                .iter()
                .zip(args_tys.iter())
                .map(|(arg_parse, arg_ty)| Expression::analyze(arg_parse, arg_ty, scope))
                .collect::<Result<_, RichError>>()?;
            let mut all_warns = vec![];
            let mut all_args = vec![];
            for (e, mut w) in args {
                all_warns.append(&mut w);
                all_args.push(e);
            }
            Ok((all_args.into(), all_warns))
        }

        let (name, name_warnings) = CallName::analyze(from, ty, scope)?;
        let (args, mut args_warnings) = match name.clone() {
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
                analyze_arguments(from.args(), &args_tys, scope)?
            }
            CallName::UnwrapLeft(right_ty) => {
                let args_tys = [ResolvedType::either(ty.clone(), right_ty)];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                let args = analyze_arguments(from.args(), &args_tys, scope)?;
                let [arg_ty] = args_tys;
                scope.track_call(from, TrackedCallName::UnwrapLeft(arg_ty));
                args
            }
            CallName::UnwrapRight(left_ty) => {
                let args_tys = [ResolvedType::either(left_ty, ty.clone())];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                let args = analyze_arguments(from.args(), &args_tys, scope)?;
                let [arg_ty] = args_tys;
                scope.track_call(from, TrackedCallName::UnwrapRight(arg_ty));
                args
            }
            CallName::IsNone(some_ty) => {
                let args_tys = [ResolvedType::option(some_ty)];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                let out_ty = ResolvedType::boolean();
                check_output_type(&out_ty, ty).with_span(from)?;
                analyze_arguments(from.args(), &args_tys, scope)?
            }
            CallName::Unwrap => {
                let args_tys = [ResolvedType::option(ty.clone())];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                scope.track_call(from, TrackedCallName::Unwrap);
                analyze_arguments(from.args(), &args_tys, scope)?
            }
            CallName::Assert => {
                let args_tys = [ResolvedType::boolean()];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                let out_ty = ResolvedType::unit();
                check_output_type(&out_ty, ty).with_span(from)?;
                scope.track_call(from, TrackedCallName::Assert);
                analyze_arguments(from.args(), &args_tys, scope)?
            }
            CallName::Panic => {
                let args_tys = [];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                // panic! allows every output type because it will never return anything
                scope.track_call(from, TrackedCallName::Panic);
                analyze_arguments(from.args(), &args_tys, scope)?
            }
            CallName::Debug => {
                let args_tys = [ty.clone()];
                check_argument_types(from.args(), &args_tys).with_span(from)?;
                let args = analyze_arguments(from.args(), &args_tys, scope)?;
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
                analyze_arguments(from.args(), &args_tys, scope)?
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
                analyze_arguments(from.args(), &args_ty, scope)?
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
                analyze_arguments(from.args(), &args_ty, scope)?
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
                analyze_arguments(from.args(), &args_ty, scope)?
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
                analyze_arguments(from.args(), &args_ty, scope)?
            }
        };

        let mut all_warnings = name_warnings;
        all_warnings.append(&mut args_warnings);
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
        match from.name() {
            parse::CallName::Jet(name) => match Elements::from_str(name.as_inner()) {
                Ok(Elements::CheckSigVerify | Elements::Verify) | Err(_) => {
                    Err(Error::JetDoesNotExist(name.clone())).with_span(from)
                }
                Ok(jet) => Ok((Self::Jet(jet), vec![])),
            },
            parse::CallName::UnwrapLeft(right_ty) => scope
                .resolve(right_ty)
                .map(|c| (Self::UnwrapLeft(c), vec![]))
                .with_span(from),
            parse::CallName::UnwrapRight(left_ty) => scope
                .resolve(left_ty)
                .map(|c| (Self::UnwrapRight(c), vec![]))
                .with_span(from),
            parse::CallName::IsNone(some_ty) => scope
                .resolve(some_ty)
                .map(|c| (Self::IsNone(c), vec![]))
                .with_span(from),
            parse::CallName::Unwrap => Ok((Self::Unwrap, vec![])),
            parse::CallName::Assert => Ok((Self::Assert, vec![])),
            parse::CallName::Panic => Ok((Self::Panic, vec![])),
            parse::CallName::Debug => Ok((Self::Debug, vec![])),
            parse::CallName::TypeCast(target) => scope
                .resolve(target)
                .map(|c| (Self::TypeCast(c), vec![]))
                .with_span(from),
            parse::CallName::Custom(name) => scope
                .get_function(name)
                .cloned()
                .map(|c| (Self::Custom(c), vec![]))
                .ok_or(Error::FunctionUndefined(name.clone()))
                .with_span(from),
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
                    Err(Error::FunctionNotFoldable(name.clone())).with_span(from)
                } else {
                    Ok((Self::ArrayFold(function, *size), vec![]))
                }
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
                    Err(Error::FunctionNotFoldable(name.clone())).with_span(from)
                } else {
                    Ok((Self::Fold(function, *bound), vec![]))
                }
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
                    ) => Ok((Self::ForWhile(function, int_ty.bit_width()), vec![])),
                    _ => Err(Error::FunctionNotLoopable(name.clone())).with_span(from),
                }
            }
        }
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
        let (scrutinee, scrutinee_warnings) =
            Expression::analyze(from.scrutinee(), &scrutinee_ty, scope)?;

        scope.push_scope();
        if let Some((pat_l, ty_l)) = from.left().pattern().as_typed_pattern() {
            let ty_l = scope.resolve(ty_l).with_span(from)?;
            let typed_variables = pat_l.is_of_type(&ty_l).with_span(from)?;
            for (identifier, ty) in typed_variables {
                scope.insert_variable(identifier, ty);
            }
        }
        let (ast_l, mut ast_l_warnings) = Expression::analyze(from.left().expression(), ty, scope)?;
        scope.pop_scope();
        scope.push_scope();
        if let Some((pat_r, ty_r)) = from.right().pattern().as_typed_pattern() {
            let ty_r = scope.resolve(ty_r).with_span(from)?;
            let typed_variables = pat_r.is_of_type(&ty_r).with_span(from)?;
            for (identifier, ty) in typed_variables {
                scope.insert_variable(identifier, ty);
            }
        }
        let (ast_r, mut ast_r_warnings) =
            Expression::analyze(from.right().expression(), ty, scope)?;
        scope.pop_scope();

        let mut all_warnings = scrutinee_warnings;
        all_warnings.append(&mut ast_l_warnings);
        all_warnings.append(&mut ast_r_warnings);

        Ok((
            Self {
                scrutinee: Arc::new(scrutinee),
                left: MatchArm {
                    pattern: from.left().pattern().clone(),
                    expression: Arc::new(ast_l),
                },
                right: MatchArm {
                    pattern: from.right().pattern().clone(),
                    expression: Arc::new(ast_r),
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
) -> Result<(HashMap<WitnessName, Value>, Vec<Warning>), RichError> {
    let unit = ResolvedType::unit();
    let mut scope = Scope::default();
    let items: Vec<(ModuleItem, Vec<Warning>)> = from
        .items()
        .iter()
        .map(|s| ModuleItem::analyze(s, &unit, &mut scope))
        .collect::<Result<_, RichError>>()?;

    debug_assert!(scope.is_topmost());
    let mut iter = items.into_iter().filter_map(|(item, warnings)| match item {
        ModuleItem::Module(module) if module.name == name => Some((module, warnings)),
        _ => None,
    });
    let Some((witness_module, warnings)) = iter.next() else {
        return Ok((HashMap::new(), vec![])); // "not present" is equivalent to empty
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
    Ok((map, warnings))
}

impl WitnessValues {
    pub fn analyze(from: &parse::ModuleProgram) -> Result<(Self, Vec<Warning>), RichError> {
        analyze_named_module(ModuleName::witness(), from)
            .map(|(i, warnings)| (Self::from(i), warnings))
    }
}

impl crate::witness::Arguments {
    pub fn analyze(from: &parse::ModuleProgram) -> Result<(Self, Vec<Warning>), RichError> {
        analyze_named_module(ModuleName::param(), from).map(|(i, warning)| (Self::from(i), warning))
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
            parse::ModuleItem::Ignored => {
                // TODO: confirm if this is a warning.
                // TODO: find the correct span
                Ok((
                    Self::Ignored,
                    vec![Warning::module_item_ignored(Span::new(0, 0))],
                ))
            }
            parse::ModuleItem::Module(witness_module) => Module::analyze(witness_module, ty, scope)
                .map(|(m, warning)| (Self::Module(m), warning)),
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
        let assignments: Vec<(ModuleAssignment, Vec<Warning>)> = from
            .assignments()
            .iter()
            .map(|s| ModuleAssignment::analyze(s, ty, scope))
            .collect::<Result<_, RichError>>()?;
        debug_assert!(scope.is_topmost());

        let mut all_warnings = vec![];
        let mut all_assignments = vec![];
        for (a, mut warnings) in assignments {
            all_warnings.append(&mut warnings);
            all_assignments.push(a);
        }

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

#[cfg(test)]
mod tests {
    use simplicity::jet::Elements;

    use crate::parse::InfixOp;
    use crate::types::{ResolvedType, TypeConstructible};

    use super::determine_infix_arith_op_jet;

    // --- infix_op_jet: Add ---

    #[test]
    fn infix_op_jet_add_u8() {
        let (jet, arg, carry) =
            determine_infix_arith_op_jet(&InfixOp::Add, &ResolvedType::u8()).unwrap();
        assert_eq!(jet, Elements::Add8);
        assert_eq!(arg, ResolvedType::u8());
        assert!(carry);
    }

    #[test]
    fn infix_op_jet_add_u16() {
        let (jet, arg, carry) =
            determine_infix_arith_op_jet(&InfixOp::Add, &ResolvedType::u16()).unwrap();
        assert_eq!(jet, Elements::Add16);
        assert_eq!(arg, ResolvedType::u16());
        assert!(carry);
    }

    #[test]
    fn infix_op_jet_add_u32() {
        let (jet, arg, carry) =
            determine_infix_arith_op_jet(&InfixOp::Add, &ResolvedType::u32()).unwrap();
        assert_eq!(jet, Elements::Add32);
        assert_eq!(arg, ResolvedType::u32());
        assert!(carry);
    }

    #[test]
    fn infix_op_jet_add_u64() {
        let (jet, arg, carry) =
            determine_infix_arith_op_jet(&InfixOp::Add, &ResolvedType::u64()).unwrap();
        assert_eq!(jet, Elements::Add64);
        assert_eq!(arg, ResolvedType::u64());
        assert!(carry);
    }

    // --- infix_op_jet: Sub ---

    #[test]
    fn infix_op_jet_sub_u8() {
        let (jet, arg, carry) =
            determine_infix_arith_op_jet(&InfixOp::Sub, &ResolvedType::u8()).unwrap();
        assert_eq!(jet, Elements::Subtract8);
        assert_eq!(arg, ResolvedType::u8());
        assert!(carry);
    }

    #[test]
    fn infix_op_jet_sub_u16() {
        let (jet, arg, carry) =
            determine_infix_arith_op_jet(&InfixOp::Sub, &ResolvedType::u16()).unwrap();
        assert_eq!(jet, Elements::Subtract16);
        assert_eq!(arg, ResolvedType::u16());
        assert!(carry);
    }

    #[test]
    fn infix_op_jet_sub_u32() {
        let (jet, arg, carry) =
            determine_infix_arith_op_jet(&InfixOp::Sub, &ResolvedType::u32()).unwrap();
        assert_eq!(jet, Elements::Subtract32);
        assert_eq!(arg, ResolvedType::u32());
        assert!(carry);
    }

    #[test]
    fn infix_op_jet_sub_u64() {
        let (jet, arg, carry) =
            determine_infix_arith_op_jet(&InfixOp::Sub, &ResolvedType::u64()).unwrap();
        assert_eq!(jet, Elements::Subtract64);
        assert_eq!(arg, ResolvedType::u64());
        assert!(carry);
    }

    // --- infix_op_jet: Mul ---

    #[test]
    fn infix_op_jet_mul_u16() {
        let (jet, arg, carry) =
            determine_infix_arith_op_jet(&InfixOp::Mul, &ResolvedType::u16()).unwrap();
        assert_eq!(jet, Elements::Multiply8);
        assert_eq!(arg, ResolvedType::u8());
        assert!(!carry);
    }

    #[test]
    fn infix_op_jet_mul_u32() {
        let (jet, arg, carry) =
            determine_infix_arith_op_jet(&InfixOp::Mul, &ResolvedType::u32()).unwrap();
        assert_eq!(jet, Elements::Multiply16);
        assert_eq!(arg, ResolvedType::u16());
        assert!(!carry);
    }

    #[test]
    fn infix_op_jet_mul_u64() {
        let (jet, arg, carry) =
            determine_infix_arith_op_jet(&InfixOp::Mul, &ResolvedType::u64()).unwrap();
        assert_eq!(jet, Elements::Multiply32);
        assert_eq!(arg, ResolvedType::u32());
        assert!(!carry);
    }

    #[test]
    fn infix_op_jet_mul_u128() {
        let (jet, arg, carry) =
            determine_infix_arith_op_jet(&InfixOp::Mul, &ResolvedType::u128()).unwrap();
        assert_eq!(jet, Elements::Multiply64);
        assert_eq!(arg, ResolvedType::u64());
        assert!(!carry);
    }

    // --- infix_op_jet: Div ---

    #[test]
    fn infix_op_jet_div_u8() {
        let (jet, arg, carry) =
            determine_infix_arith_op_jet(&InfixOp::Div, &ResolvedType::u8()).unwrap();
        assert_eq!(jet, Elements::Divide8);
        assert_eq!(arg, ResolvedType::u8());
        assert!(!carry);
    }

    #[test]
    fn infix_op_jet_div_u16() {
        let (jet, arg, carry) =
            determine_infix_arith_op_jet(&InfixOp::Div, &ResolvedType::u16()).unwrap();
        assert_eq!(jet, Elements::Divide16);
        assert_eq!(arg, ResolvedType::u16());
        assert!(!carry);
    }

    #[test]
    fn infix_op_jet_div_u32() {
        let (jet, arg, carry) =
            determine_infix_arith_op_jet(&InfixOp::Div, &ResolvedType::u32()).unwrap();
        assert_eq!(jet, Elements::Divide32);
        assert_eq!(arg, ResolvedType::u32());
        assert!(!carry);
    }

    #[test]
    fn infix_op_jet_div_u64() {
        let (jet, arg, carry) =
            determine_infix_arith_op_jet(&InfixOp::Div, &ResolvedType::u64()).unwrap();
        assert_eq!(jet, Elements::Divide64);
        assert_eq!(arg, ResolvedType::u64());
        assert!(!carry);
    }

    // --- infix_op_jet: Rem ---

    #[test]
    fn infix_op_jet_rem_u8() {
        let (jet, arg, carry) =
            determine_infix_arith_op_jet(&InfixOp::Rem, &ResolvedType::u8()).unwrap();
        assert_eq!(jet, Elements::Modulo8);
        assert_eq!(arg, ResolvedType::u8());
        assert!(!carry);
    }

    #[test]
    fn infix_op_jet_rem_u16() {
        let (jet, arg, carry) =
            determine_infix_arith_op_jet(&InfixOp::Rem, &ResolvedType::u16()).unwrap();
        assert_eq!(jet, Elements::Modulo16);
        assert_eq!(arg, ResolvedType::u16());
        assert!(!carry);
    }

    #[test]
    fn infix_op_jet_rem_u32() {
        let (jet, arg, carry) =
            determine_infix_arith_op_jet(&InfixOp::Rem, &ResolvedType::u32()).unwrap();
        assert_eq!(jet, Elements::Modulo32);
        assert_eq!(arg, ResolvedType::u32());
        assert!(!carry);
    }

    #[test]
    fn infix_op_jet_rem_u64() {
        let (jet, arg, carry) =
            determine_infix_arith_op_jet(&InfixOp::Rem, &ResolvedType::u64()).unwrap();
        assert_eq!(jet, Elements::Modulo64);
        assert_eq!(arg, ResolvedType::u64());
        assert!(!carry);
    }

    // --- infix_op_jet: error cases ---

    #[test]
    fn infix_op_jet_add_wrong_type_unit() {
        let result = determine_infix_arith_op_jet(&InfixOp::Add, &ResolvedType::unit());
        assert!(
            result.is_err(),
            "Expected Err for Add with unit output type"
        );
    }

    #[test]
    fn infix_op_jet_sub_wrong_type_unit() {
        let result = determine_infix_arith_op_jet(&InfixOp::Sub, &ResolvedType::unit());
        assert!(
            result.is_err(),
            "Expected Err for Sub with unit output type"
        );
    }

    #[test]
    fn infix_op_jet_mul_wrong_type_u8() {
        // `*` on u8 inputs would produce u16, so u8 as output type is wrong
        let result = determine_infix_arith_op_jet(&InfixOp::Mul, &ResolvedType::u8());
        assert!(result.is_err(), "Expected Err for Mul with u8 output type");
    }

    #[test]
    fn infix_op_jet_div_wrong_type_bool() {
        let result = determine_infix_arith_op_jet(&InfixOp::Div, &ResolvedType::boolean());
        assert!(
            result.is_err(),
            "Expected Err for Div with bool output type"
        );
    }

    #[test]
    fn infix_op_jet_rem_wrong_type_bool() {
        let result = determine_infix_arith_op_jet(&InfixOp::Rem, &ResolvedType::boolean());
        assert!(
            result.is_err(),
            "Expected Err for Rem with bool output type"
        );
    }
}
