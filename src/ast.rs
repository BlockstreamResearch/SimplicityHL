use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::num::NonZeroUsize;
use std::sync::Arc;

use either::Either;
use miniscript::iter::{Tree, TreeLike};
use simplicity::jet::{Core, Elements, Jet};

use crate::debug::{CallTracker, DebugSymbols, TrackedCallName};
use crate::driver::{CRATE_STR, MAIN_STR};
use crate::error::{Diagnostic, DiagnosticManager, Error, Span, WithSpan};
use crate::jet::{source_type, target_type, JetHL};
use crate::num::{NonZeroPow2Usize, Pow2Usize};
use crate::parse::{MatchPattern, UseDecl, Visibility};
use crate::pattern::Pattern;
use crate::str::{AliasName, FunctionName, Identifier, ModuleName, SymbolName};
use crate::types::{
    AliasedType, EnumInfo, EnumVariantInfo, ResolvedType, StructuralType, TypeConstructible,
    TypeDeconstructible, TypeInner, UIntType,
};
use crate::value::{UIntValue, Value};
use crate::witness::{Parameters, WitnessTypes};
use crate::TemplateProgramWitness;
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
    /// An enum declaration.
    ///
    /// A stub because the declaration was resolved into scope during the
    /// creation of the AST.
    EnumDeclaration,
    /// A function.
    Function(Function),
    Use,
    Module(Vec<Item>),
    /// A placeholder used for error recovery during parsing.
    Ignored,
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
    Witness(TemplateProgramWitness),
    /// Parameter value.
    Parameter(TemplateProgramWitness),
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
    /// Match expression over an enum's variants.
    EnumMatch(EnumMatch),
    /// Construction of an enum variant.
    ///
    /// The enum's definition lives in the type of the expression.
    EnumConstruction(EnumConstruction),
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
#[derive(Clone, Debug, Eq, Hash)]
#[allow(clippy::derived_hash_with_manual_eq)] // see comment on manual `PartialEq` impl below
pub enum CallName {
    /// Jet type.
    Jet(Box<dyn JetHL>),
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

// Manually implemented because the 1.74 (MSRV) derive expands to a body that
// moves out of the non-Copy `Box<dyn Jet>` field, later rustc versions are
// fine.
impl PartialEq for CallName {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Jet(a), Self::Jet(b)) => a == b,
            (Self::UnwrapLeft(a), Self::UnwrapLeft(b)) => a == b,
            (Self::UnwrapRight(a), Self::UnwrapRight(b)) => a == b,
            (Self::IsNone(a), Self::IsNone(b)) => a == b,
            (Self::Unwrap, Self::Unwrap) => true,
            (Self::Assert, Self::Assert) => true,
            (Self::Panic, Self::Panic) => true,
            (Self::Debug, Self::Debug) => true,
            (Self::TypeCast(a), Self::TypeCast(b)) => a == b,
            (Self::Custom(a), Self::Custom(b)) => a == b,
            (Self::Fold(a, b), Self::Fold(c, d)) => a == c && b == d,
            (Self::ArrayFold(a, b), Self::ArrayFold(c, d)) => a == c && b == d,
            (Self::ForWhile(a, b), Self::ForWhile(c, d)) => a == c && b == d,
            _ => false,
        }
    }
}

/// Definition of a custom function.
#[derive(Clone, Debug)]
pub struct CustomFunction {
    params: Arc<[FunctionParam]>,
    ret: ResolvedType,
    /// `None` if the analysis of the body failed.
    body: Option<Arc<Expression>>,
    span: Span,
}

impl CustomFunction {
    /// Access the identifiers of the parameters of the function.
    pub fn params(&self) -> &[FunctionParam] {
        &self.params
    }

    /// Access the declared return type of the function.
    pub fn ret(&self) -> &ResolvedType {
        &self.ret
    }

    /// Access the body of the function.
    ///
    /// ## Panics
    ///
    /// Panics if the analysis of the body failed.
    pub fn body(&self) -> &Expression {
        self.analyzed_body()
            .expect("programs with errors are never built")
    }

    /// Access the body of the function, if its analysis succeeded.
    fn analyzed_body(&self) -> Option<&Expression> {
        self.body.as_deref()
    }

    /// Access the span of the complete function declaration.
    pub fn span(&self) -> &Span {
        &self.span
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

impl_eq_hash!(CustomFunction; params, ret, analyzed_body);

/// Parameter of a function.
#[derive(Clone, Debug)]
pub struct FunctionParam {
    identifier: Identifier,
    ty: ResolvedType,
    span: Span,
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

    /// Access the span of the complete parameter declaration.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(FunctionParam; identifier, ty);

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

/// Match expression over an enum's variants.
#[derive(Clone, Debug)]
pub struct EnumMatch {
    scrutinee: Arc<Expression>,
    /// Arms in variant order (declaration order).
    ///
    /// The order matches the leaf order of the enum's balanced sum.
    arms: Arc<[EnumMatchArm]>,
    span: Span,
}

impl EnumMatch {
    /// Access the expression whose output is dispatched on in the match statement.
    pub fn scrutinee(&self) -> &Expression {
        &self.scrutinee
    }

    /// Access the arms in variant order (declaration order).
    pub fn arms(&self) -> &[EnumMatchArm] {
        &self.arms
    }

    /// Access the span of the match statement.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(EnumMatch; scrutinee, arms);

/// Arm of an [`EnumMatch`] expression, ordered by variant.
#[derive(Clone, Debug)]
pub struct EnumMatchArm {
    /// Pattern binding the variant's payload. [`Pattern::Ignore`] for unit
    /// variants.
    pattern: Pattern,
    body: Arc<Expression>,
    span: Span,
}

impl EnumMatchArm {
    /// Access the pattern that binds the variant's payload.
    pub fn pattern(&self) -> &Pattern {
        &self.pattern
    }

    /// Access the expression that is executed in the match arm.
    pub fn body(&self) -> &Expression {
        &self.body
    }

    /// Access the span of the complete enum match arm.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(EnumMatchArm; pattern, body);

/// Construction of an enum variant: the variant's position and its payload
/// expressions. The enum's definition lives in the type of the enclosing
/// [`SingleExpression`].
#[derive(Clone, Debug)]
pub struct EnumConstruction {
    variant_index: usize,
    payload: Arc<[Arc<Expression>]>,
    span: Span,
}

impl EnumConstruction {
    /// Access the constructed variant's position among the declared variants.
    pub fn variant_index(&self) -> usize {
        self.variant_index
    }

    /// Access the payload expressions. Empty for unit variants.
    pub fn payload(&self) -> &[Arc<Expression>] {
        &self.payload
    }
}

impl_eq_hash!(EnumConstruction; variant_index, payload);

impl AsRef<Span> for EnumConstruction {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for EnumMatch {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

/// Arm of a [`Match`] expression.
#[derive(Clone, Debug)]
pub struct MatchArm {
    pattern: MatchPattern,
    expression: Arc<Expression>,
    span: Span,
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

    /// Access the span of the complete match arm.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(MatchArm; pattern, expression);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum ExprTree<'a> {
    Expression(&'a Expression),
    Block(&'a [Statement], &'a Option<Arc<Expression>>),
    Statement(&'a Statement),
    Assignment(&'a Assignment),
    Single(&'a SingleExpression),
    Call(&'a Call),
    Match(&'a Match),
    EnumMatch(&'a EnumMatch),
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
                S::EnumMatch(enum_match) => Tree::Unary(Self::EnumMatch(enum_match)),
                S::EnumConstruction(construction) => Tree::Nary(
                    construction
                        .payload()
                        .iter()
                        .map(|arg| Self::Expression(arg))
                        .collect(),
                ),
            },
            Self::Call(call) => Tree::Nary(call.args().iter().map(Self::Expression).collect()),
            Self::Match(match_) => Tree::Nary(Arc::new([
                Self::Expression(match_.scrutinee()),
                Self::Expression(match_.left().expression()),
                Self::Expression(match_.right().expression()),
            ])),
            Self::EnumMatch(enum_match) => Tree::Nary(
                std::iter::once(Self::Expression(enum_match.scrutinee()))
                    .chain(
                        enum_match
                            .arms()
                            .iter()
                            .map(|arm| Self::Expression(arm.body())),
                    )
                    .collect(),
            ),
        }
    }
}

/// Object which produces a specific kind of jet.
///
/// All methods return a `dyn Jet` rather than the specific jet so that the trait itself
/// can be object-safe. However, implementors of this trait **must** ensure that
/// all methods return the same kind of jet to avoid panics.
///
/// Users may rely on this property for correctness of their code, though since this
/// is a safe trait, of course they may not rely on it for soundness.
pub trait JetHinter: std::fmt::Debug + Send + Sync {
    /// Attempts to parse a jet from a string.
    fn parse_jet(&self, name: &str) -> Option<Box<dyn JetHL>>;
    /// Constructs an instance of the `verify` jet.
    fn construct_verify(&self) -> Box<dyn JetHL>;
    /// Converts a runtime Simplicity jet back into this hinter's high-level jet.
    fn conjure(&self, jet: &dyn Jet) -> Option<Box<dyn JetHL>>;

    /// Clones the `JetHinter` into a boxed trait object.
    fn clone_box(&self) -> Box<dyn JetHinter>;
}

macro_rules! impl_jet_hinter {
    ($struct_name:ident, $jet_type:ident) => {
        #[derive(Clone, Debug, Default)]
        pub struct $struct_name;

        impl $struct_name {
            pub fn new() -> Self {
                Self
            }
        }

        impl JetHinter for $struct_name {
            fn parse_jet(&self, name: &str) -> Option<Box<dyn JetHL>> {
                $jet_type::parse(name)
                    .ok()
                    .map(|jet| -> Box<dyn JetHL> { Box::new(jet) })
            }

            fn construct_verify(&self) -> Box<dyn JetHL> {
                Box::new($jet_type::Verify)
            }

            fn conjure(&self, jet: &dyn Jet) -> Option<Box<dyn JetHL>> {
                jet.as_any()
                    .downcast_ref::<$jet_type>()
                    .map(|jet| Box::new(*jet) as Box<dyn JetHL>)
            }

            fn clone_box(&self) -> Box<dyn JetHinter> {
                Box::new(Self)
            }
        }
    };
}

impl_jet_hinter!(ElementsJetHinter, Elements);
impl_jet_hinter!(CoreJetHinter, Core);

/// A single module namespace. Handles arbitrary nesting via `submodules`.
#[derive(Clone, Debug, Eq, PartialEq, Default)]
struct ModuleScope {
    aliases: HashMap<AliasName, (ResolvedType, Visibility)>,
    functions: HashMap<FunctionName, (CustomFunction, Visibility)>,
    /// Nested inling `mod` blocks, each becoming a child scope.
    submodules: HashMap<ModuleName, (ModuleScope, Visibility)>,
}

/// Scope for generating the abstract syntax tree.
///
/// The scope is used for:
/// 1. Assigning types to each variable
/// 2. Resolving type aliases
/// 3. Assigning types to each witness expression
/// 4. Resolving calls to custom functions
struct Scope {
    /// Current position in the module tree. Push on `mod` enter, pop on exit.
    /// Empty path means we are at the root (main file) scope.
    module_path: Vec<ModuleName>,

    /// Global scope where items from the main file that live at the root level.
    root: ModuleScope,

    /// Block-level variable scopes. Push on block enter, pop on block exit.
    variables: Vec<HashMap<Identifier, ResolvedType>>,
    parameters: HashMap<TemplateProgramWitness, ResolvedType>,
    witnesses: HashMap<TemplateProgramWitness, ResolvedType>,
    /// Allow enum constructions to name an enum by its declared name even
    /// when that name is not an alias in scope. Enabled only for value
    /// parsing (witness and argument files), which runs without a scope.
    unscoped_enum_names: bool,
    is_main: bool,
    /// The analysis of a `main` function failed, so it is missing from the analyzed items.
    main_failed: bool,
    call_tracker: CallTracker,
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
    pub fn new(jet_hinter: Box<dyn JetHinter>) -> Self {
        Self {
            module_path: Vec::new(),
            root: ModuleScope::default(),
            variables: Vec::new(),
            parameters: HashMap::new(),
            witnesses: HashMap::new(),
            unscoped_enum_names: false,
            is_main: false,
            main_failed: false,
            call_tracker: CallTracker::default(),
            jet_hinter,
            diagnostics: Vec::new(),
        }
    }

    /// Record an error without stopping analysis.
    ///
    /// A failure that was already reported is not recorded again.
    fn report(&mut self, failure: impl Into<Failure>) {
        if let Failure::New(diagnostic) = failure.into() {
            self.diagnostics.push(diagnostic);
        }
    }

    /// Report the error of a failed check that does not prevent building the node.
    fn report_err(&mut self, result: Result<(), Diagnostic>) {
        if let Err(error) = result {
            self.report(error);
        }
    }

    /// Analyze every item, even if some of them fail.
    ///
    /// Every error is reported as soon as it is found. If any item fails,
    /// the caller receives [`Failure::Reported`] and stops as before.
    fn analyze_all<A, T>(
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
    fn for_value_parsing() -> Self {
        Self {
            unscoped_enum_names: true,
            ..Self::default()
        }
    }

    pub fn is_outside_function(&self) -> bool {
        self.variables.is_empty()
    }

    /// Enter a new block inside the current function.
    pub fn enter_block(&mut self) {
        self.variables.push(HashMap::new());
    }

    /// Analyze within a nested block scope and restore the previous scope afterwards
    fn in_block<T>(&mut self, analyze: impl FnOnce(&mut Self) -> T) -> T {
        let outer_depth = self.variables.len();
        self.enter_block();
        let result = analyze(self);
        debug_assert_eq!(
            self.variables.len(),
            outer_depth + 1,
            "Unbalanced nested block scopes"
        );
        self.exit_block();
        debug_assert_eq!(
            self.variables.len(),
            outer_depth,
            "Block scope was not restored"
        );
        result
    }

    /// Analyze within a function scope and restore the outside-function state afterwards
    fn in_function<T>(&mut self, analyze: impl FnOnce(&mut Self) -> T) -> T {
        debug_assert!(self.is_outside_function(), "Already inside a function body");
        let result = self.in_block(analyze);
        debug_assert!(
            self.is_outside_function(),
            "Function scope was not restored"
        );
        result
    }

    /// Analyze within a match-arm scope and restore the enclosing scope afterwards
    fn in_match_arm<T>(&mut self, analyze: impl FnOnce(&mut Self) -> T) -> T {
        self.in_block(analyze)
    }

    /// Push the scope of the main function onto the stack.
    ///
    /// ## Panics
    ///
    /// - Already inside the main function.
    /// - Already inside a function body.
    pub fn enter_main(&mut self) {
        assert!(!self.is_main, "Already inside main function");
        assert!(self.is_outside_function(), "Already inside a function body");
        self.enter_block();
        self.is_main = true;
    }

    /// Analyze within the main-function scope and restore the outside-function state afterwards.
    fn in_main<T>(&mut self, analyze: impl FnOnce(&mut Self) -> T) -> T {
        self.enter_main();
        let result = analyze(self);
        debug_assert!(self.is_main, "Main scope was exited during analysis");
        debug_assert_eq!(
            self.variables.len(),
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

    /// Exit the current block inside the curreent function.
    ///
    /// ## Panics
    ///
    /// - No acive block to exit.
    pub fn exit_block(&mut self) {
        self.variables.pop().expect("No active block to exit");
    }

    /// Pop the scope of the main function from the stack.
    ///
    /// ## Panics
    ///
    /// - Not inside the main function.
    /// - Unclosed nested blocks remain.
    pub fn exit_main(&mut self) {
        assert!(self.is_main, "Current scope is not inside main function");
        self.exit_block();
        self.is_main = false;
        assert!(
            self.is_outside_function(),
            "Current scope is not nested in topmost scope"
        )
    }

    /// Enter a named module, pushing it onto the module path.
    ///
    /// ## Errors
    ///
    /// * [`Error::ModuleRedefined`] A module with this name is already defined in the current scope.
    pub fn enter_module(&mut self, name: ModuleName, visibility: Visibility) -> Result<(), Error> {
        let current = self.current_module_mut();
        if current.submodules.contains_key(&name) {
            return Err(Error::ModuleRedefined { name });
        }

        current
            .submodules
            .insert(name.clone(), (ModuleScope::default(), visibility));
        self.module_path.push(name);
        Ok(())
    }

    /// Analyze within a named module and restore the enclosing module afterwards.
    fn in_module<T>(
        &mut self,
        name: ModuleName,
        visibility: Visibility,
        analyze: impl FnOnce(&mut Self) -> T,
    ) -> Result<T, Error> {
        let outer_depth = self.module_path.len();
        self.enter_module(name.clone(), visibility)?;
        let result = analyze(self);
        debug_assert_eq!(
            self.module_path.len(),
            outer_depth + 1,
            "Unbalanced nested module scopes"
        );
        debug_assert_eq!(
            self.module_path.last(),
            Some(&name),
            "Current module changed during analysis"
        );
        self.exit_module();
        debug_assert_eq!(
            self.module_path.len(),
            outer_depth,
            "Module scope was not restored"
        );
        Ok(result)
    }

    /// Exit the current module, popping it from the module path.
    ///
    /// ## Panics
    ///
    /// Not inside any module.
    pub fn exit_module(&mut self) {
        self.module_path.pop().expect("Not inside any module");
    }

    /// This allows us to perform read-only checks (like redefinitions) and
    /// call `resolve` without taking a premature mutable borrow of `self`.
    fn current_module(&self) -> &ModuleScope {
        self.module_path.iter().fold(&self.root, |scope, segment| {
            &scope.submodules.get(segment).expect("Module not found").0
        })
    }

    /// We use iterations and `O(N)` algorithm, because nested block are not so deep.
    /// It will be strange to see 100 nested blocks, so common `.fold()` will be enough for that.
    fn current_module_mut(&mut self) -> &mut ModuleScope {
        self.module_path
            .iter()
            .fold(&mut self.root, |scope, segment| {
                &mut scope
                    .submodules
                    .get_mut(segment)
                    .expect("Module not found")
                    .0
            })
    }

    // TODO: Consider to optimize it (we definitely can do it)
    /// Resolves a `use` declaration by navigating the module tree, checking visibility,
    /// and importing matching items into the current scope.
    ///
    /// ## Errors
    ///
    /// * [`Error::MissingCrateKeyword`] The import path does not start with the `crate` keyword.
    /// * [`Error::ModuleNotFound`] A module segment in the target path does not exist.
    /// * [`Error::ModuleIsPrivate`] Attempted to navigate into a private module from an unauthorized scope.
    /// * [`Error::MainCannotBeAlias`] Attempted to alias an imported item to the reserved `main` identifier.
    /// * May also return errors propagated from item collection and insertion, such as [`Error::PrivateItem`] or [`Error::RedefinedItem`].
    pub fn resolve_use(&mut self, use_decl: &UseDecl) -> Result<(), Error> {
        let path = use_decl.path();
        if path.first().map(|id| id.as_str()) != Some(CRATE_STR) {
            return Err(Error::MissingCrateKeyword);
        }

        let use_vis = use_decl.visibility().clone();
        let use_decl_items = match use_decl.items() {
            parse::UseItems::Single(elem) => std::slice::from_ref(elem),
            parse::UseItems::List(elems) => elems.as_slice(),
        };

        // Phase 1: navigate to target and collect items. Immutable borrow, dropped at end of block
        // Vec<(ProcessedAlias, ProcessedFunction, ProcessedModule)>
        // where each is Result<(Key, (Value, Visibility)), Error>
        let collected: Vec<_> = {
            // TODO: Part, that can be optimized
            // How many segments do the caller's path and the target's path have in common?
            let shared_prefix_len = self
                .module_path
                .iter()
                .zip(&path[1..])
                .take_while(|(curr, nav)| curr.as_str() == nav.as_str())
                .count();

            let mut target_scope = &self.root;

            for (ind, segment) in path[1..].iter().enumerate() {
                let name = ModuleName::from_ident(segment);

                let (inner, visibility) = target_scope
                    .submodules
                    .get(&name)
                    .ok_or_else(|| Error::ModuleNotFound { name: name.clone() })?;

                if matches!(visibility, Visibility::Private) && shared_prefix_len < ind {
                    return Err(Error::ModuleIsPrivate { name });
                }

                target_scope = inner;
            }

            let mut collected = Vec::with_capacity(use_decl_items.len());
            for (name, aliased) in use_decl_items {
                if aliased.as_ref().is_some_and(|a| a == MAIN_STR) {
                    return Err(Error::MainCannotBeAlias);
                }

                let local_name = aliased.as_ref().unwrap_or(name);

                let alias_res =
                    Self::try_collect_item(name, local_name, &target_scope.aliases, &use_vis);
                let func_res =
                    Self::try_collect_item(name, local_name, &target_scope.functions, &use_vis);
                let mod_res =
                    Self::try_collect_item(name, local_name, &target_scope.submodules, &use_vis);

                collected.push((alias_res, func_res, mod_res));
            }
            collected
        };

        // Phase 2: validate against existing names and stage the complete import.
        // Failed declarations discard these maps without changing the module tree.
        let current = self.current_module();
        let mut pending = ModuleScope::default();
        for (alias_res, func_res, mod_res) in collected {
            Self::resolve_processing_use_items_error(&[
                Self::stage_collected(alias_res, &current.aliases, &mut pending.aliases),
                Self::stage_collected(func_res, &current.functions, &mut pending.functions),
                Self::stage_collected(mod_res, &current.submodules, &mut pending.submodules),
            ])?;
        }

        // Phase 3: commit because every item was resolved successfully
        let current = self.current_module_mut();
        current.aliases.extend(pending.aliases);
        current.functions.extend(pending.functions);
        current.submodules.extend(pending.submodules);

        Ok(())
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

        if matches!(vis, Visibility::Private) {
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

    /// Insert a variable into the current block.
    ///
    /// ## Panics
    ///
    /// - No active block.
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

    /// Retrieves the resolved type of a type alias in the current module scope.
    ///
    /// ## Errors
    ///
    /// * [`Error::UndefinedAlias`]: The alias is not defined in the current scope.
    fn get_alias(&self, name: &AliasName) -> Result<ResolvedType, Error> {
        self.current_module()
            .aliases
            .get(name)
            .map(|(ty, _)| ty.clone())
            .ok_or_else(|| Error::UndefinedAlias { name: name.clone() })
    }

    /// Resolve a type with aliases to a type without aliases.
    ///
    /// ## Errors
    ///
    /// * [`Error::UndefinedAlias`]: The alias is not found in the global registry.
    pub fn resolve(&self, ty: &AliasedType) -> Result<ResolvedType, Error> {
        ty.resolve(|name| self.get_alias(name))
    }

    /// Error if `name` is already defined as an alias in the current module.
    fn check_alias_free(&self, name: &AliasName) -> Result<(), Error> {
        if self.current_module().aliases.contains_key(name) {
            return Err(Error::RedefinedAlias { name: name.clone() });
        }

        Ok(())
    }

    /// Insert a type alias into the current module scope.
    ///
    /// ## Errors
    ///
    /// * [`Error::RedefinedAlias`]: The alias name is already defined in the current scope.
    pub fn insert_alias(&mut self, alias: parse::TypeAlias) -> Result<(), Error> {
        self.check_alias_free(alias.name())?;

        let resolved = self.resolve(alias.ty())?;

        self.current_module_mut()
            .aliases
            .insert(alias.name().clone(), (resolved, alias.visibility().clone()));

        Ok(())
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
    pub fn insert_enum(
        &mut self,
        name: AliasName,
        visibility: Visibility,
        variants: Arc<[EnumVariantInfo]>,
    ) -> Result<(), Error> {
        self.check_alias_free(&name)?;

        let info = EnumInfo::new(Arc::clone(name.as_inner()), variants);
        let resolved = ResolvedType::enumeration(info);

        self.current_module_mut()
            .aliases
            .insert(name, (resolved, visibility));

        Ok(())
    }

    /// Insert a parameter into the global map.
    ///
    /// ## Errors
    ///
    /// * [`Error::ExpressionTypeMismatch`] A parameter of the same name has already been defined as a different type.
    pub fn insert_parameter(
        &mut self,
        name: TemplateProgramWitness,
        ty: ResolvedType,
    ) -> Result<(), Error> {
        match self.parameters.entry(name.clone()) {
            Entry::Occupied(entry) if entry.get() == &ty => Ok(()),
            Entry::Occupied(entry) => Err(Error::ExpressionTypeMismatch {
                expected: entry.get().clone(),
                found: ty,
            }),
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
    /// * [`Error::WitnessOutsideMain`] The current scope is not inside the main function.
    /// * [`Error::WitnessReused`] A witness with the same name has already been defined.
    pub fn insert_witness(
        &mut self,
        name: TemplateProgramWitness,
        ty: ResolvedType,
    ) -> Result<(), Error> {
        if !self.is_main {
            return Err(Error::WitnessOutsideMain);
        }

        match self.witnesses.entry(name.clone()) {
            Entry::Occupied(_) => Err(Error::WitnessReused { name }),
            Entry::Vacant(entry) => {
                entry.insert(ty);
                Ok(())
            }
        }
    }

    /// Consume the scope and build the analyzed program with the given `main` body.
    pub(crate) fn try_into_program(
        mut self,
        main: Result<Expression, Failure>,
        diagnostics: &mut DiagnosticManager,
    ) -> Option<Program> {
        let main = main.map_err(|failure| self.report(failure));
        match main {
            Ok(main) if self.diagnostics.is_empty() => Some(Program {
                main,
                parameters: Parameters::from(self.parameters),
                witness_types: WitnessTypes::from(self.witnesses),
                call_tracker: Arc::new(self.call_tracker),
            }),
            _ => {
                diagnostics.extend(self.diagnostics);
                None
            }
        }
    }

    /// Insert a custom function into the global map.
    ///
    /// ## Errors
    ///
    /// * [`Error::FunctionRedefined`] The function has already been defined.
    pub fn insert_function(
        &mut self,
        name: FunctionName,
        visibility: Visibility,
        function: CustomFunction,
    ) -> Result<(), Error> {
        if self.current_module().functions.contains_key(&name) {
            return Err(Error::FunctionRedefined { name });
        }

        self.current_module_mut()
            .functions
            .insert(name, (function, visibility));
        Ok(())
    }

    /// Retrieves the definition of a custom function, enforcing strict error prioritization.
    ///
    /// ## Errors
    ///
    /// * [`Error::FunctionUndefined`]: The function is not found in the global registry.
    pub fn get_function(&self, name: &FunctionName) -> Result<CustomFunction, Error> {
        self.current_module()
            .functions
            .get(name)
            .map(|(func, _)| func.clone())
            .ok_or_else(|| Error::FunctionUndefined { name: name.clone() })
    }

    /// Track a call expression with its span.
    pub fn track_call<S: AsRef<Span>>(&mut self, span: &S, name: TrackedCallName) {
        self.call_tracker.track_call(*span.as_ref(), name);
    }
}

/// Why the analysis of a node failed.
#[derive(Debug)]
enum Failure {
    /// A new error that was not reported yet.
    New(Diagnostic),
    /// The error was already reported to the scope.
    Reported,
}

impl From<Diagnostic> for Failure {
    fn from(diagnostic: Diagnostic) -> Self {
        Self::New(diagnostic)
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
    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, Failure>;
}

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
            scope.module_path.is_empty(),
            "Unclosed module scopes remain"
        );

        // If we find a duplicate of main function
        match Self::extract_single_main(&items).with_span(from)? {
            Some(main) => Ok(main),
            None if scope.main_failed => Err(Failure::Reported),
            None => Err(Error::MainRequired).with_span(from)?,
        }
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
                    scope.main_failed = true;
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
                scope.resolve_use(use_decl).with_span(use_decl)?;
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

                let variants = scope
                    .analyze_all(decl.variants(), |v, scope| {
                        let payload = scope.analyze_all(v.payload(), |ty, scope| {
                            Ok(scope.resolve(ty).with_span(v)?)
                        })?;
                        Ok(EnumVariantInfo::new(v.name().clone(), Arc::from(payload)))
                    })
                    .map(Arc::from)?;
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
            let params = from
                .params()
                .iter()
                .map(|param| {
                    let identifier = param.identifier().clone();
                    let ty = scope.resolve(param.ty())?;
                    Ok(FunctionParam {
                        identifier,
                        ty,
                        span: *param.span(),
                    })
                })
                .collect::<Result<Arc<[FunctionParam]>, Error>>()
                .with_span(from)?;
            let ret = from
                .ret()
                .as_ref()
                .map(|aliased| scope.resolve(aliased).with_span(from))
                .transpose()?
                .unwrap_or_else(ResolvedType::unit);

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
            let resolved = scope.resolve(aliased).with_span(from)?;
            if !resolved.is_unit() {
                return Err(Error::MainNoOutput).with_span(from)?;
            }
        }

        let body = scope.in_main(|scope| Expression::analyze(from.body(), ty, scope))?;
        Ok(Self::Main(body))
    }
}

impl AbstractSyntaxTree for Statement {
    type From = parse::Statement;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, Failure> {
        assert!(ty.is_unit(), "Statements cannot return anything");
        match from {
            parse::Statement::Assignment(assignment) => {
                Assignment::analyze(assignment, ty, scope).map(Self::Assignment)
            }
            parse::Statement::Expression(expression) => {
                Expression::analyze(expression, ty, scope).map(Self::Expression)
            }
        }
    }
}

impl AbstractSyntaxTree for Assignment {
    type From = parse::Assignment;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, Failure> {
        assert!(ty.is_unit(), "Assignments cannot return anything");
        // The assignment is a statement that returns nothing.
        //
        // However, the expression evaluated in the assignment does have a type,
        // namely the type specified in the assignment.
        let ty_expr = scope.resolve(from.ty()).with_span(from)?;
        let expression = Expression::analyze(from.expression(), &ty_expr, scope)?;
        let typed_variables = from.pattern().is_of_type(&ty_expr).with_span(from)?;
        for (identifier, ty) in typed_variables {
            scope.insert_variable(identifier, ty);
        }

        Ok(Self {
            pattern: from.pattern().clone(),
            expression,
            span: *from.as_ref(),
        })
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
    pub fn analyze_const(from: &parse::Expression, ty: &ResolvedType) -> Result<Self, Diagnostic> {
        // Value files carry no scope, so enum constructions may name the
        // enum by its declared name here — and only here.
        let mut empty_scope = Scope::for_value_parsing();
        let expression = Self::analyze(from, ty, &mut empty_scope)
            .map_err(|failure| empty_scope.report(failure));

        // Value parsing has no diagnostic manager: return the first error analysis found.
        match empty_scope.diagnostics.into_iter().next() {
            Some(error) => Err(error),
            None => Ok(expression.expect("every failure is reported to the scope")),
        }
    }
}

/// Analyze the construction of an enum variant, e.g. `Action::Refresh(sig, 3)`.
///
/// Analysis is type-directed. The expected type must be an enum, and the written enum name must name it.
/// In program source that means an alias in lexical scope, the same rule
/// matches follow. In witness and argument files, which are parsed without
/// a scope ([`Scope::unscoped_enum_names`]), the enum's declared name
/// itself also matches.
fn analyze_enum_construction(
    construction: &parse::EnumConstruction,
    ty: &ResolvedType,
    scope: &mut Scope,
) -> Result<EnumConstruction, Failure> {
    let span = *construction.span();
    let Some(info) = ty.as_enum() else {
        return Err(Error::ExpressionUnexpectedType { ty: ty.clone() }).with_span(span)?;
    };

    // The written name must be the expected enum's.
    // Enums are declared at the top level, so only a single identifier can name one.
    // An alias in scope must resolve to the expected type.
    // Without a scope (witness and argument files) the declared name itself matches.
    let written = construction.enum_path_string();
    let names_expected_enum = match construction.enum_path() {
        [single] => {
            let alias = AliasName::from_ident(single);
            match scope.get_alias(&alias) {
                Ok(resolved) if &resolved == ty => true,
                Ok(resolved) => Err(Error::ExpressionTypeMismatch {
                    expected: ty.clone(),
                    found: resolved,
                })
                .with_span(span)?,
                Err(_) => scope.unscoped_enum_names && written == info.name(),
            }
        }
        _ => false,
    };
    if !names_expected_enum {
        Err(Error::Grammar {
            msg: format!("`{written}` does not name enum `{}`", info.name()),
        })
        .with_span(span)?;
    }

    let (variant_index, variant) = info
        .variant(construction.variant())
        .ok_or_else(|| enum_variant_error(construction.variant().as_str(), info))
        .with_span(span)?;
    if construction.args().len() != variant.payload().len() {
        Err(Error::Grammar {
            msg: format!(
                "variant `{}` of enum `{}` carries {} payload value(s), found {}",
                construction.variant(),
                info.name(),
                variant.payload().len(),
                construction.args().len()
            ),
        })
        .with_span(span)?;
    }

    let payload = scope
        .analyze_all(
            construction.args().iter().zip(variant.payload()),
            |(arg, payload_ty), scope| Expression::analyze(arg, payload_ty, scope).map(Arc::new),
        )
        .map(Arc::from)?;

    Ok(EnumConstruction {
        variant_index,
        payload,
        span,
    })
}

/// Do `a` and `b` carry the same enum at every corresponding position?
///
/// Casts prove structural equality, but enums are nominal: a cast may
/// freely reshape enum-free structure (`(u16, u16)` into `u32`), while
/// every enum must map to itself at its position — otherwise variants
/// would convert by ordinal position, silently bypassing declared
/// identity.
///
/// Conservative on shape changes: an enum aligned across a reshaped
/// subtree (such as an array-to-tuple conversion) is rejected even when
/// the enum itself is unchanged.
///
/// TODO(enums): this walk aligns high-level constructors, so casts that
/// reshape only the container around an enum are rejected even when the
/// enum keeps its structural position, e.g. `Option<E>` to
/// `Either<(), E>`. A provenance-aware comparison — structural skeletons
/// with nominal enum leaves — would accept those; keep `List` types
/// conservative either way, since their partition layout complicates
/// position alignment.
fn cast_preserves_enum_identity(source: &ResolvedType, target: &ResolvedType) -> bool {
    match (source.as_inner(), target.as_inner()) {
        (TypeInner::Enum(src), TypeInner::Enum(dst)) => src == dst,
        (TypeInner::Enum(_), _) | (_, TypeInner::Enum(_)) => false,
        (TypeInner::Option(src), TypeInner::Option(dst)) => cast_preserves_enum_identity(src, dst),
        (TypeInner::Either(src_l, src_r), TypeInner::Either(dst_l, dst_r)) => {
            cast_preserves_enum_identity(src_l, dst_l) && cast_preserves_enum_identity(src_r, dst_r)
        }
        (TypeInner::Tuple(src), TypeInner::Tuple(dst)) if src.len() == dst.len() => src
            .iter()
            .zip(dst.iter())
            .all(|(src_el, dst_el)| cast_preserves_enum_identity(src_el, dst_el)),
        (TypeInner::Array(src, src_len), TypeInner::Array(dst, dst_len)) if src_len == dst_len => {
            cast_preserves_enum_identity(src, dst)
        }
        (TypeInner::List(src, src_bound), TypeInner::List(dst, dst_bound))
            if src_bound == dst_bound =>
        {
            cast_preserves_enum_identity(src, dst)
        }
        // Differently shaped subtrees may convert freely as long as no
        // enum is involved on either side.
        _ => !source.contains_enum() && !target.contains_enum(),
    }
}

/// The given string does not name a variant of the enum.
fn enum_variant_error(found: &str, info: &EnumInfo) -> Error {
    let variants = info
        .variants()
        .iter()
        .map(|variant| variant.name().to_string())
        .collect::<Vec<_>>()
        .join(", ");
    Error::Grammar {
        msg: format!(
            "`{found}` is not a variant of enum `{}`; expected one of: {variants}",
            info.name()
        ),
    }
}

impl AbstractSyntaxTree for Expression {
    type From = parse::Expression;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, Failure> {
        match from.inner() {
            parse::ExpressionInner::Single(single) => {
                let ast_single = SingleExpression::analyze(single, ty, scope)?;
                Ok(Self {
                    ty: ty.clone(),
                    inner: ExpressionInner::Single(ast_single),
                    span: *from.as_ref(),
                })
            }
            parse::ExpressionInner::Block(statements, expression) => {
                let (ast_statements, ast_expression) =
                    scope.in_block(|scope| -> Result<_, Failure> {
                        let ast_statements = statements
                            .iter()
                            .map(|s| Statement::analyze(s, &ResolvedType::unit(), scope))
                            .collect::<Result<Arc<[Statement]>, Failure>>()?;
                        let ast_expression = match expression {
                            Some(expression) => Expression::analyze(expression, ty, scope)
                                .map(Arc::new)
                                .map(Some),
                            None if ty.is_unit() => Ok(None),
                            None => Err(Error::ExpressionTypeMismatch {
                                expected: ty.clone(),
                                found: ResolvedType::unit(),
                            })
                            .with_span(from)
                            .map_err(Failure::from),
                        }?;
                        Ok((ast_statements, ast_expression))
                    })?;

                Ok(Self {
                    ty: ty.clone(),
                    inner: ExpressionInner::Block(ast_statements, ast_expression),
                    span: *from.as_ref(),
                })
            }
        }
    }
}

impl AbstractSyntaxTree for SingleExpression {
    type From = parse::SingleExpression;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, Failure> {
        let inner = match from.inner() {
            parse::SingleExpressionInner::Boolean(bit) => {
                if !ty.is_boolean() {
                    Err(Error::ExpressionTypeMismatch {
                        expected: ty.clone(),
                        found: ResolvedType::boolean(),
                    })
                    .with_span(from)?;
                }
                SingleExpressionInner::Constant(Value::from(*bit))
            }
            parse::SingleExpressionInner::Decimal(decimal) => {
                let ty = ty
                    .as_integer()
                    .ok_or(Error::ExpressionUnexpectedType { ty: ty.clone() })
                    .with_span(from)?;
                UIntValue::parse_decimal(decimal, ty)
                    .with_span(from)
                    .map(Value::from)
                    .map(SingleExpressionInner::Constant)?
            }
            parse::SingleExpressionInner::Binary(bits) => {
                let ty = ty
                    .as_integer()
                    .ok_or(Error::ExpressionUnexpectedType { ty: ty.clone() })
                    .with_span(from)?;
                let value = UIntValue::parse_binary(bits, ty).with_span(from)?;
                SingleExpressionInner::Constant(Value::from(value))
            }
            parse::SingleExpressionInner::Hexadecimal(bytes) => {
                let value = Value::parse_hexadecimal(bytes, ty).with_span(from)?;
                SingleExpressionInner::Constant(value)
            }
            parse::SingleExpressionInner::Witness(name) => {
                scope
                    .insert_witness(name.clone(), ty.clone())
                    .with_span(from)?;
                SingleExpressionInner::Witness(name.clone())
            }
            parse::SingleExpressionInner::Parameter(name) => {
                scope
                    .insert_parameter(name.shallow_clone(), ty.clone())
                    .with_span(from)?;
                SingleExpressionInner::Parameter(name.shallow_clone())
            }
            parse::SingleExpressionInner::Variable(identifier) => {
                let bound_ty = scope
                    .get_variable(identifier)
                    .ok_or(Error::UndefinedVariable {
                        identifier: identifier.clone(),
                    })
                    .with_span(from)?;
                if ty != bound_ty {
                    Err(Error::ExpressionTypeMismatch {
                        expected: ty.clone(),
                        found: bound_ty.clone(),
                    })
                    .with_span(from)?;
                }
                scope.insert_variable(identifier.clone(), ty.clone());
                SingleExpressionInner::Variable(identifier.clone())
            }
            parse::SingleExpressionInner::Expression(parse) => {
                Expression::analyze(parse, ty, scope)
                    .map(Arc::new)
                    .map(SingleExpressionInner::Expression)?
            }
            parse::SingleExpressionInner::Tuple(tuple) => {
                let types = ty
                    .as_tuple()
                    .ok_or(Error::ExpressionUnexpectedType { ty: ty.clone() })
                    .with_span(from)?;
                if tuple.len() != types.len() {
                    return Err(Error::ExpressionUnexpectedType { ty: ty.clone() })
                        .with_span(from)?;
                }

                scope
                    .analyze_all(
                        tuple.iter().zip(types.iter()),
                        |(el_parse, el_ty), scope| Expression::analyze(el_parse, el_ty, scope),
                    )
                    .map(Arc::from)
                    .map(SingleExpressionInner::Tuple)?
            }
            parse::SingleExpressionInner::Array(array) => {
                let (el_ty, size) = ty
                    .as_array()
                    .ok_or(Error::ExpressionUnexpectedType { ty: ty.clone() })
                    .with_span(from)?;

                // The element type is known even if the size is wrong,
                // so the elements are analyzed either way.
                if array.len() != size {
                    scope.report(
                        Error::ExpressionUnexpectedType { ty: ty.clone() }
                            .with_span(*from.as_ref()),
                    );
                }

                scope
                    .analyze_all(array.iter(), |el_parse, scope| {
                        Expression::analyze(el_parse, el_ty, scope)
                    })
                    .map(Arc::from)
                    .map(SingleExpressionInner::Array)?
            }
            parse::SingleExpressionInner::List(list) => {
                let (el_ty, bound) = ty
                    .as_list()
                    .ok_or(Error::ExpressionUnexpectedType { ty: ty.clone() })
                    .with_span(from)?;

                if bound.get() <= list.len() {
                    scope.report(
                        Error::ExpressionUnexpectedType { ty: ty.clone() }
                            .with_span(*from.as_ref()),
                    );
                }

                scope
                    .analyze_all(list.iter(), |e, scope| Expression::analyze(e, el_ty, scope))
                    .map(Arc::from)
                    .map(SingleExpressionInner::List)?
            }
            parse::SingleExpressionInner::Either(either) => {
                let (ty_l, ty_r) = ty
                    .as_either()
                    .ok_or(Error::ExpressionUnexpectedType { ty: ty.clone() })
                    .with_span(from)?;
                match either {
                    Either::Left(parse_l) => Expression::analyze(parse_l, ty_l, scope)
                        .map(Arc::new)
                        .map(Either::Left),
                    Either::Right(parse_r) => Expression::analyze(parse_r, ty_r, scope)
                        .map(Arc::new)
                        .map(Either::Right),
                }
                .map(SingleExpressionInner::Either)?
            }
            parse::SingleExpressionInner::Option(maybe_parse) => {
                let ty = ty
                    .as_option()
                    .ok_or(Error::ExpressionUnexpectedType { ty: ty.clone() })
                    .with_span(from)?;
                match maybe_parse {
                    Some(parse) => {
                        Some(Expression::analyze(parse, ty, scope).map(Arc::new)).transpose()
                    }
                    None => Ok(None),
                }
                .map(SingleExpressionInner::Option)?
            }
            parse::SingleExpressionInner::Call(call) => {
                Call::analyze(call, ty, scope).map(SingleExpressionInner::Call)?
            }
            parse::SingleExpressionInner::Match(match_) => {
                Match::analyze(match_, ty, scope).map(SingleExpressionInner::Match)?
            }
            parse::SingleExpressionInner::EnumConstruction(construction) => {
                analyze_enum_construction(construction, ty, scope)
                    .map(SingleExpressionInner::EnumConstruction)?
            }
            parse::SingleExpressionInner::EnumMatch(enum_match) => {
                EnumMatch::analyze(enum_match, ty, scope).map(SingleExpressionInner::EnumMatch)?
            }
        };

        Ok(Self {
            inner,
            ty: ty.clone(),
            span: *from.as_ref(),
        })
    }
}

impl AbstractSyntaxTree for EnumMatch {
    type From = parse::EnumMatch;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, Failure> {
        let arms = from.arms();
        let span = *from.span();
        debug_assert!(!arms.is_empty(), "the parser rejects empty enum matches");

        let enum_name = arms[0].enum_path_string();
        let [single] = arms[0].enum_path() else {
            return Err(Error::Grammar {
                msg: format!(
                    "`{enum_name}` does not name an enum; enums are declared at the \
                     top level, so match arms name them by a single identifier"
                ),
            })
            .with_span(span)
            .map_err(Failure::from);
        };
        let alias = AliasName::from_ident(single);
        let enum_ty = scope.get_alias(&alias).with_span(span)?;
        let info = match enum_ty.as_enum() {
            Some(info) => info.clone(),
            None => Err(Error::Grammar {
                msg: format!(
                    "`{enum_name}` is not an enum, so match arms of the form \
                         `{enum_name}::Variant` cannot apply to it"
                ),
            })
            .with_span(span)?,
        };

        // One slot per variant, in declaration order.
        // the order of the leaves of the enum's balanced sum.
        let mut arms_by_index: Vec<Option<&parse::EnumMatchArm>> =
            vec![None; info.variants().len()];

        scope.analyze_all(arms, |arm, _scope| {
            if arm.enum_path() != arms[0].enum_path() {
                Err(Error::Grammar {
                    msg: format!(
                        "all match arms must use the same enum; expected '{}', found '{}'",
                        enum_name,
                        arm.enum_path_string()
                    ),
                })
                .with_span(arm)?;
            }
            let (index, _) = info
                .variant(arm.variant())
                .ok_or_else(|| Error::Grammar {
                    msg: format!(
                        "variant '{}' is not defined in enum '{}'",
                        arm.variant(),
                        enum_name
                    ),
                })
                .with_span(arm)?;
            let slot = &mut arms_by_index[index];
            if slot.is_some() {
                Err(Error::Grammar {
                    msg: format!("duplicate arm for variant '{}'", arm.variant()),
                })
                .with_span(arm)?;
            }

            *slot = Some(arm);
            Ok(())
        })?;

        // One collect: Some(arms) iff every variant is covered.
        let covered: Option<Vec<&parse::EnumMatchArm>> = arms_by_index.iter().copied().collect();
        let Some(covered) = covered else {
            let missing: Vec<String> = arms_by_index
                .iter()
                .zip(info.variants())
                .filter(|(slot, _)| slot.is_none())
                .map(|(_, variant)| format!("'{}'", variant.name()))
                .collect();
            return Err(Error::Grammar {
                msg: format!(
                    "enum match on '{}' must cover all {} variants; missing: {}",
                    enum_name,
                    info.variants().len(),
                    missing.join(", ")
                ),
            })
            .with_span(span)
            .map_err(Failure::from);
        };

        // Analyze the scrutinee against the nominal enum type, so that
        // matching a value of a different enum (or any other type) against
        // this enum's variants is a type error.
        let scrutinee = Expression::analyze(from.scrutinee(), &enum_ty, scope).map(Arc::new)?;

        let arm_asts = scope
            .analyze_all(
                covered.into_iter().zip(info.variants()),
                |(arm, variant), scope| {
                    let arm_span = *arm.span();
                    let pattern = analyze_enum_arm_bindings(arm, variant, scope, arm_span)?;
                    scope.in_match_arm(|scope| {
                        let payload_ty = variant.payload_type();
                        let typed_variables = pattern.is_of_type(payload_ty).with_span(arm_span)?;
                        for (identifier, variable_ty) in typed_variables {
                            scope.insert_variable(identifier, variable_ty);
                        }
                        let body =
                            Expression::analyze(arm.expression(), ty, scope).map(Arc::new)?;
                        Ok(EnumMatchArm {
                            pattern,
                            body,
                            span: arm_span,
                        })
                    })
                },
            )
            .map(Arc::from)?;

        Ok(Self {
            scrutinee,
            arms: arm_asts,
            span,
        })
    }
}

/// Check an enum match arm's payload bindings against the variant's declared
/// payload types and combine them into one pattern for the variant's leaf.
///
/// Unit variants bind nothing ([`Pattern::Ignore`]); a single binding stands
/// alone; multiple bindings form a tuple pattern, matching the tuple that a
/// multi-payload variant carries at its leaf.
fn analyze_enum_arm_bindings(
    arm: &parse::EnumMatchArm,
    variant: &EnumVariantInfo,
    scope: &Scope,
    span: Span,
) -> Result<Pattern, Diagnostic> {
    if arm.bindings().len() != variant.payload().len() {
        return Err(Error::Grammar {
            msg: format!(
                "variant '{}' of enum '{}' carries {} payload value(s), \
                 but the arm binds {}",
                arm.variant(),
                arm.enum_path_string(),
                variant.payload().len(),
                arm.bindings().len()
            ),
        })
        .with_span(span);
    }

    let mut patterns = Vec::with_capacity(arm.bindings().len());
    for ((pattern, declared), payload_ty) in arm.bindings().iter().zip(variant.payload()) {
        let declared = scope.resolve(declared).with_span(span)?;
        if &declared != payload_ty {
            return Err(Error::ExpressionTypeMismatch {
                expected: payload_ty.clone(),
                found: declared,
            })
            .with_span(span);
        }
        patterns.push(pattern.clone());
    }

    let pattern = match patterns.len() {
        0 => Pattern::Ignore,
        1 => patterns[0].clone(),
        _ => Pattern::tuple(patterns),
    };
    Ok(pattern)
}

impl AbstractSyntaxTree for Call {
    type From = parse::Call;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, Failure> {
        fn check_argument_types(
            parse_args: &[parse::Expression],
            expected_tys: &[ResolvedType],
        ) -> Result<(), Error> {
            if parse_args.len() == expected_tys.len() {
                Ok(())
            } else {
                Err(Error::InvalidNumberOfArguments {
                    expected: expected_tys.len(),
                    found: parse_args.len(),
                })
            }
        }

        fn check_output_type(
            observed_ty: &ResolvedType,
            expected_ty: &ResolvedType,
        ) -> Result<(), Error> {
            if observed_ty == expected_ty {
                Ok(())
            } else {
                Err(Error::ExpressionTypeMismatch {
                    expected: expected_ty.clone(),
                    found: observed_ty.clone(),
                })
            }
        }

        fn analyze_arguments(
            parse_args: &[parse::Expression],
            args_tys: &[ResolvedType],
            scope: &mut Scope,
        ) -> Result<Arc<[Expression]>, Failure> {
            scope
                .analyze_all(
                    parse_args.iter().zip(args_tys.iter()),
                    |(arg_parse, arg_ty), scope| Expression::analyze(arg_parse, arg_ty, scope),
                )
                .map(Arc::from)
        }

        let name = CallName::analyze(from, scope)?;
        let args = match name.clone() {
            CallName::Jet(jet) => {
                let args_tys = source_type(&*jet)
                    .iter()
                    .map(AliasedType::resolve_builtin)
                    .collect::<Result<Vec<ResolvedType>, AliasName>>()
                    .map_err(|alias| Error::UndefinedAlias { name: alias })
                    .with_span(from)?;
                let out_ty = target_type(&*jet)
                    .resolve_builtin()
                    .map_err(|alias| Error::UndefinedAlias { name: alias })
                    .with_span(from)?;
                scope.report_err(check_output_type(&out_ty, ty).with_span(from));

                check_argument_types(from.args(), &args_tys).with_span(from)?;
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
                let out_ty = ResolvedType::boolean();
                scope.report_err(check_output_type(&out_ty, ty).with_span(from));

                check_argument_types(from.args(), &args_tys).with_span(from)?;
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
                let out_ty = ResolvedType::unit();
                scope.report_err(check_output_type(&out_ty, ty).with_span(from));

                check_argument_types(from.args(), &args_tys).with_span(from)?;
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
                // Casts prove structural equality, but enums are nominal:
                // every enum must map to itself at its structural position
                // (see `cast_preserves_enum_identity`), else same-shaped
                // enums would convert variants by ordinal position.
                if !cast_preserves_enum_identity(&source, ty)
                    || StructuralType::from(&source) != StructuralType::from(ty)
                {
                    scope.report(
                        Error::InvalidCast {
                            source: source.clone(),
                            target: ty.clone(),
                        }
                        .with_span(*from.as_ref()),
                    );
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
                let out_ty = function.ret();
                scope.report_err(check_output_type(out_ty, ty).with_span(from));

                check_argument_types(from.args(), &args_ty).with_span(from)?;
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

                let out_ty = function.ret();
                scope.report_err(check_output_type(out_ty, ty).with_span(from));

                check_argument_types(from.args(), &args_ty).with_span(from)?;
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

                let out_ty = function.ret();
                scope.report_err(check_output_type(out_ty, ty).with_span(from));

                check_argument_types(from.args(), &args_ty).with_span(from)?;
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

                let out_ty = function.ret();
                scope.report_err(check_output_type(out_ty, ty).with_span(from));

                check_argument_types(from.args(), &args_ty).with_span(from)?;
                analyze_arguments(from.args(), &args_ty, scope)?
            }
        };

        Ok(Self {
            name,
            args,
            span: *from.as_ref(),
        })
    }
}

impl CallName {
    // Take parse::Call, so we have access to the span for pretty errors
    fn analyze(from: &parse::Call, scope: &mut Scope) -> Result<Self, Diagnostic> {
        match from.name() {
            parse::CallName::Jet(name) => match scope.jet_hinter.parse_jet(name.as_inner()) {
                Some(jet) if !jet.is_disabled() => Ok(Self::Jet(jet)),
                _ => Err(Error::JetDoesNotExist { name: name.clone() }).with_span(from),
            },
            parse::CallName::UnwrapLeft(right_ty) => scope
                .resolve(right_ty)
                .map(Self::UnwrapLeft)
                .with_span(from),
            parse::CallName::UnwrapRight(left_ty) => scope
                .resolve(left_ty)
                .map(Self::UnwrapRight)
                .with_span(from),
            parse::CallName::IsNone(some_ty) => {
                scope.resolve(some_ty).map(Self::IsNone).with_span(from)
            }
            parse::CallName::Unwrap => Ok(Self::Unwrap),
            parse::CallName::Assert => Ok(Self::Assert),
            parse::CallName::Panic => Ok(Self::Panic),
            parse::CallName::Debug => Ok(Self::Debug),
            parse::CallName::TypeCast(target) => {
                scope.resolve(target).map(Self::TypeCast).with_span(from)
            }
            parse::CallName::Custom(name) => {
                scope.get_function(name).map(Self::Custom).with_span(from)
            }
            parse::CallName::ArrayFold(name, size) => {
                let function = scope.get_function(name).with_span(from)?;
                // A function that is used in a array fold has the signature:
                //   fn f(element: E, accumulator: A) -> A
                if function.params().len() != 2 || function.params()[1].ty() != function.ret() {
                    Err(Error::FunctionNotFoldable { name: name.clone() }).with_span(from)
                } else {
                    Ok(Self::ArrayFold(function, *size))
                }
            }
            parse::CallName::Fold(name, bound) => {
                let function = scope.get_function(name).with_span(from)?;
                // A function that is used in a list fold has the signature:
                //   fn f(element: E, accumulator: A) -> A
                if function.params().len() != 2 || function.params()[1].ty() != function.ret() {
                    Err(Error::FunctionNotFoldable { name: name.clone() }).with_span(from)
                } else {
                    Ok(Self::Fold(function, *bound))
                }
            }
            parse::CallName::ForWhile(name) => {
                let function = scope.get_function(name).with_span(from)?;
                // A function that is used in a for-while loop has the signature:
                //   fn f(accumulator: A, readonly_context: C, counter: u{N}) -> Either<B, A>
                // where
                //   N is a power of two
                if function.params().len() != 3 {
                    return Err(Error::FunctionNotLoopable { name: name.clone() }).with_span(from);
                }
                match function.ret().as_either() {
                    Some((_, out_r)) if out_r == function.params().first().unwrap().ty() => {}
                    _ => {
                        return Err(Error::FunctionNotLoopable { name: name.clone() })
                            .with_span(from);
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
                    ) => Ok(Self::ForWhile(function, int_ty.bit_width())),
                    _ => Err(Error::FunctionNotLoopable { name: name.clone() }).with_span(from),
                }
            }
        }
    }
}

impl AbstractSyntaxTree for Match {
    type From = parse::Match;

    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope) -> Result<Self, Failure> {
        let scrutinee_ty = from.scrutinee_type();
        let scrutinee_ty = scope.resolve(&scrutinee_ty).with_span(from)?;
        let scrutinee =
            Expression::analyze(from.scrutinee(), &scrutinee_ty, scope).map(Arc::new)?;

        let analyze_arm = |arm: &parse::MatchArm, scope: &mut Scope| {
            scope.in_match_arm(|scope| {
                if let Some((pattern, arm_ty)) = arm.pattern().as_typed_pattern() {
                    let arm_ty = scope.resolve(arm_ty).with_span(arm)?;
                    let typed_variables = pattern.is_of_type(&arm_ty).with_span(arm)?;

                    for (identifier, ty) in typed_variables {
                        scope.insert_variable(identifier, ty);
                    }
                }
                Expression::analyze(arm.expression(), ty, scope).map(Arc::new)
            })
        };

        // Each arm declares the types of its bindings, so the arms are independent:
        // analyze both and report the errors of each.
        let ast_l = analyze_arm(from.left(), scope).map_err(|failure| scope.report(failure));
        let ast_r = analyze_arm(from.right(), scope).map_err(|failure| scope.report(failure));
        let (Ok(ast_l), Ok(ast_r)) = (ast_l, ast_r) else {
            return Err(Failure::Reported)?;
        };

        Ok(Self {
            scrutinee,
            left: MatchArm {
                pattern: from.left().pattern().clone(),
                expression: ast_l,
                span: *from.left().span(),
            },
            right: MatchArm {
                pattern: from.right().pattern().clone(),
                expression: ast_r,
                span: *from.right().span(),
            },
            span: *from.as_ref(),
        })
    }
}

impl AsRef<Span> for Assignment {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for FunctionParam {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for CustomFunction {
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

impl AsRef<Span> for MatchArm {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for EnumMatchArm {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

#[cfg(test)]
mod span_tests {
    use crate::parse::ParseFromStr;

    use super::*;

    #[test]
    fn analyzed_custom_function_preserves_declaration_and_parameter_spans() {
        let source = "fn helper(value: u8) -> u8 { value }";
        let parsed = parse::Function::parse_from_str(source).expect("function parses");
        let mut scope = Scope::new(Box::new(ElementsJetHinter));

        Function::analyze(&parsed, &ResolvedType::unit(), &mut scope).expect("function analyzes");
        let function = scope
            .get_function(parsed.name())
            .expect("function is registered in scope");

        assert_eq!(function.span().to_slice(source), Some(source));
        assert_eq!(
            function.params()[0].span().to_slice(source),
            Some("value: u8")
        );
    }

    #[test]
    fn analyzed_match_arms_preserve_their_parsed_spans() {
        let source = r#"fn main() {
    let input: Either<u8, u8> = Left(1);
    match input {
        Left(left: u8) => {},
        Right(right: u8) => {},
    }
}"#;
        let parsed = parse::Program::parse_from_str(source).expect("program parses");
        let program = Program::analyze(
            &parsed,
            Box::new(ElementsJetHinter),
            &mut DiagnosticManager::new(),
        )
        .expect("program analyzes");

        let ExpressionInner::Block(_, Some(last)) = program.main().inner() else {
            panic!("main body should end in a match");
        };
        let ExpressionInner::Single(single) = last.inner() else {
            panic!("match should be a single expression");
        };
        let SingleExpressionInner::Match(match_) = single.inner() else {
            panic!("expected a binary match");
        };

        assert_eq!(
            match_.left().span().to_slice(source),
            Some("Left(left: u8) => {},")
        );
        assert_eq!(
            match_.right().span().to_slice(source),
            Some("Right(right: u8) => {},")
        );
    }

    #[test]
    fn analyzed_enum_match_arms_preserve_their_parsed_spans() {
        let source = r#"enum Choice { First, Second, }
fn main() {
    let input: Choice = Choice::First;
    match input {
        Choice::First => {},
        Choice::Second => {},
    }
}"#;
        let parsed = parse::Program::parse_from_str(source).expect("program parses");
        let program = Program::analyze(
            &parsed,
            Box::new(ElementsJetHinter),
            &mut DiagnosticManager::new(),
        )
        .expect("program analyzes");

        let ExpressionInner::Block(_, Some(last)) = program.main().inner() else {
            panic!("main body should end in an enum match");
        };
        let ExpressionInner::Single(single) = last.inner() else {
            panic!("enum match should be a single expression");
        };
        let SingleExpressionInner::EnumMatch(match_) = single.inner() else {
            panic!("expected an enum match");
        };

        assert_eq!(
            match_.arms()[0].span().to_slice(source),
            Some("Choice::First => {},")
        );
        assert_eq!(
            match_.arms()[1].span().to_slice(source),
            Some("Choice::Second => {},")
        );
    }
}

#[cfg(test)]
mod multi_error_tests {
    use crate::test_utils::assert_errors;

    #[test]
    fn tuple_elements() {
        assert_errors(
            "fn main() { let pair: (u32, u32) = (x, y); }",
            &["Variable `x` is not defined", "Variable `y` is not defined"],
        );
    }

    #[test]
    fn array_length_and_elements() {
        assert_errors(
            "fn main() { let array: [u32; 3] = [x, y]; }",
            &[
                "Expected expression of type `[u32; 3]`; found something else",
                "Variable `x` is not defined",
                "Variable `y` is not defined",
            ],
        );
    }

    #[test]
    fn call_output_type_and_arguments() {
        assert_errors(
            "fn main() { let sum: bool = jet::add_32(a, b); }",
            &[
                "Expected expression of type `bool`, found type `(bool, u32)`",
                "Variable `a` is not defined",
                "Variable `b` is not defined",
            ],
        );
    }

    #[test]
    fn nested_errors_are_reported_once() {
        assert_errors(
            "fn main() { let pair: (u32, u32) = (jet::add_32(a, 1), b); }",
            &[
                "Expected expression of type `u32`, found type `(bool, u32)`",
                "Variable `a` is not defined",
                "Variable `b` is not defined",
            ],
        );
    }

    #[test]
    fn match_arms() {
        assert_errors(
            "fn main() {
                let input: Either<u32, u32> = Left(1);
                let result: u32 = match input {
                    Left(l: u32) => left_var,
                    Right(r: u32) => right_var,
                };
            }",
            &[
                "Variable `left_var` is not defined",
                "Variable `right_var` is not defined",
            ],
        );
    }

    #[test]
    fn enum_match_misspelled_variants_are_not_reported_as_missing() {
        assert_errors(
            "enum Color { Red, Green, Blue }
            fn main() {
                let c: Color = Color::Red;
                match c {
                    Color::Rd => {},
                    Color::Gren => {},
                    Color::Blue => {},
                }
            }",
            &[
                "Grammar error: variant 'Rd' is not defined in enum 'Color'",
                "Grammar error: variant 'Gren' is not defined in enum 'Color'",
            ],
        );
    }

    #[test]
    fn enum_match_arms() {
        assert_errors(
            "enum Color { Red, Green }
            fn main() {
                let c: Color = Color::Red;
                let n: u32 = match c {
                    Color::Red => x,
                    Color::Green => y,
                };
            }",
            &["Variable `x` is not defined", "Variable `y` is not defined"],
        );
    }

    #[test]
    fn main_visibility_and_inputs() {
        // The body is not analyzed: it could use the parameters,
        // which would only repeat the error about inputs.
        assert_errors(
            "pub fn main(a: u32) -> u32 { undefined }",
            &[
                "Main function cannot be public",
                "Main function takes no input parameters",
            ],
        );
    }

    #[test]
    fn main_visibility_and_body() {
        assert_errors(
            "pub fn main() { let a: u32 = undefined; }",
            &[
                "Main function cannot be public",
                "Variable `undefined` is not defined",
            ],
        );
    }

    #[test]
    fn enum_duplicate_variants() {
        assert_errors(
            "enum Color { Red, Red, Green, Green }
            fn main() {}",
            &[
                "Grammar error: enum 'Color' has duplicate variant name 'Red'",
                "Grammar error: enum 'Color' has duplicate variant name 'Green'",
            ],
        );
    }

    #[test]
    fn enum_payload_types() {
        assert_errors(
            "enum Shape { Circle(Radius), Square(Side) }
            fn main() {}",
            &[
                "Type alias `Radius` is not defined",
                "Type alias `Side` is not defined",
            ],
        );
    }

    #[test]
    fn failed_check_does_not_stop_the_next_statement() {
        assert_errors(
            "fn main() {
                let b: bool = jet::add_32(1, 2);
                let c: u32 = z;
            }",
            &[
                "Expected expression of type `bool`, found type `(bool, u32)`",
                "Variable `z` is not defined",
            ],
        );
    }

    #[test]
    fn every_broken_function_is_reported() {
        assert_errors(
            "fn a() -> u32 { x }
            fn b() -> u32 { y }
            fn main() {}",
            &["Variable `x` is not defined", "Variable `y` is not defined"],
        );
    }

    #[test]
    fn wrong_call_of_function_with_broken_body_is_reported() {
        assert_errors(
            "fn f(a: u32) -> u32 { x }
            fn main() { let y: bool = f(true); }",
            &[
                "Variable `x` is not defined",
                "Expected expression of type `bool`, found type `u32`",
                "Expected expression of type `u32`, found type `bool`",
            ],
        );
    }

    #[test]
    fn function_with_broken_body_can_still_be_folded() {
        assert_errors(
            "fn add(element: u32, acc: u32) -> u32 { x }
            fn main() {
                let array: [u32; 3] = [1, 2, 3];
                let sum: u32 = array_fold::<add, 3>(array, 0);
            }",
            &["Variable `x` is not defined"],
        );
    }

    #[test]
    fn function_with_broken_body_can_still_be_imported() {
        assert_errors(
            "mod m { pub fn f() -> u32 { x } }
            use crate::m::f;
            fn main() { let y: u32 = f(); }",
            &["Variable `x` is not defined"],
        );
    }

    #[test]
    fn broken_function_in_module_does_not_stop_the_next_item() {
        assert_errors(
            "mod m { fn f() -> u32 { x } }
            fn g() -> u32 { y }
            fn main() {}",
            &["Variable `x` is not defined", "Variable `y` is not defined"],
        );
    }

    #[test]
    fn broken_main_does_not_stop_the_next_item() {
        assert_errors(
            "fn main() { let a: u32 = x; }
            fn g() -> u32 { y }",
            &["Variable `x` is not defined", "Variable `y` is not defined"],
        );
    }

    #[test]
    fn broken_main_in_module_does_not_stop_the_next_item() {
        assert_errors(
            "mod entry { fn main() { let x: u32 = missing; } }
            fn later() -> u32 { later_missing }",
            &[
                "Variable `missing` is not defined",
                "Variable `later_missing` is not defined",
            ],
        );
    }

    #[test]
    fn broken_main_in_nested_module_does_not_stop_the_next_item() {
        assert_errors(
            "mod outer {
                mod inner { fn main() { let x: u32 = missing; } }
                fn sibling() -> u32 { sibling_missing }
            }
            fn later() -> u32 { later_missing }",
            &[
                "Variable `missing` is not defined",
                "Variable `sibling_missing` is not defined",
                "Variable `later_missing` is not defined",
            ],
        );
    }
}

#[cfg(test)]
mod scope_balance_tests {
    use super::*;

    #[test]
    fn scopes_are_restored_after_failed_analysis() {
        let mut scope = Scope::new(Box::new(ElementsJetHinter));

        scope.enter_block();
        let result: Result<(), ()> = scope.in_block(|_| Err(()));
        assert!(result.is_err());
        assert_eq!(scope.variables.len(), 1);
        scope.exit_block();

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
        assert!(scope.module_path.is_empty());
    }
}

#[cfg(test)]
mod scope_resolution_tests {
    use super::{ElementsJetHinter, Program};
    use crate::driver::tests::setup_graph;

    pub(super) fn analyze_multifile(files: Vec<(&str, &str)>) -> Result<(), String> {
        let (graph, _ids, _dir, mut diagnostics) = setup_graph(files);

        let Some(driver_program) = graph.linearize_and_assemble(&mut diagnostics) else {
            return Err(diagnostics.render_to_string());
        };

        match Program::analyze(
            &driver_program,
            Box::new(ElementsJetHinter),
            &mut diagnostics,
        ) {
            Some(_) => Ok(()),
            None => Err(diagnostics
                .diagnostics()
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n")),
        }
    }

    #[test]
    fn private_type_alias_from_dependency_does_not_leak() {
        let result = analyze_multifile(vec![
            (
                "main.simf",
                "use lib::A::helper; fn main() { helper(); let x: Secret = 0; }",
            ),
            ("libs/lib/A.simf", "type Secret = u32; pub fn helper() {}"),
        ]);

        assert!(
            result.is_err(),
            "private alias from another file leaked into root scope: {result:?}"
        );
    }

    #[test]
    fn same_alias_name_in_different_modules_does_not_conflict_if_only_one_is_imported() {
        let result = analyze_multifile(vec![
            (
                "main.simf",
                "use lib::A::Word; use lib::B::id; fn main() { let x: Word = 0; assert!(jet::is_zero_32(id(x))); }",
            ),
            ("libs/lib/A.simf", "pub type Word = u32;"),
            ("libs/lib/B.simf", "pub type Word = u16; pub fn id(x: u32) -> u32 { x }"),
        ]);

        assert!(
            result.is_ok(),
            "unimported alias from another module should not collide: {result:?}"
        );
    }

    #[test]
    fn main_must_be_defined_once_per_project() {
        let result = analyze_multifile(vec![
            ("main.simf", "use lib::A::helper; fn main() { helper(); }"),
            ("libs/lib/A.simf", "fn main() {} pub fn helper() {}"),
        ]);

        assert!(
            result.is_err(),
            "Main function must be inside an entry file: {result:?}"
        );
    }

    #[test]
    fn test_local_definitions_visibility() {
        // main.simf defines a private function and a public function.
        // Expected: Both should be usable locally in main.
        let result = analyze_multifile(vec![(
            "main.simf",
            "fn private_fn() {} pub fn public_fn() {} fn main() { private_fn(); public_fn(); }",
        )]);

        assert!(
            result.is_ok(),
            "Local definitions should be visible: {result:?}"
        );
    }

    #[test]
    fn test_pub_use_propagation() {
        // Scenario: Re-exporting.
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("libs/lib/B.simf", "pub use crate::A::foo;"),
            ("main.simf", "use lib::B::foo; fn main() { foo(); }"),
        ]);

        assert!(
            result.is_ok(),
            "Public re-exports must be visible: {result:?}"
        );
    }

    #[test]
    fn test_private_import_encapsulation_error() {
        // Scenario: A private import cannot be re-exported.
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("libs/lib/B.simf", "use crate::A::foo;"), // <--- Private binding!
            ("main.simf", "use lib::B::foo; fn main() {}"),
        ]);

        let err = result.expect_err("Private imports should not be accessible");
        assert!(err.contains("private") || err.contains("foo"));
    }

    #[test]
    fn test_separated_type_aliases_and_functions() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub type bar = u32; pub fn bar() {}"),
            (
                "main.simf",
                "use lib::A::bar; fn main() { bar(); let x: bar = 0; }",
            ),
        ]);

        assert!(
            result.is_ok(),
            "AST should support separate namespaces for types and functions: {result:?}"
        );
    }

    #[test]
    fn test_public_main_is_forbidden() {
        let result = analyze_multifile(vec![("main.simf", "pub fn main() {}")]);

        let err = result.expect_err("Public main should be rejected");
        assert!(err.contains("Main") && err.contains("public"));
    }

    #[test]
    fn test_aliasing_to_main_is_forbidden() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub type bar = u32;"),
            ("main.simf", "use lib::A::bar as main; fn main() {}"),
        ]);

        let err = result.expect_err("Aliasing to main should be rejected");
        assert!(err.contains("Main") && err.contains("alias"));
    }

    #[test]
    fn test_renaming_with_use() {
        // Expected: "bar" is usable, "foo" is not.
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            (
                "main.simf",
                "use lib::A::foo as bar; fn main() { bar(); foo(); }",
            ),
        ]);

        let err = result.expect_err("Using the original unaliased name 'foo' should fail");
        assert!(err.contains("foo") && (err.contains("not defined") || err.contains("unresolved")));
    }

    #[test]
    fn test_multiple_aliases_in_list() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn foo() {} pub fn baz() {}"),
            (
                "main.simf",
                "use lib::A::{foo as bar, baz as qux}; fn main() { bar(); qux(); }",
            ),
        ]);

        assert!(
            result.is_ok(),
            "List aliases should be resolvable: {result:?}"
        );
    }

    #[test]
    fn test_alias_private_item_fails() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "fn secret() {}"),
            ("main.simf", "use lib::A::secret as my_secret; fn main() {}"),
        ]);

        let err = result.expect_err("Aliasing a private item should fail");
        assert!(err.contains("secret") && err.contains("private"));
    }

    #[test]
    fn test_deep_reexport_with_aliases() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn original() {}"),
            ("libs/lib/B.simf", "pub use crate::A::original as middle;"),
            (
                "main.simf",
                "use lib::B::middle as final_name; fn main() { final_name(); }",
            ),
        ]);

        assert!(
            result.is_ok(),
            "Deep alias re-exports should work: {result:?}"
        );
    }

    #[test]
    fn test_deep_reexport_private_link_fails() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn target() {}"),
            ("libs/lib/B.simf", "use crate::A::target as hidden_alias;"),
            ("main.simf", "use lib::B::hidden_alias; fn main() {}"),
        ]);

        let err = result.expect_err("Private intermediate aliases should block resolution");
        assert!(err.contains("hidden_alias") && err.contains("private"));
    }

    #[test]
    fn test_plain_import_and_alias_to_same_name_is_rejected() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("libs/lib/B.simf", "pub fn foo() {}"),
            (
                "main.simf",
                "use lib::A::foo; use lib::B::foo as foo; fn main() {}",
            ),
        ]);

        let err = result.expect_err("Duplicate names in scope should fail");
        assert!(err.contains("foo") && err.contains("multiple times"));
    }

    #[test]
    fn test_alias_cannot_reuse_local_definition_name() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn bar() {}"),
            (
                "main.simf",
                "pub fn foo() {} use lib::A::bar as foo; fn main() {}",
            ),
        ]);

        let err = result.expect_err("Alias reusing a local name should fail");
        assert!(err.contains("foo") && err.contains("multiple times"));
    }

    #[test]
    #[ignore = "Pending better error handler:private item errors currently mask duplicate imports"]
    fn test_private_alias_error_does_not_mask_duplicate_function_import() {
        // Scenario: Loading a private item fails, but we must STILL catch if a
        // secondary import tries to bind to the same name.
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn foo() {}"),
            ("libs/lib/B.simf", "pub fn foo() {} type foo = u32;"),
            (
                "main.simf",
                "use lib::A::foo; use lib::B::foo; fn main() {}",
            ),
        ]);

        let err = result.expect_err("Duplicate function import should fail");

        // It shouldn't just complain about the private type `foo`; it must also
        // complain that `foo` was imported twice!
        assert!(err.contains("foo") && err.contains("multiple times"));
    }

    #[test]
    fn test_failed_alias_import_does_not_poison_following_imports() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn nope() {}"),
            ("libs/lib/B.simf", "pub fn bar() {}"),
            (
                "main.simf",
                "use lib::A::missing as foo; use lib::B::bar as foo; fn main() {}",
            ),
        ]);

        let err = result.expect_err("Build should fail on the unresolved import");

        // It should complain about `missing`, but NOT about `foo` being duplicated,
        // because the first import failed and never actually reserved the name `foo`.
        assert!(err.contains("missing") || err.contains("not found"));
        assert!(!err.contains("multiple times"));
    }

    #[test]
    fn test_local_function_cannot_reuse_alias_name() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub fn bar() {}"),
            (
                "main.simf",
                "use lib::A::bar as foo; pub fn foo() {} fn main() {}",
            ),
        ]);

        let err =
            result.expect_err("Build should fail when a local definition reuses an alias name");
        assert!(err.contains("foo") && err.contains("multiple times"));
    }

    #[test]
    fn test_local_type_alias_cannot_reuse_alias_name() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub type bar = u32;"),
            (
                "main.simf",
                "use lib::A::bar as foo; type foo = u64; fn main() {}",
            ),
        ]);

        let err =
            result.expect_err("Build should fail when a local definition reuses an alias name");
        assert!(err.contains("foo") && err.contains("multiple times"));
    }
}

#[cfg(test)]
mod module_tests {
    use crate::ast::scope_resolution_tests::analyze_multifile;

    #[test]
    fn test_public_nested_modules_are_accessible() {
        let result = analyze_multifile(vec![
            (
                "libs/lib/A.simf",
                "pub mod outer { pub mod inner { pub fn target() {} } }",
            ),
            (
                "main.simf",
                "use lib::A::outer::inner::target; fn main() {}",
            ),
        ]);

        assert!(
            result.is_ok(),
            "Deeply nested public modules should be accessible: {result:?}"
        );
    }

    #[test]
    fn test_private_inner_module_blocks_external_access() {
        let result = analyze_multifile(vec![
            // `outer` is public, but `inner` is private
            // Even though `target` is public, the private wall at `inner` blocks it.
            (
                "libs/lib/A.simf",
                "pub mod outer { mod inner { pub fn target() {} } }",
            ),
            (
                "main.simf",
                "use lib::A::outer::inner::target; fn main() {}",
            ),
        ]);

        let err = result.expect_err("Private inner module must block access");
        assert!(err.contains("inner") && err.contains("private"));
    }

    #[test]
    #[ignore = "Not implemented now"]
    fn test_importing_a_whole_module_allows_path_traversal() {
        // Scenario: Instead of importing the function, the user imports the module itself,
        // and then uses the module name as a prefix.
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub mod math { pub fn add() {} }"),
            ("main.simf", "use lib::A::math; fn main() { math::add(); }"),
        ]);

        assert!(
            result.is_ok(),
            "Importing a module should bring its namespace into scope: {result:?}"
        );
    }

    #[test]
    fn test_duplicate_module_blocks_are_rejected() {
        let result = analyze_multifile(vec![(
            "main.simf",
            "mod inner {} mod inner {} fn main() {}",
        )]);

        let err = result.expect_err("Duplicate mod blocks must fail");
        assert!(err.contains("inner") && err.contains("multiple times"));
    }

    #[test]
    fn test_sibling_modules_can_access_each_others_public_items() {
        // In Rust, sibling modules share the same parent, so they are allowed to see
        // each other (even if they are private to the outside world).
        let result = analyze_multifile(vec![(
            "main.simf",
            "
                mod brother { pub fn toy() {} }
                mod sister { use crate::brother::toy; }
                fn main() {}
            ",
        )]);

        assert!(
            result.is_ok(),
            "Sibling modules should be able to import from each other: {result:?}"
        );
    }

    #[test]
    fn test_inline_module_can_import_global_item() {
        // Scenario: A nested module needs to access a function defined at the very top of the file.
        // This proves `crate::` correctly points to the un-wrapped MAIN_MODULE root.
        let result = analyze_multifile(vec![(
            "main.simf",
            "
                pub fn global_func() {}
                mod inner {
                    use crate::global_func;
                    pub fn call_it() { global_func(); }
                }
                fn main() {}
            ",
        )]);

        assert!(
            result.is_ok(),
            "Nested modules must be able to import global items: {result:?}"
        );
    }

    #[test]
    fn test_deeply_nested_inline_modules() {
        // Scenario: Traversing multiple inline module boundaries.
        let result = analyze_multifile(vec![(
            "main.simf",
            "
                mod level1 {
                    pub mod level2 {
                        pub fn treasure() {}
                    }
                }
                mod explorer {
                    use crate::level1::level2::treasure;
                }
                fn main() {}
            ",
        )]);

        assert!(
            result.is_ok(),
            "Deeply nested inline modules must resolve correctly: {result:?}"
        );
    }

    #[test]
    fn test_inline_module_privacy_is_enforced_between_siblings() {
        // Scenario: Sibling modules can see each other, but they CANNOT see each other's PRIVATE items.
        let result = analyze_multifile(vec![(
            "main.simf",
            "
                mod brother {
                    fn secret_toy() {} // Missing 'pub'
                }
                mod sister {
                    use crate::brother::secret_toy;
                }
                fn main() {}
            ",
        )]);

        let err = result.expect_err("Private inline items must remain hidden from siblings");
        assert!(err.contains("secret_toy") && err.contains("private"));
    }

    #[test]
    fn test_main_scope_cannot_access_private_inline_items() {
        // Scenario: The root of the file tries to import a private item from its own child module.
        let result = analyze_multifile(vec![(
            "main.simf",
            "
                mod child {
                    fn hidden() {}
                }
                use crate::child::hidden;
                fn main() {}
            ",
        )]);

        let err = result.expect_err("The root file scope must respect inline module privacy");
        assert!(err.contains("hidden") && err.contains("private"));
    }

    #[test]
    fn test_inline_module_alias_import() {
        // Scenario: Importing an item from a sibling inline module and renaming it locally.
        let result = analyze_multifile(vec![(
            "main.simf",
            "
                mod supplier {
                    pub fn raw_material() {}
                }
                mod factory {
                    use crate::supplier::raw_material as finished_product;
                    pub fn produce() { finished_product(); }
                }
                fn main() {}
            ",
        )]);

        assert!(
            result.is_ok(),
            "Inline imports must support aliasing: {result:?}"
        );
    }
}

#[cfg(test)]
mod enum_tests {
    use crate::ast::ElementsJetHinter;
    use crate::{TemplateAst, UnstableFeatures};

    fn analyze(src: &str) -> Result<(), String> {
        TemplateAst::new_with_unstable(
            src,
            &UnstableFeatures::all(),
            Box::new(ElementsJetHinter::new()),
        )
        .map(|_| ())
        .map_err(|e| e.to_string())
    }

    #[test]
    fn enum_declaration_registers_type_alias() {
        let result = analyze(
            "enum Color { Red, Green }
             fn main() { let _x: Color = witness::C; }",
        );
        assert!(
            result.is_ok(),
            "enum name should resolve as a type: {result:?}"
        );
    }

    #[test]
    fn enum_duplicate_variant_name_is_error() {
        let result = analyze("enum Color { Red, Red }\nfn main() {}");
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("duplicate variant name"));
    }

    #[test]
    fn enum_variant_named_after_builtin_pattern_is_ok() {
        // The written `Enum::Variant` form keeps `Action::None` distinct
        // from the built-in option literal, so variant names are
        // unrestricted.
        let result = analyze(
            "enum Action { None, Some, Other, }
             fn main() {
                 match witness::W {
                     Action::None => {},
                     Action::Some => {},
                     Action::Other => {},
                 }
             }",
        );
        assert!(
            result.is_ok(),
            "builtin-named variants should work: {result:?}"
        );
    }

    #[test]
    fn enum_empty_is_error() {
        let result = analyze("enum Color { }\nfn main() {}");
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("at least one variant"));
    }

    #[test]
    fn enum_duplicate_name_is_error() {
        let result = analyze(
            "enum Color { Red, Green }
             enum Color { Blue, Cyan }
             fn main() {}",
        );
        assert!(result.is_err(), "redefined enum name should error");
    }

    #[test]
    fn enum_declaration_inside_module_errors() {
        // FIXME: Enums may only be declared at the top level of a file.
        let result = analyze(
            "mod m {
                 pub enum Choice { X, Y, }
             }
             fn main() {}",
        );
        let err = result.expect_err("enum inside `mod` must be rejected");
        assert!(
            err.contains("top level"),
            "error should say enums are top-level only: {err}"
        );
    }

    #[test]
    fn enum_declaration_in_dependency_errors() {
        use crate::ast::scope_resolution_tests::analyze_multifile;

        // FIXME: An enum's declared name is its identity in the ABI, so enums may only be declared in the program's own files.
        let result = analyze_multifile(vec![
            (
                "main.simf",
                "use lib::A::helper;
                 fn main() { helper(); }",
            ),
            (
                "libs/lib/A.simf",
                "pub enum Status { On, Off, } pub fn helper() {}",
            ),
        ]);
        let err = result.expect_err("enums in dependency files must be rejected");
        assert!(
            err.contains("dependency"),
            "error should say enums cannot live in dependency files: {err}"
        );
    }

    #[test]
    fn enum_payload_match_binds_payload() {
        let result = analyze(
            "enum Action { Refresh(u32, bool), Cold, }
             fn main() {
                 match witness::W {
                     Action::Refresh(n: u32, b: bool) => {
                         assert!(jet::is_zero_32(n));
                         assert!(b);
                     },
                     Action::Cold => {},
                 }
             }",
        );
        assert!(
            result.is_ok(),
            "payload bindings should analyze: {result:?}"
        );
    }

    #[test]
    fn enum_payload_binding_type_mismatch_is_error() {
        let result = analyze(
            "enum Action { Refresh(u32), Cold, }
             fn main() {
                 match witness::W {
                     Action::Refresh(n: u16) => { assert!(jet::is_zero_16(n)); },
                     Action::Cold => {},
                 }
             }",
        );
        assert!(
            result.is_err(),
            "binding type must equal the declared payload type"
        );
    }

    #[test]
    fn enum_payload_binding_arity_mismatch_is_error() {
        let result = analyze(
            "enum Action { Refresh(u32, bool), Cold, }
             fn main() {
                 match witness::W {
                     Action::Refresh(n: u32) => { assert!(jet::is_zero_32(n)); },
                     Action::Cold => {},
                 }
             }",
        );
        assert!(result.is_err());
        assert!(
            result.unwrap_err().contains("payload value"),
            "error should describe the arity mismatch"
        );
    }

    #[test]
    fn enum_single_variant_matches() {
        // A single-variant enum is a named unit type; its match has one arm.
        let result = analyze(
            "enum Marker { Only }
             fn main() {
                 match witness::M {
                     Marker::Only => {},
                 }
             }",
        );
        assert!(
            result.is_ok(),
            "single-variant enum should work: {result:?}"
        );
    }

    #[test]
    fn enum_match_undefined_enum_is_error() {
        let result = analyze(
            "fn main() {
                 match witness::P {
                     Unknown::A => {},
                     Unknown::B => {},
                 }
             }",
        );
        assert!(result.is_err(), "undefined enum should error");
    }

    #[test]
    fn enum_match_mixed_enum_names_is_error() {
        let result = analyze(
            "enum A { X, Y }
             enum B { P, Q }
             fn main() {
                 match witness::W {
                     A::X => {},
                     B::Q => {},
                 }
             }",
        );
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("same enum"));
    }

    #[test]
    fn enum_match_unknown_variant_is_error() {
        let result = analyze(
            "enum A { X, Y }
             fn main() {
                 match witness::W {
                     A::X => {},
                     A::Z => {},
                 }
             }",
        );
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("not defined"));
    }

    #[test]
    fn enum_match_duplicate_arm_is_error() {
        let result = analyze(
            "enum A { X, Y }
             fn main() {
                 match witness::W {
                     A::X => {},
                     A::X => {},
                     A::Y => {},
                 }
             }",
        );
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("duplicate arm"));
    }

    #[test]
    fn enum_match_missing_arm_is_error() {
        let result = analyze(
            "enum A { X, Y, Z }
             fn main() {
                 match witness::W {
                     A::X => {},
                     A::Y => {},
                 }
             }",
        );
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("must cover all 3 variants"));
    }

    #[test]
    fn enum_match_rejects_scrutinee_of_different_enum() {
        let result = analyze(
            "enum A { X, Y, }
             enum B { P, Q, }
             fn main() {
                 let v: A = witness::V;
                 match v {
                     B::P => {},
                     B::Q => {},
                 }
             }",
        );
        assert!(
            result.is_err(),
            "matching a value of enum A against B's variants must be a type error"
        );
    }

    #[test]
    fn enum_match_rejects_plain_u8_scrutinee() {
        let result = analyze(
            "enum Action { A, B, }
             fn main() {
                 let v: u8 = witness::V;
                 match v {
                     Action::A => {},
                     Action::B => {},
                 }
             }",
        );
        assert!(
            result.is_err(),
            "matching a u8 against enum variants must be a type error"
        );
    }

    #[test]
    fn enum_match_rejects_same_shaped_enum() {
        // Identity is the declaration site: two enums with the same variants
        // are distinct types, so their values are not interchangeable.
        let result = analyze(
            "enum AChoice { X, Y, }
             enum BChoice { X, Y, }
             fn main() {
                 let v: AChoice = witness::V;
                 match v {
                     BChoice::X => {},
                     BChoice::Y => {},
                 }
             }",
        );
        assert!(
            result.is_err(),
            "structurally identical enums must not be interchangeable"
        );
    }

    #[test]
    fn enum_match_on_non_enum_alias_is_error() {
        let result = analyze(
            "type Foo = u32;
             fn main() {
                 match witness::W {
                     Foo::A => {},
                     Foo::B => {},
                 }
             }",
        );
        assert!(result.is_err());
        assert!(
            result.unwrap_err().contains("not an enum"),
            "a defined non-enum alias should not report an undefined alias"
        );
    }

    #[test]
    fn enum_cast_to_same_shaped_enum_is_rejected() {
        // Casts prove structural equality, but enums are nominal: a cast
        // between same-shaped enums would map variants by ordinal position
        // (Source::Allow -> Target::Deny), silently reversing semantics.
        let result = analyze(
            "enum Source { Allow, Deny, }
             enum Target { Deny, Allow, }
             fn main() {
                 let s: Source = Source::Allow;
                 let _t: Target = <Source>::into(s);
             }",
        );
        assert!(
            result.is_err(),
            "same-shaped enums must not cast into each other"
        );
    }

    #[test]
    fn enum_cast_to_structural_sum_is_rejected() {
        let result = analyze(
            "enum Source { Allow, Deny, }
             fn main() {
                 let s: Source = Source::Allow;
                 let _e: Either<(), ()> = <Source>::into(s);
             }",
        );
        assert!(
            result.is_err(),
            "an enum must not cast to its structural sum"
        );

        let result = analyze(
            "enum Source { Allow, Deny, }
             fn main() {
                 let e: Either<(), ()> = Left(());
                 let _s: Source = <Either<(), ()>>::into(e);
             }",
        );
        assert!(result.is_err(), "a structural sum must not cast to an enum");
    }

    #[test]
    fn enum_cast_reshaping_enum_free_siblings_is_ok() {
        // Enum-free structure may reshape around an enum that stays put
        // at its position.
        let result = analyze(
            "enum E { A, B, }
             fn main() {
                 let x: (E, (u16, u16)) = (E::A, (1, 2));
                 let _y: (E, u32) = <(E, (u16, u16))>::into(x);
             }",
        );
        assert!(
            result.is_ok(),
            "reshaping enum-free siblings must stay castable: {result:?}"
        );
    }

    #[test]
    fn enum_cast_reshaping_enum_free_siblings_is_ok_2() {
        // This one has an enum with a left sibling which is much bigger (as a HL type DAG) in the
        // source type than the target.
        let result = analyze(
            "enum E { A, B, }
             fn main() {
                 let x: ((Either<(), u8>, Either<(), u8>, Either<(), u8>), E)
                     = ((Left(()), Left(()), Left(())), E::A);
                 let _y: ((Option<u8>, Option<u8>, Option<u8>), E)
                     = <((Either<(), u8>, Either<(), u8>, Either<(), u8>), E)>::into(x);
             }",
        );
        assert!(
            result.is_ok(),
            "reshaping enum-free siblings must stay castable: {result:?}"
        );

        // Same thing, but we try to swap out the enums. This should fail.
        let result = analyze(
            "enum E { A, B, }
             enum F { C, D, }
             fn main() {
                 let x: ((Either<(), u8>, Either<(), u8>, Either<(), u8>), E)
                     = ((Left(()), Left(()), Left(())), E::A);
                 let _y: ((Option<u8>, Option<u8>, Option<u8>), F)
                     = <((Either<(), u8>, Either<(), u8>, Either<(), u8>), E)>::into(x);
             }",
        );
        assert!(
            result.is_err(),
            "reshaping enum-free siblings must stay non-castable: {result:?}"
        );
    }

    #[test]
    fn enum_cast_to_itself_is_ok() {
        let result = analyze(
            "enum Source { Allow, Deny, }
             fn main() {
                 let s: Source = Source::Allow;
                 let _t: Source = <Source>::into(s);
             }",
        );
        assert!(
            result.is_ok(),
            "nominally identical cast should stay allowed: {result:?}"
        );
    }

    #[test]
    fn enum_cast_option_either() {
        let result = analyze(
            "enum E { A, B, }
             fn main() {
                 let x: Option<E> = None;
                 let _y: Either<(), E> = <Option<E>>::into(x);
             }",
        );
        result.expect_err("this should work");
    }

    #[test]
    fn enum_cast_array_tuple() {
        let result = analyze(
            "enum E { A, B, }
             fn main() {
                 let x: [E; 2] = [E::A, E::B];
                 let _y: (E, E) = <[E; 2]>::into(x);
             }",
        );
        result.expect_err("this should work");
    }

    #[test]
    fn enum_cast_list1_option() {
        let result = analyze(
            "enum E { A, B, }
             fn main() {
                 let x: List<E, 2> = list![];
                 let _y: Option<E> = <List<E, 2>>::into(x);
             }",
        );
        result.expect_err("this should work");
    }

    #[test]
    fn enum_cast_list2_option() {
        let result = analyze(
            "enum E { A, B, }
             fn main() {
                 let x: List<E, 4> = list![];
                 let _y: (Option<(E, E)>, Option<E>) = <List<E, 4>>::into(x);
             }",
        );
        result.expect_err("this should work");
    }

    #[test]
    fn enum_named_after_builtin_type_is_rejected() {
        // `enum Signature` would shadow the built-in alias: constructions
        // would name the enum while type annotations resolve to the
        // builtin, and the ABI would report the bare name ambiguously.
        for name in crate::str::ALIAS_RESERVED {
            let result = analyze(&format!("enum {name} {{ A, B, }}\nfn main() {{}}"));
            assert!(result.is_err(), "enum named `{name}` must be rejected");
        }
    }

    #[test]
    fn enum_alias_named_after_pattern_is_matchable() {
        // `type Left = Action` shadows a built-in pattern name; the arm
        // parser distinguishes `Left::A` (enum path) from `Left(x)`
        // (built-in pattern) by the `::` that follows.
        let result = analyze(
            "enum Action { A, B, }
             type Left = Action;
             fn main() {
                 let v: Left = Action::A;
                 match v {
                     Left::A => {},
                     Left::B => {},
                 }
             }",
        );
        assert!(
            result.is_ok(),
            "an enum alias shadowing a pattern name must be matchable: {result:?}"
        );
    }

    #[test]
    fn enum_alias_named_none_is_constructable() {
        // The nullary built-in `None` parses without parentheses, so the
        // expression parser must yield to enum construction when `::`
        // follows, like the arm parser does.
        let result = analyze(
            "enum Action { A, B, }
             type None = Action;
             fn main() {
                 let _x: None = None::A;
             }",
        );
        assert!(
            result.is_ok(),
            "`None::A` must parse as enum construction: {result:?}"
        );
    }

    #[test]
    fn alias_named_after_pattern_stays_valid_without_enums() {
        // Stable programs may alias pattern names; the enums feature must
        // not retroactively reject them.
        let result = TemplateAst::new_with_unstable(
            "type Left = u32;\nfn main() { let _x: Left = 1; }",
            &UnstableFeatures::none(),
            Box::new(ElementsJetHinter::new()),
        );
        assert!(
            result.is_ok(),
            "stable alias names must stay valid without -Z enums"
        );
    }

    #[test]
    fn enum_construction_follows_lexical_scope_in_source() {
        // Inside a module the root's `E` is not in scope: only the local
        // import name may construct, exactly as matches require. The
        // declared-name fallback applies only to witness/argument files.
        let result = analyze(
            "pub enum E { A, B, }
             mod m {
                 use crate::E as Choice;
                 pub fn make() -> Choice {
                     E::A
                 }
             }
             use crate::m::make;
             fn main() {
                 let _x: E = make();
             }",
        );
        assert!(
            result.is_err(),
            "an out-of-scope declared name must not construct"
        );

        let result = analyze(
            "pub enum E { A, B, }
             mod m {
                 use crate::E as Choice;
                 pub fn make() -> Choice {
                     Choice::A
                 }
             }
             use crate::m::make;
             fn main() {
                 let _x: E = make();
             }",
        );
        assert!(
            result.is_ok(),
            "the imported alias must construct: {result:?}"
        );
    }

    #[test]
    fn enum_requires_unstable_feature() {
        let result = TemplateAst::new_with_unstable(
            "enum Color { Red, Green }\nfn main() {}",
            &UnstableFeatures::none(),
            Box::new(ElementsJetHinter::new()),
        );
        assert!(result.is_err(), "enum syntax is gated behind -Z enums");
    }
}

#[cfg(feature = "fmt")]
#[cfg(test)]
mod literal_tests {
    use crate::parse::ParseFromStr;
    use crate::value::{UIntValue, Value};

    use super::*;

    #[test]
    fn analyzed_numeric_literals_accept_digit_separators() {
        let cases = [
            ("1_337", UIntType::U16, Value::from(UIntValue::U16(1_337))),
            (
                "0b1010_0101",
                UIntType::U8,
                Value::from(UIntValue::U8(0b1010_0101)),
            ),
            (
                "0xDE_AD_BE_EF",
                UIntType::U32,
                Value::from(UIntValue::U32(0xdead_beef)),
            ),
        ];

        for (source, integer_type, expected) in cases {
            let parsed = parse::Expression::parse_from_str(source).expect("literal parses");
            let analyzed =
                Expression::analyze_const(&parsed, &integer_type.into()).expect("literal analyzes");

            let ExpressionInner::Single(single) = analyzed.inner() else {
                panic!("expected a single expression")
            };
            let SingleExpressionInner::Constant(value) = single.inner() else {
                panic!("expected a constant expression")
            };

            assert_eq!(value, &expected, "unexpected value for {source:?}");
            assert_eq!(single.span().to_slice(source), Some(source));
        }
    }
}

#[cfg(test)]
mod transactional_use_tests {
    use super::*;
    use crate::parse::ParseFromStr;

    fn resolve(scope: &mut Scope, source: &str) -> Result<(), Error> {
        let program = parse::Program::parse_from_str(source).unwrap();
        let parse::Item::Use(decl) = &program.items()[0] else {
            panic!("expected use declaration");
        };
        scope.resolve_use(decl)
    }

    fn scope() -> Scope {
        let mut scope = Scope::default();
        scope
            .enter_module(ModuleName::from_str_unchecked("source"), Visibility::Public)
            .unwrap();
        scope.current_module_mut().aliases.insert(
            AliasName::from_str_unchecked("Good"),
            (ResolvedType::u32(), Visibility::Public),
        );
        scope.current_module_mut().aliases.insert(
            AliasName::from_str_unchecked("Secret"),
            (ResolvedType::u16(), Visibility::Private),
        );
        scope.exit_module();
        scope
    }

    #[test]
    fn failed_imports_preserve_the_complete_module_tree() {
        for (source, expected) in [
            (
                "use crate::source::{Good, Missing};",
                Error::UnresolvedItem {
                    name: "Missing".into(),
                },
            ),
            (
                "use crate::source::{Good, Secret};",
                Error::PrivateItem {
                    name: "Secret".into(),
                },
            ),
            (
                "use crate::source::{Good as Same, Good as Same};",
                Error::RedefinedItem {
                    name: "Same".into(),
                },
            ),
            (
                "use crate::source::{Good, Good as main};",
                Error::MainCannotBeAlias,
            ),
            (
                "use crate::source::{Good, Good as Taken};",
                Error::RedefinedItem {
                    name: "Taken".into(),
                },
            ),
        ] {
            for nested in [false, true] {
                let mut scope = scope();
                if nested {
                    scope
                        .enter_module(
                            ModuleName::from_str_unchecked("consumer"),
                            Visibility::Private,
                        )
                        .unwrap();
                }
                scope.current_module_mut().aliases.insert(
                    AliasName::from_str_unchecked("Taken"),
                    (ResolvedType::u8(), Visibility::Private),
                );
                let before = scope.root.clone();
                let path = scope.module_path.clone();
                let error = resolve(&mut scope, source).expect_err(source);
                assert_eq!(error.to_string(), expected.to_string(), "{source}");
                assert_eq!(scope.root, before, "failed import mutated scope: {source}");
                assert_eq!(scope.module_path, path, "{source}");
                resolve(&mut scope, "use crate::source::Good;").unwrap();
            }
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
        resolve(&mut scope, "pub use crate::source::Good as Renamed;").unwrap();
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
