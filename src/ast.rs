use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::convert::Infallible;
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
use crate::str::{AliasName, FunctionName, Identifier, ModuleName, SymbolName, WitnessName};
use crate::types::{
    AliasedType, EnumInfo, EnumVariantInfo, ResolvedType, StructuralType, TypeConstructible,
    TypeDeconstructible, TypeInner, UIntType,
};
use crate::value::{UIntValue, Value};
use crate::witness::{Parameters, WitnessTypes};
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
    Error,
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
    /// A placeholder for a statement that failed to parse.
    Error,
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
    /// Match expression over an enum's variants.
    EnumMatch(EnumMatch),
    /// Construction of an enum variant.
    ///
    /// The enum's definition lives in the type of the expression.
    EnumConstruction(EnumConstruction),
    /// Placeholder for subexpression that failed to parse.
    ///
    /// Emitted by the parser during error recovery.
    Error,
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

impl CallName {
    /// Does this call name a function whose signature is unknowable?
    fn is_never(&self) -> bool {
        match self {
            Self::Custom(f) | Self::Fold(f, _) | Self::ArrayFold(f, _) | Self::ForWhile(f, _) => {
                f.is_never()
            }
            _ => false,
        }
    }
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
    body: Arc<Expression>,
    span: Span,
    /// Poison: the definition could not be found, so the signature is a
    /// placeholder rather than the truth.
    is_never: bool,
}

impl CustomFunction {
    /// A function whose signature is unknowable, used when a name is declared
    /// but its definition cannot be found.
    fn error(span: Span) -> Self {
        Self {
            params: Arc::from([]),
            body: Arc::new(Expression::error(ResolvedType::never(), span)),
            span,
            is_never: true,
        }
    }

    /// Is the signature unknowable? Every check against it — arity, argument
    /// types, output type, foldability, loopability — is then absorbed.
    pub fn is_never(&self) -> bool {
        self.is_never
    }

    /// Access the identifiers of the parameters of the function.
    pub fn params(&self) -> &[FunctionParam] {
        &self.params
    }

    /// Access the body of the function.
    pub fn body(&self) -> &Expression {
        &self.body
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

impl_eq_hash!(CustomFunction; params, body);

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
                Statement::Error => Tree::Nullary,
            },
            Self::Assignment(assignment) => Tree::Unary(Self::Expression(assignment.expression())),
            Self::Single(single) => match single.inner() {
                S::Constant(_)
                | S::Witness(_)
                | S::Parameter(_)
                | S::Variable(_)
                | S::Option(None)
                | S::Error => Tree::Nullary,
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
    /// Names a failed `use` was meant to introduce. Kept apart from the maps
    /// above so poison never takes part in a redefinition check, and consulted
    /// only on a miss, so a real definition always wins.
    poisoned_imports: HashSet<SymbolName>,
}

impl ModuleScope {
    fn poison_import(&mut self, name: &SymbolName) {
        self.poisoned_imports.insert(name.shallow_clone());
    }

    /// A name is poisoned only when the `use` bound it in *no* namespace, so the
    /// poison applies to every namespace alike.
    fn is_poisoned_import(&self, name: &str) -> bool {
        self.poisoned_imports
            .contains(&SymbolName::from_str_unchecked(name))
    }
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
    parameters: HashMap<WitnessName, ResolvedType>,
    witnesses: HashMap<WitnessName, ResolvedType>,
    /// Allow enum constructions to name an enum by its declared name even
    /// when that name is not an alias in scope. Enabled only for value
    /// parsing (witness and argument files), which runs without a scope.
    unscoped_enum_names: bool,
    is_main: bool,
    call_tracker: CallTracker,
    jet_hinter: Box<dyn JetHinter>,

    diagnostics: Vec<Diagnostic>,
}

impl Default for Scope {
    fn default() -> Self {
        Self::new(
            // TODO: Should be passed in global configuration
            Box::new(ElementsJetHinter),
            Vec::new(),
        )
    }
}

impl Scope {
    pub fn new(jet_hinter: Box<dyn JetHinter>, diagnostics: Vec<Diagnostic>) -> Self {
        Self {
            module_path: Vec::new(),
            root: ModuleScope::default(),
            variables: Vec::new(),
            parameters: HashMap::new(),
            witnesses: HashMap::new(),
            unscoped_enum_names: false,
            is_main: false,
            call_tracker: CallTracker::default(),
            jet_hinter,
            diagnostics,
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

    /// Re-enter a module that is already registered, without registering it again.
    ///
    /// Used to keep analyzing the items of a *redefined* module: the collision
    /// was reported, but the items inside are independent of it, and discarding
    /// the whole block would hide every error in it.
    ///
    /// ## Panics
    ///
    /// No module of this name exists in the current scope.
    fn reenter_module(&mut self, name: ModuleName) {
        assert!(
            self.current_module().submodules.contains_key(&name),
            "module must already exist to be re-entered"
        );
        self.module_path.push(name);
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
        if path.first().map(|id| id.as_inner()) != Some(CRATE_STR) {
            return Err(Error::MissingCrateKeyword);
        }

        let use_vis = use_decl.visibility().clone();
        let use_decl_items = match use_decl.items() {
            parse::UseItems::Single(elem) => std::slice::from_ref(elem),
            parse::UseItems::List(elems) => elems.as_slice(),
        };

        let aliases_main = |(_, aliased): &(SymbolName, Option<SymbolName>)| -> bool {
            aliased.as_ref().is_some_and(|a| a.as_inner() == MAIN_STR)
        };

        // The local name each item introduces, in declaration order. `main` is
        // never one: aliasing to it is rejected below.
        let local_names: Vec<SymbolName> = use_decl_items
            .iter()
            .filter(|item| !aliases_main(item))
            .map(|(name, aliased)| aliased.as_ref().unwrap_or(name).clone())
            .collect();

        // Errors from individual items, reported together at the end: one bad
        // item neither aborts the declaration nor hides the ones beside it.
        let mut item_errors: Vec<Error> = Vec::new();

        // Aliasing to `main` is a property of the declaration alone, so it is
        // checked before navigating: a broken path must not hide it.
        item_errors.extend(
            use_decl_items
                .iter()
                .filter(|item| aliases_main(item))
                .map(|_| Error::MainCannotBeAlias),
        );

        // Phase 1: navigate to target and collect items. Immutable borrow, dropped at end of block
        // Vec<(LocalName, ProcessedAlias, ProcessedFunction, ProcessedModule)>
        // where each result is Result<(Key, (Value, Visibility)), Error>
        let collected: Result<Vec<_>, Error> = {
            // TODO: Part, that can be optimized
            // How many segments do the caller's path and the target's path have in common?
            let shared_prefix_len = self
                .module_path
                .iter()
                .zip(&path[1..])
                .take_while(|(curr, nav)| curr.as_inner() == nav.as_inner())
                .count();

            let mut target_scope = Ok(&self.root);

            for (ind, segment) in path[1..].iter().enumerate() {
                let Ok(scope) = target_scope else { break };
                let name = ModuleName::from_str_unchecked(segment.as_inner());

                target_scope = match scope.submodules.get(&name) {
                    None => Err(Error::ModuleNotFound { name }),
                    Some((_, Visibility::Private)) if shared_prefix_len < ind => {
                        Err(Error::ModuleIsPrivate { name })
                    }
                    Some((inner, _)) => Ok(inner),
                };
            }

            target_scope.map(|target_scope| {
                let mut collected = Vec::with_capacity(use_decl_items.len());
                for item in use_decl_items {
                    // Already reported above; the rest are still collected,
                    // because the items of one `use` are independent.
                    if aliases_main(item) {
                        continue;
                    }

                    let (name, aliased) = item;
                    let local_name = aliased.as_ref().unwrap_or(name);

                    let alias_res =
                        Self::try_collect_item(name, local_name, &target_scope.aliases, &use_vis);
                    let func_res =
                        Self::try_collect_item(name, local_name, &target_scope.functions, &use_vis);
                    let mod_res = Self::try_collect_item(
                        name,
                        local_name,
                        &target_scope.submodules,
                        &use_vis,
                    );

                    collected.push((local_name.clone(), alias_res, func_res, mod_res));
                }
                collected
            })
        };

        let span = *use_decl.span();

        // A broken path binds nothing at all, so every name the declaration
        // introduces is poisoned before the one real error is returned.
        let collected = match collected {
            Ok(collected) => collected,
            Err(path_err) => {
                let current = self.current_module_mut();
                for local_name in &local_names {
                    current.poison_import(local_name);
                }
                for err in item_errors {
                    self.report(err.with_span(span));
                }
                return Err(path_err);
            }
        };

        // Phase 2: insert into current scope.
        //
        // The items of one `use` are independent — `b` failing says nothing
        // about `a` — so each is recorded and the loop continues. Only the
        // path-level failures above abort, because they leave nothing to insert.
        {
            let current = self.current_module_mut();
            for (local_name, alias_res, func_res, mod_res) in collected {
                let results = [
                    Self::insert_collected(alias_res, &mut current.aliases),
                    Self::insert_collected(func_res, &mut current.functions),
                    Self::insert_collected(mod_res, &mut current.submodules),
                ];

                if !results.iter().any(Result::is_ok) {
                    current.poison_import(&local_name);
                }

                item_errors.extend(Self::resolve_processing_use_items_error(&results));
            }
        }

        for err in item_errors {
            self.report(err.with_span(span));
        }

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

    /// Inserts a successfully collected item into the current scope's map.
    ///
    /// ## Errors
    ///
    /// * [`Error::RedefinedItem`] An item with the same name is already defined in the target scope.
    /// * Propagates any upstream resolution error passed into the `res` argument.
    fn insert_collected<K, V>(
        res: Result<(K, (V, Visibility)), Error>,
        map: &mut HashMap<K, (V, Visibility)>,
    ) -> Result<(), Error>
    where
        K: Eq + std::hash::Hash + std::fmt::Display,
    {
        res.and_then(|(k, v)| match map.entry(k) {
            Entry::Occupied(entry) => Err(Error::RedefinedItem {
                name: entry.key().to_string(),
            }),
            Entry::Vacant(entry) => {
                entry.insert(v);
                Ok(())
            }
        })
    }

    /// Evaluates the results of attempting to collect an item from multiple namespaces
    /// (aliases, functions, submodules) and resolves the final error state.
    ///
    /// ## Errors
    ///
    /// * Returns *every* specific error (e.g., [`Error::PrivateItem`],
    ///   [`Error::RedefinedItem`]) that occurred.
    /// * Returns a fallback [`Error::UnresolvedItem`] if the item could not be found in any of the checked namespaces.
    fn resolve_processing_use_items_error(results: &[Result<(), Error>]) -> Vec<Error> {
        let errors: Vec<&Error> = results
            .iter()
            .filter_map(|res| res.as_ref().err())
            .collect();

        // A collision or a privacy violation is a real failure of this import
        // in that namespace. The namespaces are independent, so one such
        // failure must not mask another: a private alias `foo` and a duplicate
        // function `foo` are two distinct problems with the same `use`.
        let specific: Vec<Error> = errors
            .iter()
            .filter(|err| !matches!(err, Error::UnresolvedItem { .. }))
            .map(|err| (*err).clone())
            .collect();

        if !specific.is_empty() {
            return specific;
        }

        // Only "not found" remains. If the item did land in some namespace, that
        // is expected noise; otherwise the name exists nowhere, so report it once.
        if results.iter().any(Result::is_ok) {
            Vec::new()
        } else {
            errors
                .first()
                .map(|err| vec![(*err).clone()])
                .unwrap_or_default()
        }
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
        let module = self.current_module();
        if let Some((ty, _)) = module.aliases.get(name) {
            return Ok(ty.clone());
        }
        if module.is_poisoned_import(name.as_inner()) {
            return Ok(ResolvedType::never());
        }
        Err(Error::UndefinedAlias { name: name.clone() })
    }

    /// Resolve a type with aliases, substituting a poison type for every alias
    /// that is not defined and reporting each one.
    ///
    /// Never fails, so a caller can keep analyzing: a type whose aliases are all
    /// broken still yields a type, and a type with two broken aliases reports
    /// both instead of aborting at the first.
    pub fn resolve_or_poison(&mut self, ty: &AliasedType, span: Span) -> ResolvedType {
        let mut undefined = Vec::new();
        let resolved = ty
            .resolve::<_, Infallible>(|name| {
                Ok(self.get_alias(name).unwrap_or_else(|_| {
                    undefined.push(name.clone());
                    ResolvedType::never()
                }))
            })
            .unwrap_or_else(|never| match never {});

        for name in undefined {
            self.report(Error::UndefinedAlias { name }.with_span(span));
        }
        resolved
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
    /// An alias whose body does not resolve is still registered, at a poison
    /// type: the body's error was reported, and a missing registration would
    /// cascade into "undefined alias" at every use of the name.
    ///
    /// ## Errors
    ///
    /// * [`Error::RedefinedAlias`]: The alias name is already defined in the current scope.
    pub fn insert_alias(&mut self, alias: parse::TypeAlias, span: Span) -> Result<(), Error> {
        // The body is independent of the name collision, so resolve it either
        // way for its own diagnostics.
        let resolved = self.resolve_or_poison(alias.ty(), span);

        // A redefinition keeps the existing binding, which is the good one.
        self.check_alias_free(alias.name())?;

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

        let info = EnumInfo::new(Arc::from(name.as_inner()), variants);
        let resolved = ResolvedType::enumeration(info);

        self.current_module_mut()
            .aliases
            .insert(name, (resolved, visibility));

        Ok(())
    }

    /// Register a type name at a poison type.
    ///
    /// Used when a declaration is rejected but its name was still written: the
    /// cause was reported, and leaving the name unbound would cascade into
    /// [`Error::UndefinedAlias`] at every use of the type.
    ///
    /// ## Errors
    ///
    /// * [`Error::RedefinedAlias`]: The name is already defined in the current module.
    fn insert_poison_alias(
        &mut self,
        name: AliasName,
        visibility: Visibility,
    ) -> Result<(), Error> {
        self.check_alias_free(&name)?;

        self.current_module_mut()
            .aliases
            .insert(name, (ResolvedType::never(), visibility));

        Ok(())
    }

    /// Insert a parameter into the global map.
    ///
    /// ## Errors
    ///
    /// * [`Error::ExpressionTypeMismatch`] A parameter of the same name has already been defined as a different type.
    pub fn insert_parameter(&mut self, name: WitnessName, ty: ResolvedType) -> Result<(), Error> {
        match self.parameters.entry(name.clone()) {
            // Compatible, so the poisoned slots take this use's concrete types.
            // Without refining, the first poisoned use would absorb every later
            // one and a real conflict between two of them would never surface.
            Entry::Occupied(mut entry) if entry.get().compatible(&ty) => {
                let refined = entry.get().refine(&ty);
                entry.insert(refined);
                Ok(())
            }
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
    pub fn insert_witness(&mut self, name: WitnessName, ty: ResolvedType) -> Result<(), Error> {
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
        let module = self.current_module();
        if let Some((func, _)) = module.functions.get(name) {
            return Ok(func.clone());
        }
        if module.is_poisoned_import(name.as_inner()) {
            return Ok(CustomFunction::error(Span::DUMMY));
        }
        Err(Error::FunctionUndefined { name: name.clone() })
    }

    /// Track a call expression with its span.
    pub fn track_call<S: AsRef<Span>>(&mut self, span: &S, name: TrackedCallName) {
        self.call_tracker.track_call(*span.as_ref(), name);
    }

    fn report(&mut self, diag: Diagnostic) {
        self.diagnostics.push(diag);
    }

    fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }
}

/// RAII guard that balances a function/block scope.
///
/// Multi-error analysis keeps going after an error, so a body can fail
/// mid-analysis. Pairing enter/exit by hand around a `?` leaks the scope on the
/// error path, and the next item's balance assertion then panics. This guard
/// runs the exit on *every* path — normal return, early `?`, or unwind — so the
/// scope is always balanced. Entering a scope is only possible through
/// [`Scope::block`] / [`Scope::main_scope`], which always arm the matching exit.
struct ScopeGuard<'a> {
    scope: &'a mut Scope,
    exit: fn(&mut Scope),
}

impl Drop for ScopeGuard<'_> {
    fn drop(&mut self) {
        (self.exit)(self.scope);
    }
}

impl Scope {
    /// Enter a nested block; the guard exits it on drop.
    pub fn block(&mut self) -> ScopeGuard<'_> {
        self.enter_block();

        ScopeGuard {
            scope: self,
            exit: Scope::exit_block,
        }
    }

    /// Enter the main function's scope; the guard exits it on drop.
    ///
    /// ## Panics
    /// - Already inside the main function.
    /// - Already inside a function body.
    pub fn main_scope(&mut self) -> ScopeGuard<'_> {
        self.enter_main();
        ScopeGuard {
            scope: self,
            exit: Scope::exit_main,
        }
    }

    /// Enter a new block inside the current function.
    fn enter_block(&mut self) {
        self.variables.push(HashMap::new());
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
        self.enter_block();
        self.is_main = true;
    }

    /// Exit the current block inside the curreent function.
    ///
    /// ## Panics
    ///
    /// - No acive block to exit.
    fn exit_block(&mut self) {
        self.variables.pop().expect("No active block to exit");
    }

    /// Pop the scope of the main function from the stack.
    ///
    /// ## Panics
    ///
    /// - Not inside the main function.
    /// - Unclosed nested blocks remain.
    fn exit_main(&mut self) {
        assert!(self.is_main, "Current scope is not inside main function");
        self.exit_block();
        self.is_main = false;
        assert!(
            self.is_outside_function(),
            "Current scope is not nested in topmost scope"
        )
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
    fn analyze(from: &Self::From, ty: &ResolvedType, scope: &mut Scope)
        -> Result<Self, Diagnostic>;
}

impl Program {
    pub fn analyze(
        from: &parse::Program,
        jet_hinter: Box<dyn JetHinter>,
        diagnostics: &mut DiagnosticManager,
    ) -> Option<Self> {
        let before = diagnostics.error_count();
        let unit = ResolvedType::unit();
        let mut scope = Scope::new(jet_hinter, Vec::new());

        let items: Vec<Item> = from
            .items()
            .iter()
            .map(|item| match Item::analyze(item, &unit, &mut scope) {
                Ok(item) => item,
                Err(diag) => {
                    scope.report(diag);
                    Item::Error
                }
            })
            .collect();

        debug_assert!(scope.is_outside_function());
        debug_assert!(
            scope.module_path.is_empty(),
            "Unclosed module scopes remain"
        );

        let main = match Self::extract_single_main(&items) {
            Ok(Some(main)) => Some(main),
            Ok(None) => {
                scope.report(Error::MainRequired.with_span(from.into()));
                None
            }
            Err(err) => {
                scope.report(err.with_span(from.into()));
                None
            }
        };

        diagnostics.extend(scope.diagnostics().iter().cloned());
        if diagnostics.error_count() > before {
            return None;
        }

        let (parameters, witness_types, call_tracker) = scope.destruct();
        Some(Self {
            main: main?,
            parameters,
            witness_types,
            call_tracker: Arc::new(call_tracker),
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

impl AbstractSyntaxTree for Item {
    type From = parse::Item;

    fn analyze(
        from: &Self::From,
        ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<Self, Diagnostic> {
        assert!(ty.is_unit(), "Items cannot return anything");
        assert!(
            scope.is_outside_function(),
            "Variables live only inside the function"
        );

        match from {
            parse::Item::TypeAlias(alias) => {
                let span = *alias.as_ref();
                scope.insert_alias(alias.clone(), span).with_span(alias)?;
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
                // A sum of zero types would be uninhabited, which Simplicity's
                // type algebra cannot express; duplicate variant names leave the
                // enum's shape ambiguous. Either way the declaration is rejected,
                // but its *name* must still be registered — see below.
                let rejected: Vec<String> = if decl.variants().is_empty() {
                    vec![format!(
                        "enum '{}' must have at least one variant",
                        decl.name()
                    )]
                } else {
                    // The variants are independent, so every duplicated name reports.
                    let mut seen_names = HashSet::new();
                    let mut reported = HashSet::new();
                    decl.variants()
                        .iter()
                        .filter(|v| !seen_names.insert(v.name()) && reported.insert(v.name()))
                        .map(|v| {
                            format!(
                                "enum '{}' has duplicate variant name '{}'",
                                decl.name(),
                                v.name()
                            )
                        })
                        .collect()
                };

                if !rejected.is_empty() {
                    for msg in rejected {
                        scope.report(Diagnostic::new(Error::Grammar { msg }, decl.into()));
                    }

                    // The payload types are independent of the rejection, so
                    // resolve them anyway to surface their own errors.
                    for v in decl.variants() {
                        for payload_ty in v.payload() {
                            scope.resolve_or_poison(payload_ty, v.into());
                        }
                    }

                    // Register the name at a poison type instead of the enum, so
                    // that `let x: E = ..` does not cascade into "E is not
                    // defined" at every use.
                    scope
                        .insert_poison_alias(decl.name().clone(), decl.visibility().clone())
                        .with_span(decl)?;

                    return Ok(Self::EnumDeclaration);
                }

                let variants: Arc<[EnumVariantInfo]> = decl
                    .variants()
                    .iter()
                    .map(|v| {
                        let payload: Arc<[ResolvedType]> = v
                            .payload()
                            .iter()
                            .map(|ty| scope.resolve_or_poison(ty, v.into()))
                            .collect();
                        EnumVariantInfo::new(v.name().clone(), payload)
                    })
                    .collect();

                scope
                    .insert_enum(decl.name().clone(), decl.visibility().clone(), variants)
                    .with_span(decl)?;

                Ok(Self::EnumDeclaration)
            }
            parse::Item::Module(module) => {
                // A name collision is reported, not returned: the items inside
                // are independent of it, so they are analyzed in the existing
                // module of that name rather than discarded wholesale. A genuine
                // duplicate among them then reports itself, as any item would.
                if let Err(err) =
                    scope.enter_module(module.name().clone(), module.visibility().clone())
                {
                    scope.report(err.with_span(module.into()));
                    scope.reenter_module(module.name().clone());
                }

                let mut analyzed_children = Vec::new();
                for item in module.items() {
                    let analyzed = match Item::analyze(item, ty, scope) {
                        Ok(item) => item,
                        Err(diag) => {
                            scope.report(diag);
                            Item::Error
                        }
                    };
                    analyzed_children.push(analyzed);
                }
                scope.exit_module();
                Ok(Self::Module(analyzed_children))
            }
            parse::Item::Ignored => Ok(Self::Error),
        }
    }
}

impl AbstractSyntaxTree for Function {
    type From = parse::Function;

    fn analyze(
        from: &Self::From,
        ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<Self, Diagnostic> {
        assert!(ty.is_unit(), "Function definitions cannot return anything");
        assert!(
            scope.is_outside_function(),
            "Variables live only inside the function"
        );

        if from.name().as_inner() != MAIN_STR {
            let params: Arc<[FunctionParam]> = from
                .params()
                .iter()
                .map(|param| FunctionParam {
                    identifier: param.identifier().clone(),
                    ty: scope.resolve_or_poison(param.ty(), *from.span()),
                    span: *param.span(),
                })
                .collect();
            let ret = match from.ret() {
                Some(aliased) => scope.resolve_or_poison(aliased, from.into()),
                None => ResolvedType::unit(),
            };

            let body = {
                let guard = scope.block();
                for param in params.iter() {
                    guard
                        .scope
                        .insert_variable(param.identifier().clone(), param.ty().clone());
                }

                Arc::new(analyze_child(from.body(), &ret, guard.scope))
            };

            debug_assert!(scope.is_outside_function());
            let function = CustomFunction {
                params,
                body,
                span: *from.span(),
                is_never: false,
            };
            scope
                .insert_function(from.name().clone(), from.visibility().clone(), function)
                .with_span(from)?;

            return Ok(Self::Custom);
        }

        // An invalid signature is reported, not returned. `main` was written, so
        // erasing it here would invent a spurious `MainRequired`, skip the body,
        // and hide a second `main`. It survives as a poisoned `Function::Main`,
        // exactly as a `main` whose body fails already does.
        let span: Span = from.into();

        if !from.params().is_empty() {
            scope.report(Diagnostic::new(Error::MainNoInputs, span));
        }
        if let Some(aliased) = from.ret() {
            let resolved = scope.resolve_or_poison(aliased, span);
            // A poisoned return type absorbs this check: the alias was already
            // reported, and whether it is unit is unknowable.
            if !resolved.is_unit() && !resolved.is_never() {
                scope.report(Diagnostic::new(Error::MainNoOutput, span));
            }
        }
        if matches!(from.visibility(), Visibility::Public) {
            scope.report(Diagnostic::new(Error::MainCannotBePublic, span));
        }

        // The rejected parameters are still declared, so bind them: a body that
        // uses one must not cascade into "undefined variable".
        let params: Vec<(Identifier, ResolvedType)> = from
            .params()
            .iter()
            .map(|param| {
                (
                    param.identifier().clone(),
                    scope.resolve_or_poison(param.ty(), span),
                )
            })
            .collect();

        let guard = scope.main_scope();
        for (identifier, param_ty) in params {
            guard.scope.insert_variable(identifier, param_ty);
        }

        // The body is checked against unit whatever the declared return type:
        // `Function::Main` always carries a unit-typed body, so a rejected
        // return type must not change what the body is held to.
        let body = analyze_child(from.body(), ty, guard.scope);
        Ok(Self::Main(body))
    }
}

impl AbstractSyntaxTree for Statement {
    type From = parse::Statement;

    fn analyze(
        from: &Self::From,
        ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<Self, Diagnostic> {
        assert!(ty.is_unit(), "Statements cannot return anything");
        match from {
            parse::Statement::Assignment(assignment) => {
                Assignment::analyze(assignment, ty, scope).map(Self::Assignment)
            }
            parse::Statement::Expression(expression) => {
                Expression::analyze(expression, ty, scope).map(Self::Expression)
            }
            parse::Statement::Error(_) => Ok(Self::Error),
        }
    }
}

impl AbstractSyntaxTree for Assignment {
    type From = parse::Assignment;

    // TODO: So, currently we do not need a `Diagnostic` for this
    fn analyze(
        from: &Self::From,
        ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<Self, Diagnostic> {
        assert!(ty.is_unit(), "Assignments cannot return anything");
        // The assignment is a statement that returns nothing.
        //
        // However, the expression evaluated in the assignment does have a type,
        // namely the type specified in the assignment.
        let ty_expr = scope.resolve_or_poison(from.ty(), from.into());

        let expression = analyze_child(from.expression(), &ty_expr, scope);
        let typed_variables = bind_pattern(from.pattern(), &ty_expr, scope, from.into());
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
        Self::analyze(from, ty, &mut empty_scope)
    }

    fn error(ty: ResolvedType, span: Span) -> Self {
        let inner = ExpressionInner::Single(SingleExpression {
            inner: SingleExpressionInner::Error,
            ty: ty.clone(),
            span,
        });

        Expression { inner, ty, span }
    }
}

/// Bind a pattern's identifiers, recovering from a failed shape check.
///
/// The shape error is reported and the identifiers are bound at poison, so later
/// uses do not cascade into "undefined variable".
fn bind_pattern(
    pattern: &Pattern,
    ty: &ResolvedType,
    scope: &mut Scope,
    span: Span,
) -> HashMap<Identifier, ResolvedType> {
    match pattern.is_of_type(ty) {
        Ok(variables) => variables,
        Err(err) => {
            let reuse_reported = matches!(err, Error::VariableReuseInPattern { .. });
            scope.report(err.with_span(span));
            poison_bindings(pattern, reuse_reported, scope, span)
        }
    }
}

/// Bind every identifier a pattern declares at a poison type.
///
/// Used when the pattern does not match its annotation: the shape error was
/// already reported, and dropping the identifiers would cascade into
/// "undefined variable" at every use of them.
///
/// A duplicate binding is reported here, because [`Pattern::is_of_type`] returns
/// only its first error and a shape mismatch would otherwise hide it. Set
/// `reuse_reported` when the caller's error already was the reuse itself.
fn poison_bindings(
    pattern: &Pattern,
    reuse_reported: bool,
    scope: &mut Scope,
    span: Span,
) -> HashMap<Identifier, ResolvedType> {
    let mut bindings = HashMap::new();
    for identifier in pattern.identifiers() {
        let duplicate = bindings
            .insert(identifier.clone(), ResolvedType::never())
            .is_some();
        if duplicate && !reuse_reported {
            scope.report(
                Error::VariableReuseInPattern {
                    identifier: identifier.clone(),
                }
                .with_span(span),
            );
        }
    }
    bindings
}

/// Analyze one child expression, substituting a poison node if it fails.
///
/// Catches the error instead of propagating it, so the caller keeps analyzing
/// whatever comes after the child: a sibling, a registration, or an artifact.
fn analyze_child(child: &parse::Expression, ty: &ResolvedType, scope: &mut Scope) -> Expression {
    match Expression::analyze(child, ty, scope) {
        Ok(expr) => expr,
        Err(diag) => {
            scope.report(diag);
            Expression::error(ty.clone(), *child.span())
        }
    }
}

/// Analyze a container's children, each against its own expected type.
///
/// Missing expected types are padded with poison, so a count mismatch between
/// children and types never hides a child's own errors. Catches every child, so
/// it cannot fail.
fn analyze_children(
    children: &[parse::Expression],
    expected: &[ResolvedType],
    scope: &mut Scope,
) -> Arc<[Expression]> {
    children
        .iter()
        .enumerate()
        .map(|(i, child)| {
            let ty = expected.get(i).cloned().unwrap_or_else(ResolvedType::never);
            analyze_child(child, &ty, scope)
        })
        .collect()
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
) -> Result<EnumConstruction, Diagnostic> {
    let span = *construction.span();

    // A construction we cannot analyze structurally still has arguments whose
    // own errors must surface, so drain them at a poison type before bailing.
    let Some(info) = ty.as_enum() else {
        analyze_children(construction.args(), &[], scope);
        return Err(Error::ExpressionUnexpectedType { ty: ty.clone() }).with_span(span);
    };

    // The written name must be the expected enum's.
    // Enums are declared at the top level, so only a single identifier can name one.
    // An alias in scope must resolve to the expected type.
    // Without a scope (witness and argument files) the declared name itself matches.
    let written = construction.enum_path_string();
    let names_expected_enum = match construction.enum_path() {
        [single] => {
            let alias = AliasName::from_str_unchecked(single.as_inner());
            match scope.get_alias(&alias) {
                Ok(resolved) if &resolved == ty => true,
                Ok(resolved) => {
                    analyze_children(construction.args(), &[], scope);
                    return Err(Error::ExpressionTypeMismatch {
                        expected: ty.clone(),
                        found: resolved,
                    })
                    .with_span(span);
                }
                Err(_) => scope.unscoped_enum_names && written == info.name(),
            }
        }
        _ => false,
    };
    if !names_expected_enum {
        analyze_children(construction.args(), &[], scope);
        return Err(Error::Grammar {
            msg: format!("`{written}` does not name enum `{}`", info.name()),
        })
        .with_span(span);
    }

    let Some((variant_index, variant)) = info.variant(construction.variant()) else {
        analyze_children(construction.args(), &[], scope);
        return Err(enum_variant_error(construction.variant().as_inner(), info)).with_span(span);
    };

    // The variant is known, so the payload types are the best expected types
    // available even when the count disagrees: report the count and keep going.
    if construction.args().len() != variant.payload().len() {
        scope.report(
            Error::Grammar {
                msg: format!(
                    "variant `{}` of enum `{}` carries {} payload value(s), found {}",
                    construction.variant(),
                    info.name(),
                    variant.payload().len(),
                    construction.args().len()
                ),
            }
            .with_span(span),
        );
    }

    let payload: Arc<[Arc<Expression>]> =
        analyze_children(construction.args(), variant.payload(), scope)
            .iter()
            .cloned()
            .map(Arc::new)
            .collect();

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

    fn analyze(
        from: &Self::From,
        ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<Self, Diagnostic> {
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
                let guard = scope.block();
                let ast_statements = statements
                    .iter()
                    .map(
                        |s| match Statement::analyze(s, &ResolvedType::unit(), guard.scope) {
                            Ok(stmt) => stmt,
                            Err(diag) => {
                                guard.scope.report(diag);
                                Statement::Error
                            }
                        },
                    )
                    .collect();

                let ast_expression = match expression {
                    Some(expression) => Expression::analyze(expression, ty, guard.scope)
                        .map(Arc::new)
                        .map(Some),

                    // A poisoned expected type absorbs the missing-tail check: the
                    // annotation was already reported, so demanding unit here would
                    // cascade.
                    None if ty.is_unit() || ty.is_never() => Ok(None),
                    None => Err(Error::ExpressionTypeMismatch {
                        expected: ty.clone(),
                        found: ResolvedType::unit(),
                    })
                    .with_span(from),
                }?;

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

    fn analyze(
        from: &Self::From,
        ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<Self, Diagnostic> {
        let inner = match from.inner() {
            parse::SingleExpressionInner::Boolean(bit) => {
                if ty.is_never() {
                    SingleExpressionInner::Error
                } else if !ty.is_boolean() {
                    return Err(Error::ExpressionTypeMismatch {
                        expected: ty.clone(),
                        found: ResolvedType::boolean(),
                    })
                    .with_span(from);
                } else {
                    SingleExpressionInner::Constant(Value::from(*bit))
                }
            }
            parse::SingleExpressionInner::Decimal(decimal) => {
                if ty.is_never() {
                    SingleExpressionInner::Error
                } else {
                    let ty = ty
                        .as_integer()
                        .ok_or_else(|| Error::ExpressionUnexpectedType { ty: ty.clone() })
                        .with_span(from)?;

                    UIntValue::parse_decimal(decimal, ty)
                        .with_span(from)
                        .map(Value::from)
                        .map(SingleExpressionInner::Constant)?
                }
            }
            parse::SingleExpressionInner::Binary(bits) => {
                if ty.is_never() {
                    SingleExpressionInner::Error
                } else {
                    let ty = ty
                        .as_integer()
                        .ok_or_else(|| Error::ExpressionUnexpectedType { ty: ty.clone() })
                        .with_span(from)?;

                    let value = UIntValue::parse_binary(bits, ty).with_span(from)?;
                    SingleExpressionInner::Constant(Value::from(value))
                }
            }
            parse::SingleExpressionInner::Hexadecimal(bytes) => {
                if ty.is_never() {
                    SingleExpressionInner::Error
                } else {
                    let value = Value::parse_hexadecimal(bytes, ty).with_span(from)?;
                    SingleExpressionInner::Constant(value)
                }
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
                    .ok_or_else(|| Error::UndefinedVariable {
                        identifier: identifier.clone(),
                    })
                    .with_span(from)?;

                if !ty.compatible(bound_ty) {
                    return Err(Error::ExpressionTypeMismatch {
                        expected: ty.clone(),
                        found: bound_ty.clone(),
                    })
                    .with_span(from);
                }

                // Reading a variable does not rebind it. `insert_variable` writes
                // into the innermost scope, so binding the *expected* type here
                // shadows the declaration.
                SingleExpressionInner::Variable(identifier.clone())
            }
            parse::SingleExpressionInner::Expression(parse) => {
                Expression::analyze(parse, ty, scope)
                    .map(Arc::new)
                    .map(SingleExpressionInner::Expression)?
            }
            parse::SingleExpressionInner::Tuple(tuple) => {
                // A shape or arity failure is reported, not returned: the
                // elements are independent, so each must still be analyzed.
                let types: Vec<ResolvedType> = match ty.as_tuple() {
                    Some(types) => {
                        if types.len() != tuple.len() {
                            report_shape_mismatch(ty, *from.as_ref(), scope);
                        }
                        // The slots that do line up keep their known types, so a
                        // wrongly typed element still reports.
                        types.iter().map(|a| a.as_ref().clone()).collect()
                    }
                    // Not a tuple at all: no slot types to keep.
                    None => {
                        report_shape_mismatch(ty, *from.as_ref(), scope);
                        vec![ResolvedType::never(); tuple.len()]
                    }
                };

                SingleExpressionInner::Tuple(analyze_children(tuple, &types, scope))
            }
            parse::SingleExpressionInner::Array(array) => {
                // A size mismatch leaves the element type intact, so it stays
                // the expected type; only a non-array annotation poisons it.
                let el_ty: ResolvedType = match ty.as_array() {
                    Some((el_ty, size)) => {
                        if array.len() != size {
                            scope.report(
                                Error::ExpressionUnexpectedType { ty: ty.clone() }
                                    .with_span(from.into()),
                            );
                        }
                        el_ty.clone()
                    }
                    None => {
                        report_shape_mismatch(ty, *from.as_ref(), scope);
                        ResolvedType::never()
                    }
                };

                let types = vec![el_ty; array.len()];
                SingleExpressionInner::Array(analyze_children(array, &types, scope))
            }
            parse::SingleExpressionInner::List(list) => {
                let el_ty: ResolvedType = match ty.as_list() {
                    Some((el_ty, bound)) => {
                        if bound.get() <= list.len() {
                            scope.report(
                                Error::ExpressionUnexpectedType { ty: ty.clone() }
                                    .with_span(from.into()),
                            );
                        }
                        el_ty.clone()
                    }
                    None => {
                        report_shape_mismatch(ty, *from.as_ref(), scope);
                        ResolvedType::never()
                    }
                };

                let types = vec![el_ty; list.len()];
                SingleExpressionInner::List(analyze_children(list, &types, scope))
            }
            parse::SingleExpressionInner::Either(either) => {
                // A shape mismatch is reported, not returned: the wrapped child
                // has its own errors either way, so it is analyzed against
                // poison, the only expected type left.
                let (ty_l, ty_r) = match ty.as_either() {
                    Some((ty_l, ty_r)) => (ty_l.clone(), ty_r.clone()),
                    None => {
                        report_shape_mismatch(ty, *from.as_ref(), scope);
                        (ResolvedType::never(), ResolvedType::never())
                    }
                };

                let inner = match either {
                    Either::Left(parse_l) => {
                        Either::Left(Arc::new(analyze_child(parse_l, &ty_l, scope)))
                    }
                    Either::Right(parse_r) => {
                        Either::Right(Arc::new(analyze_child(parse_r, &ty_r, scope)))
                    }
                };
                SingleExpressionInner::Either(inner)
            }
            parse::SingleExpressionInner::Option(maybe_parse) => {
                let inner_ty: ResolvedType = match ty.as_option() {
                    Some(inner_ty) => inner_ty.clone(),
                    None => {
                        report_shape_mismatch(ty, *from.as_ref(), scope);
                        ResolvedType::never()
                    }
                };

                let inner = maybe_parse
                    .as_ref()
                    .map(|parse| Arc::new(analyze_child(parse, &inner_ty, scope)));
                SingleExpressionInner::Option(inner)
            }
            parse::SingleExpressionInner::Call(call) => {
                Call::analyze(call, ty, scope).map(SingleExpressionInner::Call)?
            }
            parse::SingleExpressionInner::Match(match_) => {
                Match::analyze(match_, ty, scope).map(SingleExpressionInner::Match)?
            }
            parse::SingleExpressionInner::EnumConstruction(construction) => {
                if ty.is_never() {
                    // The variant is unknowable, but the payload arguments are
                    // independent of it: drain them at poison so their own
                    // errors still surface.
                    analyze_children(construction.args(), &[], scope);
                    SingleExpressionInner::Error
                } else {
                    analyze_enum_construction(construction, ty, scope)
                        .map(SingleExpressionInner::EnumConstruction)?
                }
            }
            parse::SingleExpressionInner::EnumMatch(enum_match) => {
                analyze_enum_match(enum_match, ty, scope)?
            }
            parse::SingleExpressionInner::Error => SingleExpressionInner::Error,
        };

        Ok(Self {
            inner,
            ty: ty.clone(),
            span: *from.as_ref(),
        })
    }
}

/// Report a shape mismatch, unless the expected type is poison.
fn report_shape_mismatch(ty: &ResolvedType, span: Span, scope: &mut Scope) {
    if !ty.is_never() {
        scope.report(Error::ExpressionUnexpectedType { ty: ty.clone() }.with_span(span));
    }
}

/// Surface the errors inside an enum match that cannot be analyzed structurally.
///
/// The scrutinee and the arm bodies are independent of the variant bookkeeping
/// that failed — an unknown enum, an unknown or duplicated variant, a missing
/// one — so they are analyzed anyway. Without a known variant the declared
/// bindings cannot be trusted, so their identifiers are bound at poison, which
/// keeps the bodies from cascading into "undefined variable".
fn drain_enum_match(from: &parse::EnumMatch, ty: &ResolvedType, scope: &mut Scope) {
    let span = *from.span();
    analyze_child(from.scrutinee(), &ResolvedType::never(), scope);

    for arm in from.arms() {
        let guard = scope.block();
        for (pattern, declared) in arm.bindings() {
            // Resolve to surface the declared type's own errors, but discard it.
            guard.scope.resolve_or_poison(declared, span);
            // Nothing was reported for this pattern, so a duplicate still counts.
            for (identifier, binding_ty) in poison_bindings(pattern, false, guard.scope, span) {
                guard.scope.insert_variable(identifier, binding_ty);
            }
        }
        analyze_child(arm.expression(), ty, guard.scope);
    }
}

/// Surface the errors inside an enum match whose enum is known, but whose arms
/// do not form a usable match.
///
/// The enum resolved, so every check independent of the broken bookkeeping still
/// runs: the scrutinee is checked against the real enum type, and an arm naming a
/// known variant has its payload bindings validated. Only the arms that failed
/// fall back to poison.
fn drain_known_enum_match(
    from: &parse::EnumMatch,
    ty: &ResolvedType,
    enum_ty: &ResolvedType,
    info: &EnumInfo,
    scope: &mut Scope,
) {
    // Matching a `u32` against `E::..` is an error whether or not the arms name
    // real variants of `E`.
    analyze_child(from.scrutinee(), enum_ty, scope);

    let expected_path = from.arms()[0].enum_path();
    for arm in from.arms() {
        let variant = if arm.enum_path() == expected_path {
            info.variant(arm.variant()).map(|(_, variant)| variant)
        } else {
            None
        };
        analyze_enum_match_arm(arm, variant, ty, scope);
    }
}

/// Analyze an enum match into the expression node it yields.
///
/// Returns the node rather than an [`EnumMatch`], because a match whose enum is
/// poisoned yields [`SingleExpressionInner::Error`] instead: there is no match
/// to build and nothing further to report. `Err` carries the one diagnostic the
/// caller should report; any others are reported here.
fn analyze_enum_match(
    from: &parse::EnumMatch,
    ty: &ResolvedType,
    scope: &mut Scope,
) -> Result<SingleExpressionInner, Diagnostic> {
    let arms = from.arms();
    let span = *from.span();
    debug_assert!(!arms.is_empty(), "the parser rejects empty enum matches");

    let enum_name = arms[0].enum_path_string();
    let [single] = arms[0].enum_path() else {
        drain_enum_match(from, ty, scope);
        return Err(Error::Grammar {
            msg: format!(
                "`{enum_name}` does not name an enum; enums are declared at the \
                     top level, so match arms name them by a single identifier"
            ),
        })
        .with_span(span);
    };
    let alias = AliasName::from_str_unchecked(single.as_inner());
    let enum_ty = match scope.get_alias(&alias) {
        Ok(enum_ty) => enum_ty,
        Err(err) => {
            drain_enum_match(from, ty, scope);
            return Err(err).with_span(span);
        }
    };
    // A poisoned alias absorbs the check: whether it names an enum is
    // unknowable, and its own error was already reported at the declaration.
    if enum_ty.is_never() {
        drain_enum_match(from, ty, scope);
        return Ok(SingleExpressionInner::Error);
    }

    let info = match enum_ty.as_enum() {
        Some(info) => info.clone(),
        None => {
            drain_enum_match(from, ty, scope);
            return Err(Error::Grammar {
                msg: format!(
                    "`{enum_name}` is not an enum, so match arms of the form \
                         `{enum_name}::Variant` cannot apply to it"
                ),
            })
            .with_span(span);
        }
    };

    // One slot per variant, in declaration order.
    // the order of the leaves of the enum's balanced sum.
    let mut arms_by_index: Vec<Option<&parse::EnumMatchArm>> = vec![None; info.variants().len()];
    // The arms are independent: a wrong enum path, an unknown variant or a
    // duplicate says nothing about the arm beside it, so the loop records
    // each and keeps going.
    let mut arm_errors: Vec<Diagnostic> = Vec::new();
    for arm in arms {
        if arm.enum_path() != arms[0].enum_path() {
            arm_errors.push(
                Error::Grammar {
                    msg: format!(
                        "all match arms must use the same enum; expected '{}', found '{}'",
                        enum_name,
                        arm.enum_path_string()
                    ),
                }
                .with_span(span),
            );
            continue;
        }
        let Some((index, _)) = info.variant(arm.variant()) else {
            arm_errors.push(
                Error::Grammar {
                    msg: format!(
                        "variant '{}' is not defined in enum '{}'",
                        arm.variant(),
                        enum_name
                    ),
                }
                .with_span(span),
            );
            continue;
        };
        let slot = &mut arms_by_index[index];
        if slot.is_some() {
            arm_errors.push(
                Error::Grammar {
                    msg: format!("duplicate arm for variant '{}'", arm.variant()),
                }
                .with_span(span),
            );
            continue;
        }
        *slot = Some(arm);
    }

    if !arm_errors.is_empty() {
        drain_known_enum_match(from, ty, &enum_ty, &info, scope);
        // The caller reports the one we return, so the rest go in here.
        let first = arm_errors.remove(0);
        for diag in arm_errors {
            scope.report(diag);
        }
        return Err(first);
    }

    // One collect: Some(arms) iff every variant is covered.
    let covered: Option<Vec<&parse::EnumMatchArm>> = arms_by_index.iter().copied().collect();
    let Some(covered) = covered else {
        let missing: Vec<String> = arms_by_index
            .iter()
            .zip(info.variants())
            .filter(|(slot, _)| slot.is_none())
            .map(|(_, variant)| format!("'{}'", variant.name()))
            .collect();
        drain_known_enum_match(from, ty, &enum_ty, &info, scope);
        return Err(Error::Grammar {
            msg: format!(
                "enum match on '{}' must cover all {} variants; missing: {}",
                enum_name,
                info.variants().len(),
                missing.join(", ")
            ),
        })
        .with_span(span);
    };

    // Analyze the scrutinee against the nominal enum type, so that
    // matching a value of a different enum (or any other type) against
    // this enum's variants is a type error.
    // A poisoned scrutinee must not suppress the arm-body errors.
    let scrutinee = Arc::new(analyze_child(from.scrutinee(), &enum_ty, scope));

    let arm_asts = covered
        .into_iter()
        .zip(info.variants())
        .map(|(arm, variant)| analyze_enum_match_arm(arm, Some(variant), ty, scope))
        .collect::<Arc<[EnumMatchArm]>>();

    Ok(SingleExpressionInner::EnumMatch(EnumMatch {
        scrutinee,
        arms: arm_asts,
        span,
    }))
}

/// Analyze one match arm: its bindings, then its body.
///
/// `variant` is `None` when the arm names no known variant, which leaves no
/// payload to check the bindings against.
fn analyze_enum_match_arm(
    arm: &parse::EnumMatchArm,
    variant: Option<&EnumVariantInfo>,
    ty: &ResolvedType,
    scope: &mut Scope,
) -> EnumMatchArm {
    let arm_span = *arm.span();
    // A failed binding poisons only this arm; later arms still run.
    let (pattern, fits) = analyze_enum_arm_bindings(arm, variant, scope, arm_span);

    let guard = scope.block();

    // When the arity is wrong the combined pattern cannot match the payload,
    // and saying so again would only restate the arity error. Check it against
    // poison instead of skipping the check.
    let expected = match variant {
        Some(variant) if fits => variant.payload_type().clone(),
        _ => ResolvedType::never(),
    };
    let typed_variables = bind_pattern(&pattern, &expected, guard.scope, arm_span);
    for (identifier, variable_ty) in typed_variables {
        guard.scope.insert_variable(identifier, variable_ty);
    }
    let body = Arc::new(analyze_child(arm.expression(), ty, guard.scope));

    EnumMatchArm {
        pattern,
        body,
        span: arm_span,
    }
}

/// Check an enum match arm's payload bindings against the variant's declared
/// payload types and combine them into one pattern for the variant's leaf.
///
/// Unit variants bind nothing ([`Pattern::Ignore`]); a single binding stands
/// alone; multiple bindings form a tuple pattern, matching the tuple that a
/// multi-payload variant carries at its leaf.
/// Reports rather than returns: an arm whose bindings do not fit the variant
/// still declares its identifiers, and every binding is checked, so one bad
/// declared type neither hides the next nor drops the arm's names.
///
/// Also returns whether the pattern *fits* the variant's payload. When it does
/// not, the arity error was already reported here, and the caller must bind the
/// identifiers at poison rather than check the combined pattern against the
/// payload type.
///
/// `variant` is `None` when the arm names no known variant; the caller reported
/// that, and there is no payload to check, but the declared types are still
/// resolved so their own errors surface.
fn analyze_enum_arm_bindings(
    arm: &parse::EnumMatchArm,
    variant: Option<&EnumVariantInfo>,
    scope: &mut Scope,
    span: Span,
) -> (Pattern, bool) {
    let payload: &[ResolvedType] = variant.map_or(&[], EnumVariantInfo::payload);
    let fits = variant.is_some() && arm.bindings().len() == payload.len();
    if variant.is_some() && !fits {
        scope.report(
            Error::Grammar {
                msg: format!(
                    "variant '{}' of enum '{}' carries {} payload value(s), \
                     but the arm binds {}",
                    arm.variant(),
                    arm.enum_path_string(),
                    payload.len(),
                    arm.bindings().len()
                ),
            }
            .with_span(span),
        );
    }

    let mut patterns = Vec::with_capacity(arm.bindings().len());
    for (i, (pattern, declared)) in arm.bindings().iter().enumerate() {
        let declared = scope.resolve_or_poison(declared, span);

        // Compare only against a payload slot that exists; a count mismatch
        // was already reported above, and an unknown variant has no payload.
        if let Some(payload_ty) = payload.get(i) {
            if !declared.compatible(payload_ty) {
                scope.report(
                    Error::ExpressionTypeMismatch {
                        expected: payload_ty.clone(),
                        found: declared,
                    }
                    .with_span(span),
                );
            }
        }
        patterns.push(pattern.clone());
    }

    let pattern = match patterns.len() {
        0 => Pattern::Ignore,
        1 => patterns[0].clone(),
        _ => Pattern::tuple(patterns),
    };
    (pattern, fits)
}

impl AbstractSyntaxTree for Call {
    type From = parse::Call;

    fn analyze(
        from: &Self::From,
        ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<Self, Diagnostic> {
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
            if observed_ty.compatible(expected_ty) {
                Ok(())
            } else {
                Err(Error::ExpressionTypeMismatch {
                    expected: expected_ty.clone(),
                    found: observed_ty.clone(),
                })
            }
        }

        /// Report a callee-level failure without returning.
        ///
        /// The arguments are analyzed independently of the arity and of the
        /// output type, so a failure here must not stop them from surfacing
        /// their own errors.
        fn report_check(result: Result<(), Error>, scope: &mut Scope, span: Span) {
            if let Err(err) = result {
                scope.report(err.with_span(span));
            }
        }

        let span = *from.as_ref();

        let name = match CallName::analyze(from, ty, scope) {
            Ok(n) => n,
            Err(name_err) => {
                // callee unknown: analyze args against error() to surface their errors,
                // then propagate the name error (do not double-report, because container reports it)
                analyze_children(from.args(), &[], scope);
                return Err(name_err);
            }
        };

        if name.is_never() {
            let args = analyze_children(from.args(), &[], scope);
            return Ok(Self {
                name,
                args,
                span: *from.as_ref(),
            });
        }

        let args = match name.clone() {
            CallName::Jet(jet) => {
                let args_tys = source_type(&*jet)
                    .iter()
                    .map(AliasedType::resolve_builtin)
                    .collect::<Result<Vec<ResolvedType>, AliasName>>()
                    .map_err(|alias| Error::UndefinedAlias { name: alias })
                    .with_span(from)?;
                report_check(check_argument_types(from.args(), &args_tys), scope, span);

                let out_ty = target_type(&*jet)
                    .resolve_builtin()
                    .map_err(|alias| Error::UndefinedAlias { name: alias })
                    .with_span(from)?;
                report_check(check_output_type(&out_ty, ty), scope, span);

                scope.track_call(from, TrackedCallName::Jet);
                analyze_children(from.args(), &args_tys, scope)
            }
            CallName::UnwrapLeft(right_ty) => {
                let args_tys = [ResolvedType::either(ty.clone(), right_ty)];
                report_check(check_argument_types(from.args(), &args_tys), scope, span);

                let args = analyze_children(from.args(), &args_tys, scope);
                let [arg_ty] = args_tys;

                scope.track_call(from, TrackedCallName::UnwrapLeft(arg_ty));
                args
            }
            CallName::UnwrapRight(left_ty) => {
                let args_tys = [ResolvedType::either(left_ty, ty.clone())];
                report_check(check_argument_types(from.args(), &args_tys), scope, span);

                let args = analyze_children(from.args(), &args_tys, scope);
                let [arg_ty] = args_tys;
                scope.track_call(from, TrackedCallName::UnwrapRight(arg_ty));
                args
            }
            CallName::IsNone(some_ty) => {
                let args_tys = [ResolvedType::option(some_ty)];
                report_check(check_argument_types(from.args(), &args_tys), scope, span);

                let out_ty = ResolvedType::boolean();
                report_check(check_output_type(&out_ty, ty), scope, span);
                analyze_children(from.args(), &args_tys, scope)
            }
            CallName::Unwrap => {
                let args_tys = [ResolvedType::option(ty.clone())];
                report_check(check_argument_types(from.args(), &args_tys), scope, span);

                scope.track_call(from, TrackedCallName::Unwrap);
                analyze_children(from.args(), &args_tys, scope)
            }
            CallName::Assert => {
                let args_tys = [ResolvedType::boolean()];
                report_check(check_argument_types(from.args(), &args_tys), scope, span);

                let out_ty = ResolvedType::unit();
                report_check(check_output_type(&out_ty, ty), scope, span);

                scope.track_call(from, TrackedCallName::Assert);
                analyze_children(from.args(), &args_tys, scope)
            }
            CallName::Panic => {
                let args_tys = [];
                report_check(check_argument_types(from.args(), &args_tys), scope, span);

                // panic! allows every output type because it will never return anything
                scope.track_call(from, TrackedCallName::Panic);
                analyze_children(from.args(), &args_tys, scope)
            }
            CallName::Debug => {
                let args_tys = [ty.clone()];
                report_check(check_argument_types(from.args(), &args_tys), scope, span);

                let args = analyze_children(from.args(), &args_tys, scope);
                let [arg_ty] = args_tys;

                scope.track_call(from, TrackedCallName::Debug(arg_ty));
                args
            }
            CallName::TypeCast(source) => {
                // Casts prove structural equality, but enums are nominal:
                // every enum must map to itself at its structural position
                // (see `cast_preserves_enum_identity`), else same-shaped
                // enums would convert variants by ordinal position.
                // A poisoned type on either side absorbs the check: the cause was
                // already reported, and `StructuralType` cannot represent poison
                // (converting one panics, by design — see the gate).
                let comparable = !source.contains_never() && !ty.contains_never();
                if comparable
                    && (!cast_preserves_enum_identity(&source, ty)
                        || StructuralType::from(&source) != StructuralType::from(ty))
                {
                    scope.report(
                        Error::InvalidCast {
                            source: source.clone(),
                            target: ty.clone(),
                        }
                        .with_span(span),
                    );
                }

                let args_tys = [source];
                report_check(check_argument_types(from.args(), &args_tys), scope, span);
                analyze_children(from.args(), &args_tys, scope)
            }
            CallName::Custom(function) => {
                let args_ty = function
                    .params()
                    .iter()
                    .map(FunctionParam::ty)
                    .cloned()
                    .collect::<Vec<ResolvedType>>();
                report_check(check_argument_types(from.args(), &args_ty), scope, span);

                let out_ty = function.body().ty();
                report_check(check_output_type(out_ty, ty), scope, span);
                analyze_children(from.args(), &args_ty, scope)
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
                report_check(check_argument_types(from.args(), &args_ty), scope, span);

                let out_ty = function.body().ty();
                report_check(check_output_type(out_ty, ty), scope, span);

                analyze_children(from.args(), &args_ty, scope)
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
                report_check(check_argument_types(from.args(), &args_ty), scope, span);

                let out_ty = function.body().ty();
                report_check(check_output_type(out_ty, ty), scope, span);

                analyze_children(from.args(), &args_ty, scope)
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
                report_check(check_argument_types(from.args(), &args_ty), scope, span);

                let out_ty = function.body().ty();
                report_check(check_output_type(out_ty, ty), scope, span);

                analyze_children(from.args(), &args_ty, scope)
            }
        };

        Ok(Self {
            name,
            args,
            span: *from.as_ref(),
        })
    }
}

/// Does the function have a foldable signature, `fn f(element: E, acc: A) -> A`?
///
/// Compares with [`ResolvedType::compatible`] rather than `==`: while any type
/// in the signature is poisoned the answer is unknowable, so the check is
/// absorbed rather than failed, which would cascade on top of the type's own
/// error.
fn is_foldable(function: &CustomFunction) -> bool {
    function.is_never()
        || (function.params().len() == 2
            && function.params()[1].ty().compatible(function.body().ty()))
}

impl AbstractSyntaxTree for CallName {
    // Take parse::Call, so we have access to the span for pretty errors
    type From = parse::Call;

    fn analyze(
        from: &Self::From,
        _ty: &ResolvedType,
        scope: &mut Scope,
    ) -> Result<Self, Diagnostic> {
        match from.name() {
            parse::CallName::Jet(name) => match scope.jet_hinter.parse_jet(name.as_inner()) {
                Some(jet) if !jet.is_disabled() => Ok(Self::Jet(jet)),
                _ => Err(Error::JetDoesNotExist { name: name.clone() }).with_span(from),
            },
            // A builtin's type argument resolves like any other type: every
            // undefined alias in it is independent, so all of them are reported
            // and the call proceeds against a poisoned type argument.
            parse::CallName::UnwrapLeft(right_ty) => Ok(Self::UnwrapLeft(
                scope.resolve_or_poison(right_ty, *from.as_ref()),
            )),
            parse::CallName::UnwrapRight(left_ty) => Ok(Self::UnwrapRight(
                scope.resolve_or_poison(left_ty, *from.as_ref()),
            )),
            parse::CallName::IsNone(some_ty) => Ok(Self::IsNone(
                scope.resolve_or_poison(some_ty, *from.as_ref()),
            )),
            parse::CallName::Unwrap => Ok(Self::Unwrap),
            parse::CallName::Assert => Ok(Self::Assert),
            parse::CallName::Panic => Ok(Self::Panic),
            parse::CallName::Debug => Ok(Self::Debug),
            // Safe to poison: the cast's structural check already skips a
            // poisoned side, which `StructuralType` cannot represent.
            parse::CallName::TypeCast(target) => Ok(Self::TypeCast(
                scope.resolve_or_poison(target, *from.as_ref()),
            )),
            parse::CallName::Custom(name) => {
                scope.get_function(name).map(Self::Custom).with_span(from)
            }
            parse::CallName::ArrayFold(name, size) => {
                let function = scope.get_function(name).with_span(from)?;
                // A function that is used in a array fold has the signature:
                //   fn f(element: E, accumulator: A) -> A
                //
                // `compatible` rather than `==`: while the signature holds a
                // poisoned type, foldability is unknowable, so the check is
                // absorbed instead of failed.
                if is_foldable(&function) {
                    Ok(Self::ArrayFold(function, *size))
                } else {
                    Err(Error::FunctionNotFoldable { name: name.clone() }).with_span(from)
                }
            }
            parse::CallName::Fold(name, bound) => {
                let function = scope.get_function(name).with_span(from)?;
                // A function that is used in a list fold has the signature:
                //   fn f(element: E, accumulator: A) -> A
                if is_foldable(&function) {
                    Ok(Self::Fold(function, *bound))
                } else {
                    Err(Error::FunctionNotFoldable { name: name.clone() }).with_span(from)
                }
            }
            parse::CallName::ForWhile(name) => {
                let function = scope.get_function(name).with_span(from)?;
                // A poisoned signature has no shape to check against.
                if function.is_never() {
                    return Ok(Self::ForWhile(function, Pow2Usize::ONE));
                }
                // A function that is used in a for-while loop has the signature:
                //   fn f(accumulator: A, readonly_context: C, counter: u{N}) -> Either<B, A>
                // where
                //   N is a power of two
                if function.params().len() != 3 {
                    return Err(Error::FunctionNotLoopable { name: name.clone() }).with_span(from);
                }
                match function.body().ty().as_either() {
                    Some((_, out_r))
                        if out_r.compatible(function.params().first().unwrap().ty()) => {}
                    // A poisoned body type absorbs the shape check: whether it
                    // is the required `Either` is unknowable.
                    _ if function.body().ty().is_never() => {}
                    _ => {
                        return Err(Error::FunctionNotLoopable { name: name.clone() })
                            .with_span(from);
                    }
                }
                // Disable loops for u32 or higher since no one will want to run
                // 2^32 = 4294967296 ≈ 4 billion iterations.
                // The resulting Simplicity program will not fit into a Bitcoin block.
                let counter_ty = function.params().get(2).unwrap().ty();

                match counter_ty.as_integer() {
                    Some(
                        int_ty @ (UIntType::U1
                        | UIntType::U2
                        | UIntType::U4
                        | UIntType::U8
                        | UIntType::U16),
                    ) => Ok(Self::ForWhile(function, int_ty.bit_width())),

                    // A poisoned counter has no knowable width, so whether the
                    // function loops is unknowable too: absorb the check rather
                    // than cascade on top of the type's own error. The width is
                    // a placeholder, like every other poison substitution — the
                    // program has an error, so the gate stops it before codegen
                    // can read it.
                    None if counter_ty.is_never() => Ok(Self::ForWhile(function, Pow2Usize::ONE)),
                    _ => Err(Error::FunctionNotLoopable { name: name.clone() }).with_span(from),
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
    ) -> Result<Self, Diagnostic> {
        //let span = *from.as_ref();

        // Resolve each arm's declared type exactly once, poison-tolerantly. A
        // broken type in one arm must neither abort the match nor be reported
        // twice — once for the scrutinee's composite type and once for the arm.
        let left = from
            .left()
            .pattern()
            .as_typed_pattern()
            .map(|(pat, aliased)| (pat, scope.resolve_or_poison(aliased, *from.left().span())));
        let right = from
            .right()
            .pattern()
            .as_typed_pattern()
            .map(|(pat, aliased)| (pat, scope.resolve_or_poison(aliased, *from.right().span())));

        // Rebuild the scrutinee's type from the arms, mirroring
        // `parse::Match::scrutinee_type` but over the resolved parts.
        let scrutinee_ty = match (from.left().pattern(), from.right().pattern()) {
            (MatchPattern::Left(..), MatchPattern::Right(..)) => {
                let (_, ty_l) = left.as_ref().expect("left arm binds a type");
                let (_, ty_r) = right.as_ref().expect("right arm binds a type");
                ResolvedType::either(ty_l.clone(), ty_r.clone())
            }
            (MatchPattern::None, MatchPattern::Some(..)) => {
                let (_, ty_r) = right.as_ref().expect("some arm binds a type");
                ResolvedType::option(ty_r.clone())
            }
            (MatchPattern::False, MatchPattern::True) => ResolvedType::boolean(),
            _ => unreachable!("Match expressions have valid left and right arms"),
        };

        // A poisoned scrutinee must not suppress the arm-body errors.
        let scrutinee = Arc::new(analyze_child(from.scrutinee(), &scrutinee_ty, scope));

        let guard = scope.block();
        if let Some((pat_l, ty_l)) = &left {
            let typed_variables = bind_pattern(pat_l, ty_l, guard.scope, *from.left().span());
            for (identifier, ty) in typed_variables {
                guard.scope.insert_variable(identifier, ty);
            }
        }

        let ast_l = Arc::new(analyze_child(from.left().expression(), ty, guard.scope));
        drop(guard);

        let guard = scope.block();
        if let Some((pat_r, ty_r)) = &right {
            let typed_variables = bind_pattern(pat_r, ty_r, guard.scope, *from.right().span());

            for (identifier, ty) in typed_variables {
                guard.scope.insert_variable(identifier, ty);
            }
        }
        let ast_r = Arc::new(analyze_child(from.right().expression(), ty, guard.scope));

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
        let mut scope = Scope::new(Box::new(ElementsJetHinter), Vec::new());

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
        let program = analyzed(source);

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
        let program = analyzed(source);

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
pub(super) fn analyze_multifile(files: Vec<(&str, &str)>) -> Result<(), DiagnosticManager> {
    use crate::driver::tests::setup_graph;

    let (graph, _ids, _dir, mut diagnostics) = setup_graph(files);

    let Some(driver_program) = graph.linearize_and_assemble(&mut diagnostics) else {
        return Err(diagnostics);
    };

    if diagnostics.has_errors() {
        return Err(diagnostics);
    }

    if Program::analyze(
        &driver_program,
        Box::new(ElementsJetHinter),
        &mut diagnostics,
    )
    .is_none()
    {
        return Err(diagnostics);
    }

    Ok(())
}

/// All diagnostics for a multi-file program, empty if it compiled.
///
/// The sink is the source of truth for whether a program is correct, so tests
/// assert on it directly rather than on a `Result`: no `expect_err` to reach
/// the diagnostics, and a passing program is simply an empty manager.
#[cfg(test)]
pub(super) fn errors_multifile(files: Vec<(&str, &str)>) -> DiagnosticManager {
    analyze_multifile(files).err().unwrap_or_default()
}

/// All diagnostics for a single-file program, empty if it compiled.
#[cfg(test)]
pub(super) fn errors(src: &str) -> DiagnosticManager {
    errors_multifile(vec![("main.simf", src)])
}

/// The analyzed AST of a single-file program that is expected to compile.
///
/// Goes through the in-memory parse/analyze path rather than the driver, so
/// spans stay relative to `src`: the driver flattens each file into a
/// `mod unit_N` block, which shifts every offset.
#[cfg(test)]
pub(super) fn analyzed(src: &str) -> Program {
    use crate::parse::ParseFromStr;

    let parsed = parse::Program::parse_from_str(src).expect("program parses");
    let mut diagnostics = DiagnosticManager::new();
    let program = Program::analyze(&parsed, Box::new(ElementsJetHinter), &mut diagnostics);

    assert!(
        !diagnostics.has_errors(),
        "program must analyze:\n{diagnostics}"
    );
    program.expect("analysis yields a program when it reports no errors")
}

#[cfg(test)]
mod scope_resolution_tests {
    use super::analyze_multifile;

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

        let err = result
            .expect_err("Private imports should not be accessible")
            .to_string();
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

        let err = result
            .expect_err("Public main should be rejected")
            .to_string();
        assert!(err.contains("Main") && err.contains("public"));
    }

    #[test]
    fn test_aliasing_to_main_is_forbidden() {
        let result = analyze_multifile(vec![
            ("libs/lib/A.simf", "pub type bar = u32;"),
            ("main.simf", "use lib::A::bar as main; fn main() {}"),
        ]);

        let err = result
            .expect_err("Aliasing to main should be rejected")
            .to_string();
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

        let err = result
            .expect_err("Using the original unaliased name 'foo' should fail")
            .to_string();
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

        let err = result
            .expect_err("Aliasing a private item should fail")
            .to_string();
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

        let err = result
            .expect_err("Private intermediate aliases should block resolution")
            .to_string();
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

        let err = result
            .expect_err("Duplicate names in scope should fail")
            .to_string();
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

        let err = result
            .expect_err("Alias reusing a local name should fail")
            .to_string();
        assert!(err.contains("foo") && err.contains("multiple times"));
    }

    #[test]
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

        let err = result
            .expect_err("Duplicate function import should fail")
            .to_string();

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

        let err = result
            .expect_err("Build should fail on the unresolved import")
            .to_string();

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

        let err = result
            .expect_err("Build should fail when a local definition reuses an alias name")
            .to_string();
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

        let err = result
            .expect_err("Build should fail when a local definition reuses an alias name")
            .to_string();
        assert!(err.contains("foo") && err.contains("multiple times"));
    }
}

#[cfg(test)]
mod module_tests {
    use super::analyze_multifile;

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

        let err = result
            .expect_err("Private inner module must block access")
            .to_string();
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

        let err = result
            .expect_err("Duplicate mod blocks must fail")
            .to_string();
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

        let err = result
            .expect_err("Private inline items must remain hidden from siblings")
            .to_string();
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

        let err = result
            .expect_err("The root file scope must respect inline module privacy")
            .to_string();
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
    use crate::{TemplateProgram, UnstableFeatures};

    fn analyze(src: &str) -> Result<(), String> {
        TemplateProgram::new_with_unstable(
            src,
            &UnstableFeatures::all(),
            Box::new(ElementsJetHinter::new()),
        )
        .map(|_| ())
        .map_err(|diag| diag.to_string())
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
        use super::analyze_multifile;

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

        let err = result
            .expect_err("enums in dependency files must be rejected")
            .to_string();
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
        let result = TemplateProgram::new_with_unstable(
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
        let result = TemplateProgram::new_with_unstable(
            "enum Color { Red, Green }\nfn main() {}",
            &UnstableFeatures::none(),
            Box::new(ElementsJetHinter::new()),
        );
        assert!(result.is_err(), "enum syntax is gated behind -Z enums");
    }
}

#[cfg(test)]
mod multi_error_tests {
    use super::*;

    use crate::parse::{self, ParseFromStr};
    use crate::types::{ResolvedType, TypeConstructible};

    /// Analyze a syntactically valid expression against `ty` as a constant.
    fn analyze_at(src: &str, ty: &ResolvedType) -> bool {
        let expr = parse::Expression::parse_from_str(src).expect("valid syntax");
        Expression::analyze_const(&expr, ty).is_ok()
    }

    #[test]
    fn two_undefined_vars_in_separate_statements_both_report() {
        let src = "fn main() {
            let p: u32 = missing_a;
            let q: u32 = missing_b;
        }";

        let diags = errors(src);
        assert_eq!(2, diags.error_count());

        let r = diags.to_string();
        assert!(r.contains("missing_a") && r.contains("missing_b"), "{r}");
    }

    #[test]
    fn later_statements_analyzed_after_an_earlier_failure() {
        // The bool/u32 mismatch after the undefined var proves analysis continued.
        let src = "fn main() {
            let p: u32 = missing_a;
            assert!(jet::eq_32(true, 28));
        }";
        assert!(errors(src).error_count() >= 2);
    }

    #[test]
    fn two_broken_functions_both_report() {
        let src = "fn f() -> u32 { missing_a }
                   fn g() -> u32 { missing_b }
                   fn main() { }";
        assert_eq!(2, errors(src).error_count());
    }

    #[test]
    fn broken_function_does_not_hide_error_in_main() {
        let src = "fn f() -> u32 { missing_a }
                   fn main() { let q: u32 = missing_b; }";
        assert_eq!(2, errors(src).error_count());
    }

    #[test]
    fn broken_items_inside_module_all_surface() {
        let src = "mod m {
                       pub fn f() -> u32 { missing_a }
                       pub fn g() -> u32 { missing_b }
                   }
                   fn main() { }";
        assert_eq!(2, errors(src).error_count());
    }

    #[test]
    fn broken_items_inside_tuple_all_surface() {
        let src = "fn main() {
    let pair: (u32, u32) = (missing_a, missing_b);
}";
        assert_eq!(2, errors(src).error_count());
    }

    #[test]
    fn cascading_error_with_function() {
        let src = "fn f() -> u32 { missing }
fn main() {
    let x: u32 = f();
}";
        assert_eq!(1, errors(src).error_count());
    }

    #[test]
    fn duplicate_main_detected_when_first_body_failed() {
        // Even though the first main's body fails, it stays a Function::Main (poison
        // body), so the duplicate is still caught.
        let src = "fn main() { missing_tail } fn main() {}";
        let diags = errors(src);
        assert_eq!(2, diags.error_count());
        assert!(
            diags
                .diagnostics()
                .iter()
                .any(|d| matches!(d.error(), Error::FunctionRedefined { .. })),
            "duplicate main must be reported despite the first main's broken body"
        );
    }

    #[test]
    fn failed_main_body_does_not_trigger_main_required() {
        // Broken main body must report ONLY the body error, not also "Main required":
        // main is preserved with a poison body, so extract_single_main still finds it.
        let src = "fn main() { missing_tail }";
        assert_eq!(1, errors(src).error_count());
    }

    #[test]
    fn failed_assigment_does_not_trigger_undefined_variable() {
        let src = "fn main() {
    let x: u32 = missing_value;
    let y: u32 = x;
}";
        assert_eq!(1, errors(src).error_count());
    }

    #[test]
    fn failed_return_type_registers_poison_function() {
        // `Missing` (undefined return type) + `missing_body` = 2 errors.
        // `f` still registers with a poison return type, so `f()` in main does
        // NOT cascade into "function f is not defined".
        let src = "fn f() -> Missing { missing_body }
                fn main() { let x: u32 = f(); }";
        assert_eq!(2, errors(src).error_count());
    }

    #[test]
    fn bad_annotation_still_analyzes_rhs() {
        // The annotation resolves to ResolvedType::never(); the RHS is still
        // analyzed, so both the bad type and the undefined value are reported.
        let src = "fn main() { let x: Missing = missing_value; }";
        assert_eq!(2, errors(src).error_count());
    }

    #[test]
    fn undefined_function_still_reports_arg() {
        // The unknown callee must not suppress the argument error: the supplied
        // arg is analyzed against a poison type, so `missing_arg` still surfaces.
        let src = "fn main() { missing_fn(missing_arg); }";
        assert_eq!(2, errors(src).error_count());
    }

    #[test]
    fn both_match_arms_report_independent_errors() {
        // An error in the left arm must not suppress the right arm.
        let src = "fn main() {
            let r: u32 = match false {
                false => missing_a,
                true => missing_b,
            };
        }";
        assert_eq!(2, errors(src).error_count());
    }

    #[test]
    fn undefined_scrutinee_still_analyzes_both_arms() {
        // A poisoned scrutinee must not hide the arm-body errors.
        let src = "fn main() {
            let r: u32 = match missing_scrutinee {
                false => missing_a,
                true => missing_b,
            };
        }";
        assert_eq!(3, errors(src).error_count());
    }

    #[test]
    fn poison_expected_type_absorbs_literals_and_containers() {
        // Without the is_error() guards each of these emits ExpressionUnexpectedType.
        let err = ResolvedType::never();
        for src in ["5", "0x00", "(1, 2)", "[1, 2, 3]", "Some(1)"] {
            assert!(analyze_at(src, &err), "poison type should absorb `{src}`");
        }
    }

    #[test]
    fn poison_type_absorbs_the_cast_validity_check() {
        // `StructuralType` has no representation for poison and panics on it by
        // design, so a cast must not compare structures when either side is
        // poisoned at any depth — each of these used to abort the compiler.
        for src in [
            "fn main() { let x: Missing = <u16>::into(5); }",
            "type Broken = Missing;
             fn main() { let x: u32 = <Broken>::into(5); }",
            "type Broken = Missing;
             fn main() { let x: Broken = <Broken>::into(5); }",
        ] {
            // One root cause: the undefined alias, with no cast error piled on.
            assert_eq!(1, errors(src).error_count(), "{src}");
        }
    }

    #[test]
    fn error_unifies_with_anything_but_reals_stay_structural() {
        let err = ResolvedType::never();
        let u32 = ResolvedType::parse_from_str("u32").unwrap();
        let u16 = ResolvedType::parse_from_str("u16").unwrap();

        // poison unifies both directions
        assert!(err.compatible(&u32) && u32.compatible(&err) && err.compatible(&err));
        // reals stay structural
        assert!(u32.compatible(&u32));
        assert!(!u32.compatible(&u16));

        // nested: (u32, error) ~ (u32, u32), but (u32, u32) !~ (u32, u16)
        let t_err = ResolvedType::tuple([u32.clone(), err]);
        let t_u32 = ResolvedType::tuple([u32.clone(), u32.clone()]);
        let t_u16 = ResolvedType::tuple([u32.clone(), u16]);
        assert!(t_err.compatible(&t_u32));
        assert!(!t_u32.compatible(&t_u16));

        // arity still enforced under compatibility
        let t3 = ResolvedType::tuple([u32.clone(), u32.clone(), u32]);
        assert!(!t_u32.compatible(&t3));
    }
}

#[cfg(test)]
mod known_collection_gaps {
    use super::*;
    // The gaps fall into three families:
    //
    // * P1/P4 — a failed *registration* removes a name from scope (or an
    //   artifact from the program), so every later use cascades.
    // * P2/P3 — a *container-level* check (arity, output type, shape)
    //   returns before its children are analyzed, so their independent
    //   errors never surface.
    // * P5 — *binding recovery* discards the declared identifiers, so every
    //   later use of them cascades.

    /// Is any diagnostic of the kind matched by `pred`?
    fn reports(diags: &DiagnosticManager, pred: impl Fn(&Error) -> bool) -> bool {
        diags.diagnostics().iter().any(|d| pred(d.error()))
    }

    /// The undefined variables reported, in report order.
    fn undefined_vars(diags: &DiagnosticManager) -> Vec<String> {
        diags
            .diagnostics()
            .iter()
            .filter_map(|d| match d.error() {
                Error::UndefinedVariable { identifier } => Some(identifier.to_string()),
                _ => None,
            })
            .collect()
    }

    /// The undefined type aliases reported, in report order.
    fn undefined_aliases(diags: &DiagnosticManager) -> Vec<String> {
        diags
            .diagnostics()
            .iter()
            .filter_map(|d| match d.error() {
                Error::UndefinedAlias { name } => Some(name.to_string()),
                _ => None,
            })
            .collect()
    }

    // P1: an invalid `main` signature must not erase the declaration

    #[test]
    fn public_main_reports_only_the_visibility_error() {
        let diags = errors("pub fn main() {}");
        assert!(
            !reports(&diags, |e| matches!(e, Error::MainRequired)),
            "main exists, it is merely public: {diags}"
        );
        assert_eq!(1, diags.error_count());
    }

    #[test]
    fn main_with_inputs_reports_only_the_signature_error() {
        let diags = errors("fn main(x: u32) {}");
        assert!(
            !reports(&diags, |e| matches!(e, Error::MainRequired)),
            "{diags}"
        );
        assert_eq!(1, diags.error_count());
    }

    #[test]
    fn main_with_output_reports_only_the_signature_error() {
        // The body is still checked against unit, so a second error is fine
        // here — but it must not be "main required".
        let diags = errors("fn main() -> u32 { 1 }");
        assert!(
            reports(&diags, |e| matches!(e, Error::MainNoOutput)),
            "{diags}"
        );
        assert!(
            !reports(&diags, |e| matches!(e, Error::MainRequired)),
            "{diags}"
        );
    }

    #[test]
    fn public_main_still_analyzes_its_body() {
        // A poisoned Function::Main keeps the body reachable, exactly as a
        // failed body already does (see failed_main_body_does_not_trigger_main_required).
        let diags = errors("pub fn main() { missing_body }");
        assert!(
            reports(&diags, |e| matches!(e, Error::MainCannotBePublic)),
            "{diags}"
        );
        assert_eq!(["missing_body"][..], undefined_vars(&diags)[..]);
        assert!(
            !reports(&diags, |e| matches!(e, Error::MainRequired)),
            "{diags}"
        );
    }

    #[test]
    fn public_main_does_not_hide_a_duplicate_main() {
        let diags = errors("pub fn main() {}\nfn main() {}");
        assert!(
            reports(&diags, |e| matches!(e, Error::MainCannotBePublic)),
            "{diags}"
        );
        assert!(
            reports(&diags, |e| matches!(e, Error::FunctionRedefined { .. })),
            "the second main must still be caught: {diags}"
        );
    }

    // P2: a known callee's checks must not suppress argument errors

    #[test]
    fn call_output_mismatch_still_reports_argument_errors() {
        let diags = errors(
            "fn f(x: u32) -> u32 { x }
             fn main() { let y: u16 = f(missing_arg); }",
        );
        assert_eq!(["missing_arg"][..], undefined_vars(&diags)[..]);
        assert_eq!(2, diags.error_count());
    }

    #[test]
    fn call_arity_mismatch_still_reports_every_argument_error() {
        // Surplus arguments have no expected type, so they must be analyzed
        // against error() — dropping them loses missing_b.
        let diags = errors(
            "fn f(x: u32) -> u32 { x }
             fn main() { let y: u32 = f(missing_a, missing_b); }",
        );
        assert_eq!(["missing_a", "missing_b"][..], undefined_vars(&diags)[..]);
        assert_eq!(3, diags.error_count());
    }

    #[test]
    fn jet_arity_mismatch_still_reports_argument_errors() {
        let diags = errors("fn main() { assert!(jet::eq_32(missing_a)); }");
        assert_eq!(["missing_a"][..], undefined_vars(&diags)[..]);
        assert_eq!(2, diags.error_count());
    }

    #[test]
    fn invalid_cast_still_reports_argument_errors() {
        let diags = errors("fn main() { let x: u32 = <u16>::into(missing_a); }");
        assert_eq!(["missing_a"][..], undefined_vars(&diags)[..]);
        assert_eq!(2, diags.error_count());
    }

    #[test]
    fn tuple_arity_mismatch_still_reports_element_errors() {
        let diags = errors("fn main() { let t: (u32, u32) = (missing_a, missing_b, missing_c); }");
        assert_eq!(
            ["missing_a", "missing_b", "missing_c"][..],
            undefined_vars(&diags)[..]
        );
    }

    #[test]
    fn tuple_against_non_tuple_type_still_reports_element_errors() {
        // The elements have no expected type, so they must be analyzed
        // against error() rather than skipped.
        let diags = errors("fn main() { let t: u32 = (missing_a, missing_b); }");
        assert_eq!(["missing_a", "missing_b"][..], undefined_vars(&diags)[..]);
    }

    #[test]
    fn array_size_mismatch_still_reports_element_errors() {
        let diags = errors("fn main() { let a: [u32; 2] = [missing_a, missing_b, missing_c]; }");
        assert_eq!(
            ["missing_a", "missing_b", "missing_c"][..],
            undefined_vars(&diags)[..]
        );
    }

    #[test]
    fn list_bound_mismatch_still_reports_element_errors() {
        let diags =
            errors("fn main() { let a: List<u32, 2> = list![missing_a, missing_b, missing_c]; }");
        assert_eq!(
            ["missing_a", "missing_b", "missing_c"][..],
            undefined_vars(&diags)[..]
        );
    }

    #[test]
    fn enum_construction_arity_mismatch_still_reports_payload_errors() {
        let diags = errors(
            "enum E { V(u32) }
             fn main() { let x: E = E::V(missing_a, missing_b); }",
        );
        assert_eq!(["missing_a", "missing_b"][..], undefined_vars(&diags)[..]);
    }

    #[test]
    fn non_exhaustive_enum_match_still_reports_arm_body_errors() {
        let diags = errors(
            "enum E { A, B }
             fn main() { let r: u32 = match witness::W { E::A => missing_a, }; }",
        );
        assert_eq!(["missing_a"][..], undefined_vars(&diags)[..]);
        assert_eq!(2, diags.error_count());
    }

    #[test]
    fn duplicate_enum_match_arm_still_reports_arm_body_errors() {
        let diags = errors(
            "enum E { A, B }
             fn main() {
                 let r: u32 = match witness::W {
                     E::A => missing_a,
                     E::A => missing_b,
                     E::B => missing_c,
                 };
             }",
        );
        assert_eq!(
            ["missing_a", "missing_b", "missing_c"][..],
            undefined_vars(&diags)[..]
        );
    }

    #[test]
    fn unknown_enum_match_variant_still_reports_arm_body_errors() {
        let diags = errors(
            "enum E { A, B }
             fn main() {
                 let r: u32 = match witness::W { E::A => missing_a, E::Zzz => missing_b, };
             }",
        );
        assert_eq!(["missing_a", "missing_b"][..], undefined_vars(&diags)[..]);
    }

    // P3: type resolution must not abort a whole match

    #[test]
    fn broken_arm_types_do_not_abort_the_match() {
        let diags = errors(
            "fn main() {
                 let r: u32 = match witness::W {
                     Left(a: Missing) => missing_a,
                     Right(b: MissingTwo) => missing_b,
                 };
             }",
        );
        assert_eq!(["Missing", "MissingTwo"][..], undefined_aliases(&diags)[..]);
        assert_eq!(["missing_a", "missing_b"][..], undefined_vars(&diags)[..]);
        assert_eq!(4, diags.error_count());
    }

    #[test]
    fn broken_right_arm_type_does_not_hide_the_left_arm_body() {
        let diags = errors(
            "fn main() {
                 let r: u32 = match witness::W {
                     Left(a: u32) => missing_a,
                     Right(b: MissingTwo) => missing_b,
                 };
             }",
        );
        assert_eq!(["missing_a", "missing_b"][..], undefined_vars(&diags)[..]);
        assert_eq!(3, diags.error_count());
    }

    #[test]
    fn arm_pattern_shape_mismatch_does_not_abort_the_match() {
        let diags = errors(
            "fn main() {
                 let r: u32 = match witness::W {
                     Left((a, b): u32) => missing_a,
                     Right(c: u32) => missing_b,
                 };
             }",
        );
        assert_eq!(["missing_a", "missing_b"][..], undefined_vars(&diags)[..]);
    }

    #[test]
    fn every_broken_enum_arm_binding_type_reports() {
        let diags = errors(
            "enum E { V(u32, u32) }
             fn main() { let r: u32 = match witness::W { E::V(x: Missing, y: MissingTwo) => 1, }; }",
        );
        assert_eq!(["Missing", "MissingTwo"][..], undefined_aliases(&diags)[..]);
    }

    // P4: a failed registration must still leave a poisoned name

    #[test]
    fn broken_type_alias_does_not_cascade() {
        let diags = errors(
            "type Broken = Missing;
             fn main() { let x: Broken = 5; }",
        );
        assert_eq!(["Missing"][..], undefined_aliases(&diags)[..]);
        assert_eq!(1, diags.error_count());
    }

    #[test]
    fn broken_type_alias_does_not_cascade_per_use_site() {
        let diags = errors(
            "type Broken = Missing;
             fn f() -> Broken { 5 }
             fn main() { let x: Broken = 5; }",
        );
        assert_eq!(1, diags.error_count(), "{diags}");
    }

    #[test]
    fn enum_with_duplicate_variant_still_registers_its_name() {
        let diags = errors(
            "enum E { A, A }
             fn main() { let x: E = witness::W; }",
        );
        assert!(undefined_aliases(&diags).is_empty(), "{diags}");
        assert_eq!(1, diags.error_count());
    }

    #[test]
    fn empty_enum_still_registers_its_name() {
        let diags = errors(
            "enum E { }
             fn main() { let x: E = witness::W; }",
        );
        assert!(undefined_aliases(&diags).is_empty(), "{diags}");
        assert_eq!(1, diags.error_count());
    }

    #[test]
    fn redefined_module_still_analyzes_its_items() {
        let diags = errors(
            "mod m { pub fn a() -> u32 { missing_a } }
             mod m { pub fn b() -> u32 { missing_b } }
             fn main() {}",
        );
        assert_eq!(["missing_a", "missing_b"][..], undefined_vars(&diags)[..]);
        assert_eq!(3, diags.error_count());
    }

    // P5: binding recovery must retain the declared identifiers

    #[test]
    fn failed_assignment_pattern_keeps_its_bindings() {
        // The pattern does not fit the annotation; `a` and `b` are still
        // declared, so using them must not cascade.
        let diags = errors("fn main() { let (a, b): u32 = 5; assert!(jet::eq_32(a, b)); }");
        assert!(undefined_vars(&diags).is_empty(), "{diags}");
        assert_eq!(1, diags.error_count());
    }

    #[test]
    fn failed_enum_arm_binding_keeps_its_bindings() {
        let diags = errors(
            "enum E { V(u32) }
             fn main() { let r: u32 = match witness::W { E::V(x: u16) => x, }; }",
        );
        assert!(undefined_vars(&diags).is_empty(), "{diags}");
        assert_eq!(1, diags.error_count());
    }

    /// The unresolved import names reported, in report order.
    fn unresolved_items(diags: &DiagnosticManager) -> Vec<String> {
        diags
            .diagnostics()
            .iter()
            .filter_map(|d| match d.error() {
                Error::UnresolvedItem { name } => Some(name.clone()),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn single_child_shape_mismatch_still_reports_the_child() {
        // `Left`, `Right` and `Some` wrap exactly one child. The child has its
        // own errors whether or not the annotation is the right shape, so the
        // mismatch must be reported and the child analyzed against poison.
        for src in [
            "fn main() { let x: u32 = Left(missing_child); }",
            "fn main() { let x: u32 = Right(missing_child); }",
            "fn main() { let x: u32 = Some(missing_child); }",
        ] {
            let diags = errors(src);
            assert_eq!(["missing_child"][..], undefined_vars(&diags)[..], "{src}");
            assert_eq!(2, diags.error_count(), "{src}");
        }
    }

    #[test]
    fn poison_expected_type_still_reports_enum_payload_errors() {
        // The payload is analyzed at poison, like every other container's
        // children, rather than skipped wholesale.
        let diags = errors(
            "enum E { V(u32) }
            fn main() { let x: Missing = E::V(missing_child); }",
        );
        assert_eq!(["missing_child"][..], undefined_vars(&diags)[..]);
        assert_eq!(2, diags.error_count());
    }

    #[test]
    fn multi_item_import_reports_every_unresolved_item() {
        // The items of one `use` are independent: `b` failing tells you nothing
        // about `a`, so both must be reported.
        let diags = errors(
            "mod m {}
            use crate::m::{a, b};
            fn main() {}",
        );
        assert_eq!(["a", "b"][..], unresolved_items(&diags)[..]);
    }

    #[test]
    fn generic_call_type_reports_every_undefined_alias() {
        // The type argument of a builtin resolves like any other type, so two
        // broken aliases in it report twice, not once.
        for src in [
            "fn main() { let x: bool = is_none::<Either<Missing, MissingTwo>>(missing_arg); }",
            "fn main() { let x: u32 = unwrap_left::<Either<Missing, MissingTwo>>(missing_arg); }",
            "fn main() { let x: u32 = <(Missing, MissingTwo)>::into(missing_arg); }",
        ] {
            let diags = errors(src);
            assert_eq!(
                ["Missing", "MissingTwo"][..],
                undefined_aliases(&diags)[..],
                "{src}"
            );
        }
    }

    #[test]
    fn poisoned_fold_signature_does_not_cascade_into_not_foldable() {
        // Whether the signature folds is unknowable until its types resolve, so
        // a poisoned one must absorb the check rather than fail it.
        for src in [
            "fn step(e: u32, acc: Missing) -> u32 { 0 }
            fn main() { let r: u32 = array_fold::<step, 2>([1, 2], 0); }",
            "fn step(e: u32, acc: u32) -> Missing { 0 }
            fn main() { let r: u32 = array_fold::<step, 2>([1, 2], 0); }",
        ] {
            let diags = errors(src);
            assert!(
                !reports(&diags, |e| matches!(e, Error::FunctionNotFoldable { .. })),
                "the undefined alias is the only root cause: {diags}"
            );
            assert_eq!(["Missing"][..], undefined_aliases(&diags)[..], "{src}");
        }
    }

    #[test]
    fn redefined_alias_still_reports_errors_in_the_rejected_body() {
        // The rejected body is independent of the name collision: resolve it for
        // its own diagnostics, without replacing the existing binding.
        let diags = errors(
            "type A = u32;
            type A = Missing;
            fn main() {}",
        );
        assert!(reports(&diags, |e| matches!(
            e,
            Error::RedefinedAlias { .. }
        )));
        assert_eq!(["Missing"][..], undefined_aliases(&diags)[..]);
        assert_eq!(2, diags.error_count());
    }

    #[test]
    fn every_rejected_registration_still_reports_its_own_errors() {
        // `insert_alias` is the only registration that resolves anything itself,
        // so it is the only one whose collision check could swallow an inner
        // error (see the test above). The rest take values their caller already
        // analyzed and reported on, which is what keeps these cases honest —
        // moving that work inside a registration would silently regress them.
        for (src, inner) in [
            // enum: the payload types are resolved before `insert_enum`
            (
                "enum E { A }\nenum E { B(Missing) }\nfn main() {}",
                "Missing",
            ),
            // ...including when the collision is with a plain alias
            (
                "type E = u32;\nenum E { B(Missing) }\nfn main() {}",
                "Missing",
            ),
            // function: params, return type and body precede `insert_function`
            ("fn f() {}\nfn f(x: Missing) {}\nfn main() {}", "Missing"),
            (
                "fn f() {}\nfn f() -> Missing { 1 }\nfn main() {}",
                "Missing",
            ),
        ] {
            let diags = errors(src);
            assert_eq!([inner][..], undefined_aliases(&diags)[..], "{src}");
            assert_eq!(2, diags.error_count(), "{src}");
        }
    }

    #[test]
    fn rejected_function_body_errors_still_report() {
        // The body case, which has no alias to count: the duplicate must not
        // swallow the undefined variable inside the rejected definition.
        let diags = errors(
            "fn f() {}
            fn f() -> u32 { missing_body }
            fn main() {}",
        );
        assert!(reports(&diags, |e| matches!(
            e,
            Error::FunctionRedefined { .. }
        )));
        assert_eq!(["missing_body"][..], undefined_vars(&diags)[..]);
    }

    #[test]
    fn surplus_enum_arm_bindings_do_not_cascade_into_a_shape_error() {
        // Binding two names to a one-value payload is one mistake. The arity
        // diagnostic says so; re-checking the combined pattern against the
        // payload type only restates it.
        let diags = errors(
            "enum E { V(u32) }
            fn main() { let r: u32 = match witness::W { E::V(x: u32, y: u32) => 1, }; }",
        );
        assert!(
            !reports(&diags, |e| matches!(
                e,
                Error::ExpressionUnexpectedType { .. }
            )),
            "the arity error already says it: {diags}"
        );
        assert_eq!(1, diags.error_count());
    }

    /// How many diagnostics carry a [`Error::Grammar`] message?
    ///
    /// Grammar errors are distinguished only by their text, so counting them is
    /// the robust way to assert that several independent ones surfaced.
    fn grammar_count(diags: &DiagnosticManager) -> usize {
        diags
            .diagnostics()
            .iter()
            .filter(|d| matches!(d.error(), Error::Grammar { .. }))
            .count()
    }

    #[test]
    fn aliasing_an_item_to_main_does_not_abort_its_siblings() {
        // A: the items of one `use` are independent, so a rejected alias must
        // not swallow the item beside it.
        let diags = errors(
            "mod m { pub fn a() {} }
            use crate::m::{a as main, missing};
            fn main() {}",
        );
        assert!(
            reports(&diags, |e| matches!(e, Error::MainCannotBeAlias)),
            "{diags}"
        );
        assert_eq!(["missing"][..], unresolved_items(&diags)[..]);
    }

    #[test]
    fn every_malformed_enum_match_arm_reports() {
        // A: the arm loop must not stop at the first unknown variant; `Y` is a
        // separate mistake from `X`.
        let diags = errors(
            "enum E { A, B }
            fn main() { let r: u32 = match witness::W { E::X => 1, E::Y => 2, }; }",
        );
        assert_eq!(
            2,
            grammar_count(&diags),
            "both unknown variants must report: {diags}"
        );
    }

    #[test]
    fn unknown_arm_does_not_suppress_the_scrutinee_type_error() {
        // The enum resolved, so the scrutinee's type is knowable and its
        // mismatch is independent of the arm naming a variant that does not exist.
        let diags = errors(
            "enum E { A, B }
            fn main() {
                let v: u32 = witness::V;
                let r: u32 = match v { E::X => 1, E::A => 2, E::B => 3, };
            }",
        );
        assert_eq!(1, grammar_count(&diags), "unknown variant `X`: {diags}");
        assert!(
            reports(&diags, |e| matches!(
                e,
                Error::ExpressionTypeMismatch { .. } | Error::ExpressionUnexpectedType { .. }
            )),
            "matching a u32 against E is a type error of its own: {diags}"
        );
    }

    #[test]
    fn missing_arm_does_not_suppress_the_scrutinee_type_error() {
        let diags = errors(
            "enum E { A, B }
            fn main() {
                let v: u32 = witness::V;
                let r: u32 = match v { E::A => 1, };
            }",
        );
        assert_eq!(1, grammar_count(&diags), "missing variant `B`: {diags}");
        assert!(
            reports(&diags, |e| matches!(
                e,
                Error::ExpressionTypeMismatch { .. } | Error::ExpressionUnexpectedType { .. }
            )),
            "matching a u32 against E is a type error of its own: {diags}"
        );
    }

    #[test]
    fn unknown_arm_does_not_suppress_payload_checks_on_the_valid_arms() {
        // `E::A`'s binding is declared u16 against a u32 payload; the unknown
        // `E::Zzz` beside it says nothing about that.
        let diags = errors(
            "enum E { A(u32), B }
            fn main() { let r: u32 = match witness::W { E::A(x: u16) => 1, E::Zzz => 2, }; }",
        );
        assert_eq!(1, grammar_count(&diags), "unknown variant `Zzz`: {diags}");
        assert!(
            reports(&diags, |e| matches!(
                e,
                Error::ExpressionTypeMismatch { .. }
            )),
            "the u16/u32 payload mismatch must still report: {diags}"
        );
    }

    #[test]
    fn poisoned_enum_alias_does_not_cascade_into_not_an_enum() {
        // B: `E` resolves to poison, so whether it names an enum is unknowable.
        // Treating poison as a concrete non-enum invents a second error.
        let diags = errors(
            "type E = Missing;
            fn main() { let r: u32 = match witness::W { E::A => 1, }; }",
        );
        assert_eq!(["Missing"][..], undefined_aliases(&diags)[..]);
        assert_eq!(1, diags.error_count(), "{diags}");
    }

    #[test]
    fn poisoned_loop_counter_does_not_cascade_into_not_loopable() {
        // B: the counter's width is unknowable while its type is poisoned, so
        // loopability is unknowable too — absorb the check rather than fail it.
        let diags = errors(
            "fn step(acc: u32, ctx: (), i: Missing) -> Either<u32, u32> { Left(acc) }
            fn main() { let r: Either<u32, u32> = for_while::<step>(0, ()); }",
        );
        assert!(
            !reports(&diags, |e| matches!(e, Error::FunctionNotLoopable { .. })),
            "the undefined alias is the only root cause: {diags}"
        );
        assert_eq!(["Missing"][..], undefined_aliases(&diags)[..]);
    }

    #[test]
    fn reading_a_variable_does_not_rebind_it() {
        // C: reading `x` at a poisoned expected type must not replace the
        // declared `x: u32`. The second read is an independent mistake and has
        // to be caught against the *declaration*, not against the first read.
        let diags = errors(
            "fn f(x: u32) { let a: Missing = x; let b: u16 = x; }
            fn main() {}",
        );
        assert_eq!(["Missing"][..], undefined_aliases(&diags)[..]);
        assert!(
            reports(&diags, |e| matches!(
                e,
                Error::ExpressionTypeMismatch { .. }
            )),
            "the u32/u16 mismatch is independent of the bad annotation: {diags}"
        );
        assert_eq!(2, diags.error_count());
    }

    #[test]
    fn arity_recovery_still_validates_the_binding_pattern() {
        // D: the arity error explains the count, and nothing else. Skipping the
        // pattern check to suppress the shape cascade also drops the reuse of
        // `x`, which is an independent mistake.
        let diags = errors(
            "enum E { V(u32) }
            fn main() { let r: u32 = match witness::W { E::V(x: u32, x: u32) => 1, }; }",
        );
        assert!(
            reports(&diags, |e| matches!(
                e,
                Error::VariableReuseInPattern { .. }
            )),
            "reusing `x` is independent of the arity: {diags}"
        );
        assert_eq!(2, diags.error_count());
    }

    #[test]
    fn import_collision_in_one_namespace_is_not_masked_by_another() {
        // E: the alias `foo` imports cleanly, the function `foo` collides with a
        // local definition. Succeeding in one namespace must not report success
        // for all of them.
        let diags = errors(
            "mod m { pub type foo = u32; pub fn foo() {} }
            fn foo() {}
            use crate::m::foo;
            fn main() {}",
        );
        assert!(
            reports(&diags, |e| matches!(e, Error::RedefinedItem { .. })),
            "the duplicate function import must surface: {diags}"
        );
    }

    // P1, imports: a name a failed `use` was meant to introduce is poisoned, so
    // the cost of a broken import is one error rather than one per use.

    #[test]
    fn unresolved_module_does_not_cascade_into_every_call() {
        let diags = errors(
            "use crate::nope::foo;
            fn main() { foo(); foo(); foo(); foo(); foo(); }",
        );
        assert!(
            reports(&diags, |e| matches!(e, Error::ModuleNotFound { .. })),
            "{diags}"
        );
        assert_eq!(1, diags.error_count(), "{diags}");
    }

    #[test]
    fn unresolved_item_does_not_cascade_into_every_call() {
        let diags = errors(
            "mod m { pub fn f() {} }
            use crate::m::missing;
            fn main() { missing(); missing(); missing(); }",
        );
        assert!(
            reports(&diags, |e| matches!(e, Error::UnresolvedItem { .. })),
            "{diags}"
        );
        assert_eq!(1, diags.error_count(), "{diags}");
    }

    #[test]
    fn private_item_does_not_cascade_into_every_call() {
        let diags = errors(
            "mod m { fn f() -> u32 { 1 } }
            use crate::m::f;
            fn main() { let a: u32 = f(); let b: u32 = f(); let c: u32 = f(); }",
        );
        assert!(
            reports(&diags, |e| matches!(e, Error::PrivateItem { .. })),
            "{diags}"
        );
        assert_eq!(1, diags.error_count(), "{diags}");
    }

    #[test]
    fn a_real_module_does_not_disable_poison_in_other_namespaces() {
        // The poison covers the name in every namespace, so a same-named module
        // must not re-enable the function cascade the poison exists to absorb.
        let diags = errors(
            "mod m { fn f() -> u32 { 1 } }
            mod f {}
            use crate::m::f;
            fn main() { let a: u32 = f(); let b: u32 = f(); }",
        );
        assert!(
            !reports(&diags, |e| matches!(e, Error::FunctionUndefined { .. })),
            "the failed import must absorb the calls: {diags}"
        );
        assert_eq!(1, diags.error_count(), "{diags}");
    }

    #[test]
    fn broken_path_still_reports_the_main_alias() {
        // Aliasing to `main` is a property of the declaration, not of the target,
        // so navigation failing says nothing about it.
        let diags = errors("use crate::missing::{f as main, g}; fn main() {}");
        assert!(
            reports(&diags, |e| matches!(e, Error::ModuleNotFound { .. })),
            "{diags}"
        );
        assert!(
            reports(&diags, |e| matches!(e, Error::MainCannotBeAlias)),
            "the `as main` alias is rejected regardless of the path: {diags}"
        );
    }

    #[test]
    fn poisoned_parameter_use_does_not_mask_a_later_conflict() {
        // The first use poisons `param::P`; the second fixes it at u16. The
        // third is a real u16/u32 conflict and must not be absorbed.
        let diags = errors(
            "fn main() {
                let a: Missing = param::P;
                let b: u16 = param::P;
                let c: u32 = param::P;
            }",
        );
        assert_eq!(["Missing"][..], undefined_aliases(&diags)[..]);
        assert!(
            reports(&diags, |e| matches!(
                e,
                Error::ExpressionTypeMismatch { .. }
            )),
            "the u16/u32 conflict between the later uses must report: {diags}"
        );
    }

    #[test]
    fn tuple_arity_mismatch_still_reports_known_slot_types() {
        // The slots that line up keep their types, so `true` is still checked
        // against u32; only the surplus element has no expected type.
        let diags = errors("fn main() { let x: (u32, u32) = (true, 1, missing); }");
        assert_eq!(["missing"][..], undefined_vars(&diags)[..]);
        assert_eq!(
            3,
            diags.error_count(),
            "arity, the true/u32 mismatch, and the undefined variable: {diags}"
        );
    }

    #[test]
    fn pattern_shape_failure_still_reports_duplicate_bindings() {
        // `is_of_type` returns only its first error, so the shape mismatch would
        // otherwise hide the reuse behind it.
        let diags = errors("fn main() { let (x, x): u32 = 1; }");
        assert!(
            reports(&diags, |e| matches!(
                e,
                Error::VariableReuseInPattern { .. }
            )),
            "binding `x` twice is its own error: {diags}"
        );
        assert_eq!(2, diags.error_count(), "{diags}");
    }

    #[test]
    fn every_duplicate_enum_variant_reports() {
        let diags = errors("enum E { A, A, B, B } fn main() {}");
        assert_eq!(
            2,
            grammar_count(&diags),
            "both `A` and `B` are duplicated: {diags}"
        );
    }

    #[test]
    fn a_repeated_enum_variant_reports_once() {
        let diags = errors("enum E { A, A, A } fn main() {}");
        assert_eq!(
            1,
            grammar_count(&diags),
            "`A` is one duplicated name, however often it repeats: {diags}"
        );
    }

    #[test]
    fn failed_import_does_not_cascade_into_every_type_use() {
        // A `use` does not say which namespace the item lives in, so the name is
        // poisoned as a type as well as a function.
        let diags = errors(
            "mod m { pub fn f() {} }
            use crate::m::Missing;
            fn main() { let x: Missing = 5; let y: Missing = 6; }",
        );
        assert!(undefined_aliases(&diags).is_empty(), "{diags}");
        assert_eq!(1, diags.error_count(), "{diags}");
    }

    #[test]
    fn failed_import_inside_a_module_does_not_cascade() {
        let diags = errors(
            "mod a { pub fn f() {} }
            mod b { use crate::a::nope; pub fn g() { nope(); nope(); } }
            fn main() {}",
        );
        assert_eq!(1, diags.error_count(), "{diags}");
    }

    #[test]
    fn poisoned_import_absorbs_arity_and_output_checks() {
        // The signature is unknowable, so neither the argument count nor the
        // output type has an answer to check against.
        let diags = errors(
            "use crate::nope::foo;
            fn main() { let x: u32 = foo(1, 2, 3); }",
        );
        assert_eq!(1, diags.error_count(), "{diags}");
    }

    #[test]
    fn poisoned_import_still_reports_its_argument_errors() {
        // Absorbing the callee must not swallow the arguments' own errors.
        let diags = errors(
            "use crate::nope::foo;
            fn main() { foo(missing_a, missing_b); }",
        );
        assert_eq!(["missing_a", "missing_b"][..], undefined_vars(&diags)[..]);
        assert_eq!(3, diags.error_count(), "{diags}");
    }

    #[test]
    fn poisoned_import_does_not_cascade_into_not_foldable_or_not_loopable() {
        for src in [
            "use crate::nope::step;
            fn main() { let r: u32 = array_fold::<step, 2>([1, 2], 0); }",
            "use crate::nope::step;
            fn main() { let r: u32 = fold::<step, 2>(list![1, 2], 0); }",
            "use crate::nope::step;
            fn main() { let r: Either<u32, u32> = for_while::<step>(0, ()); }",
        ] {
            let diags = errors(src);
            assert!(
                !reports(&diags, |e| matches!(
                    e,
                    Error::FunctionNotFoldable { .. } | Error::FunctionNotLoopable { .. }
                )),
                "a poisoned signature has no shape to fail: {src}\n{diags}"
            );
            assert_eq!(1, diags.error_count(), "{src}\n{diags}");
        }
    }

    #[test]
    fn a_failed_import_still_reports_every_bad_item() {
        // Poisoning the names must not collapse the per-item collection.
        let diags = errors(
            "mod m { pub fn f() {} }
            use crate::m::{missing_x, missing_y};
            fn main() { missing_x(); missing_y(); }",
        );
        assert_eq!(2, diags.error_count(), "{diags}");
    }

    #[test]
    fn a_failed_import_does_not_poison_its_healthy_siblings() {
        let diags = errors(
            "mod m { pub fn a() -> u32 { 1 } pub fn b() -> u32 { 2 } }
            use crate::m::{a, nope, b};
            fn main() { let x: u32 = a(); let y: u32 = b(); nope(); }",
        );
        assert_eq!(1, diags.error_count(), "{diags}");
    }

    #[test]
    fn a_redefined_import_keeps_the_good_binding() {
        // The name is already bound to a real function, so it must not be
        // poisoned: a genuine mistake against that signature still reports.
        let diags = errors(
            "mod m { pub fn f(x: u32) -> u32 { x } }
            use crate::m::f;
            use crate::m::f;
            fn main() { let y: u32 = f(1, 2); }",
        );
        assert!(
            reports(&diags, |e| matches!(e, Error::RedefinedItem { .. })),
            "{diags}"
        );
        assert!(
            reports(&diags, |e| matches!(
                e,
                Error::InvalidNumberOfArguments { .. }
            )),
            "the real signature must still be checked: {diags}"
        );
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
