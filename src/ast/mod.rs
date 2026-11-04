mod analyze;
mod jet_hinter;
mod recovery;
mod scope;
#[cfg(test)]
mod tests;

use std::num::NonZeroUsize;
use std::sync::Arc;

use either::Either;
use miniscript::iter::{Tree, TreeLike};

use crate::compile::RawHashJets;
use crate::debug::{CallTracker, DebugSymbols};
use crate::error::Span;
use crate::impl_eq_hash;
use crate::jet::JetHL;
use crate::num::{NonZeroPow2Usize, Pow2Usize};
use crate::parse::MatchPattern;
use crate::pattern::Pattern;
use crate::str::Identifier;
use crate::types::{ResolvedType, TypeConstructible};
use crate::value::Value;
use crate::witness::{Parameters, WitnessTypes};
use crate::TemplateProgramWitness;

pub use self::jet_hinter::{CoreJetHinter, ElementsJetHinter, JetHinter};

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
    /// A constant declaration.
    ///
    /// A stub because the value was evaluated into scope during the
    /// creation of the AST.
    Const,
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
    /// SHA-256 of the concatenated bytes of a tuple of unsigned integers of the given type,
    /// using the given jets.
    RawHash(ResolvedType, RawHashJets),
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
            (Self::RawHash(a, b), Self::RawHash(c, d)) => a == c && b == d,
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
    /// Panics if the analysis of the body failed. This cannot happen for a function
    /// of an analyzed [`Program`], because a program with errors is never built.
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
