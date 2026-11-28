//! This module contains the parsing code to convert the
//! tokens into an AST.

#[cfg(feature = "arbitrary")]
mod arbitrary_impls;
mod display;
mod grammar;
#[cfg(feature = "fmt")]
mod lossless;
mod pipeline;
#[cfg(test)]
mod tests;

use std::num::NonZeroUsize;
use std::path::PathBuf;
use std::sync::Arc;

use either::Either;
use miniscript::iter::{Tree, TreeLike};

use crate::error::{Diagnostic, Error, Span};
use crate::impl_eq_hash;
use crate::num::NonZeroPow2Usize;
use crate::pattern::Pattern;
use crate::str::{
    AliasName, Binary, Decimal, FunctionName, Hexadecimal, Identifier, JetName, ModuleName,
    SymbolName,
};
use crate::types::{AliasedType, TypeConstructible};
use crate::unstable::{impl_require_feature, FeatureRequirement, RequireFeature, UnstableFeature};
use crate::TemplateProgramWitness;

pub use self::grammar::ChumskyParse;
#[cfg(feature = "fmt")]
pub use self::lossless::ParsedSource;
pub use self::pipeline::{ParseFromStr, ParseFromStrWithErrors};

/// A program is a sequence of items.
#[derive(Clone, Debug)]
pub struct Program {
    items: Arc<[Item]>,
    span: Span,
}

impl Program {
    // Need for driver usage
    pub(crate) fn new(items: &[Item], span: Span) -> Self {
        Self {
            items: Arc::from(items),
            span,
        }
    }

    /// Access the items of the program.
    pub fn items(&self) -> &[Item] {
        &self.items
    }
}

impl_eq_hash!(Program; items);

impl_require_feature!(Program { recurse: items; });

/// An item is a component of a program.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Item {
    /// A type alias.
    TypeAlias(TypeAlias),
    /// A function.
    Function(Function),
    /// An import declaration (e.g., `use math::add`) that brings another
    /// [`Item`] into the current scope.
    Use(UseDecl),
    /// An enum declaration.
    EnumDeclaration(EnumDeclaration),
    /// A constant declaration.
    Const(ConstDecl),
    /// A module containing a collection of nested [`Item`].
    Module(Module),
    /// A placeholder used exclusively for error recovery during parsing.
    ///
    /// When the parser encounters a syntax error, it skips the malformed tokens
    /// until it reaches a valid top-level keyword and inserts `Ignored` into the AST.
    Ignored,
}

impl Item {
    /// Access the source span when this item was parsed successfully.
    ///
    /// Error-recovery placeholders have no source node to decorate.
    pub fn span(&self) -> Option<&Span> {
        match self {
            Self::TypeAlias(alias) => Some(alias.span()),
            Self::Function(function) => Some(function.span()),
            Self::Use(use_decl) => Some(use_decl.span()),
            Self::EnumDeclaration(declaration) => Some(declaration.span()),
            Self::Const(decl) => Some(decl.span()),
            Self::Module(module) => Some(module.span()),
            Self::Ignored => None,
        }
    }
}

impl_require_feature!(Item {
    variants:
        TypeAlias(alias),
        Function(function),
        Use(use_decl),
        EnumDeclaration(decl),
        Const(decl),
        Module(module),
        Ignored,
});

#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum Visibility {
    Public,
    #[default]
    Private,
}

/// Represents an import declaration in the Abstract Syntax Tree.
///
/// This structure defines how items from other modules or files are brought into the
/// current scope. Note that in this architecture, the first identifier in the path
/// is always treated as an dependency root path name bound to a specific physical path.
///
/// # Example
/// ```text
/// pub use std::collections::{HashMap, HashSet};
/// ```
#[derive(Clone, Debug)]
pub struct UseDecl {
    /// The visibility of the import (e.g., `pub use` vs `use`).
    visibility: Visibility,

    /// The base path to the target file or module.
    ///
    /// The first element is always the registered dependency root path name for
    /// the import path. Subsequent elements represent nested modules or directories.
    path: Vec<Identifier>,

    /// The specific item or list of items being imported from the resolved path.
    items: UseItems,
    span: Span,
}

impl_require_feature!(UseDecl {
    requires: UnstableFeature::Imports, span: span;
    recurse: items;
});

impl_require_feature!(UseItems {
    variants:
        Single(_),
        List(_),
});

impl UseDecl {
    pub fn visibility(&self) -> &Visibility {
        &self.visibility
    }

    /// Returns the full logical module path as a vector of string slices.
    ///
    /// This includes the Dependency Root Path Name (the first segment)
    /// followed by all subsequent sub-module segments.
    pub fn path(&self) -> &[Identifier] {
        &self.path
    }

    pub fn items(&self) -> &UseItems {
        &self.items
    }

    pub fn span(&self) -> &Span {
        &self.span
    }

    pub fn str_path(&self) -> String {
        let path: PathBuf = self.path().iter().map(Identifier::as_str).collect();
        path.display().to_string()
    }

    /// Extracts the Dependency Root Path Name (the very first segment) from this path.
    ///
    /// # Errors
    ///
    /// Returns a `Diagnostic` if the use declaration path is completely empty.
    pub fn drp_name(&self) -> Result<&str, Diagnostic> {
        let parts: Vec<&str> = self.path().iter().map(Identifier::as_str).collect();
        parts.first().copied().ok_or_else(|| {
            Error::CannotParse {
                msg: "Empty use path".to_string(),
            }
            .with_span(self.span)
        })
    }

    pub(crate) fn set_path(&mut self, path: &[Identifier]) {
        self.path = Vec::from(path)
    }
}

// `span` are required because `UseDecl` hashing is context-dependent.
// For instance, identical `use crate::...` paths differ between binary and library roots.
// Tested by: `functional_tests::identical_crate_uses_in_different_package_roots_do_not_poison_resolution_cache`.
impl_eq_hash!(UseDecl; visibility, path, items, span);

/// Aliases the specific identifier of an imported type to a new, local identifier
pub type AliasedSymbolName = (SymbolName, Option<SymbolName>);

/// Specified the items being brought into scope at the end of a `use` declaration
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum UseItems {
    /// A single item import.
    ///
    /// # Example
    /// ```text
    /// use core::math::add;
    /// ```
    Single(AliasedSymbolName),

    /// A multiple item import grouped in a list.
    ///
    /// # Example
    /// ```text
    /// use core::math::{add, subtract};
    /// ```
    List(Vec<AliasedSymbolName>),
}

#[derive(Clone, Debug)]
pub struct Function {
    visibility: Visibility,
    name: FunctionName,
    params: Arc<[FunctionParam]>,
    ret: Option<AliasedType>,
    body: Expression,
    span: Span,
}

impl Function {
    pub fn visibility(&self) -> &Visibility {
        &self.visibility
    }

    /// Access the name of the function.
    pub fn name(&self) -> &FunctionName {
        &self.name
    }

    /// Access the parameters of the function.
    pub fn params(&self) -> &[FunctionParam] {
        &self.params
    }

    /// Access the return type of the function.
    ///
    /// An empty return type means that the function returns the unit value.
    pub fn ret(&self) -> Option<&AliasedType> {
        self.ret.as_ref()
    }

    /// Access the body of the function.
    pub fn body(&self) -> &Expression {
        &self.body
    }

    /// Access the span of the function.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(Function; visibility, name, params, ret, body);

impl_require_feature!(Function { recurse: params, ret, body; });

/// Parameter of a function.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct FunctionParam {
    identifier: Identifier,
    ty: AliasedType,
    span: Span,
}

impl FunctionParam {
    /// Access the identifier of the parameter.
    pub fn identifier(&self) -> &Identifier {
        &self.identifier
    }

    /// Access the type of the parameter.
    pub fn ty(&self) -> &AliasedType {
        &self.ty
    }

    /// Access the source span of the complete parameter.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(FunctionParam; identifier, ty);

impl_require_feature!(FunctionParam { recurse: ty; });

/// A statement is a component of a block expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Statement {
    /// A declaration of variables inside a pattern.
    Assignment(Assignment),
    /// An expression that returns nothing (the unit value).
    Expression(Expression),
}

impl Statement {
    /// Access the span of the statement contents.
    ///
    /// The terminating semicolon is deliberately not part of this span: it is a
    /// separator owned by the containing block's layout.
    pub fn span(&self) -> &Span {
        match self {
            Self::Assignment(assignment) => assignment.span(),
            Self::Expression(expression) => expression.span(),
        }
    }
}

impl_require_feature!(Statement {
    variants:
        Assignment(assignment),
        Expression(expr),
});

/// The output of an expression is assigned to a pattern.
#[derive(Clone, Debug)]
pub struct Assignment {
    pattern: Pattern,
    ty: AliasedType,
    expression: Expression,
    span: Span,
}

impl Assignment {
    /// Access the pattern of the assignment.
    pub fn pattern(&self) -> &Pattern {
        &self.pattern
    }

    /// Access the return type of assigned expression.
    pub fn ty(&self) -> &AliasedType {
        &self.ty
    }

    /// Access the assigned expression.
    pub fn expression(&self) -> &Expression {
        &self.expression
    }

    /// Access the span of the expression.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(Assignment; pattern, ty, expression);

impl_require_feature!(Assignment { recurse: pattern, ty, expression; });

/// Call expression.
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

    /// Access the arguments to the call.
    pub fn args(&self) -> &[Expression] {
        self.args.as_ref()
    }

    /// Access the span of the call.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(Call; name, args);

// Hand-written because `raw_hash` is gated per call name, while the macro
// can gate only an entire type, and `CallName` has no span of its own.
impl RequireFeature for Call {
    fn feature_requirements(&self, out: &mut Vec<FeatureRequirement>) {
        if let CallName::RawHash(_) = self.name {
            out.push(FeatureRequirement::new(UnstableFeature::RawHash, self.span));
        }

        self.name.feature_requirements(out);
        self.args.feature_requirements(out);
    }
}

/// Name of a call.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum CallName {
    /// Name of a jet.
    Jet(JetName),
    /// [`Either::unwrap_left`].
    UnwrapLeft(AliasedType),
    /// [`Either::unwrap_right`].
    UnwrapRight(AliasedType),
    /// [`Option::unwrap`].
    Unwrap,
    /// [`Option::is_none`].
    IsNone(AliasedType),
    /// [`assert!`].
    Assert,
    /// [`panic!`] without error message.
    Panic,
    /// [`dbg!`].
    Debug,
    /// Cast from the given source type.
    TypeCast(AliasedType),
    /// Name of a custom function.
    Custom(FunctionName),
    /// Fold of a bounded list with the given function.
    Fold(FunctionName, NonZeroPow2Usize),
    /// Fold of an array with the given function.
    ArrayFold(FunctionName, NonZeroUsize),
    /// Loop over the given function a bounded number of times until it returns success.
    ForWhile(FunctionName),
    /// SHA-256 of the concatenated bytes of a tuple of unsigned integers of the given type.
    RawHash(AliasedType),
}

impl_require_feature!(CallName {
    variants:
        Jet(_),
        UnwrapLeft(ty),
        UnwrapRight(ty),
        Unwrap,
        IsNone(ty),
        Assert,
        Panic,
        Debug,
        TypeCast(ty),
        Custom(_),
        Fold(_, _),
        ArrayFold(_, _),
        ForWhile(_),
        RawHash(ty),
});

/// A type alias.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct TypeAlias {
    visibility: Visibility,
    name: AliasName,
    ty: AliasedType,
    span: Span,
}

impl TypeAlias {
    pub fn visibility(&self) -> &Visibility {
        &self.visibility
    }

    /// Access the name of the alias.
    pub fn name(&self) -> &AliasName {
        &self.name
    }

    /// Access the type that the alias resolves to.
    ///
    /// During the parsing stage, the resolved type may include aliases.
    /// The compiler will later check if all contained aliases have been declared before.
    pub fn ty(&self) -> &AliasedType {
        &self.ty
    }

    /// Access the span of the alias.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(TypeAlias; name, ty);

impl_require_feature!(TypeAlias { recurse: ty; });

/// A constant declaration.
#[derive(Clone, Debug)]
pub struct ConstDecl {
    visibility: Visibility,
    name: Identifier,
    ty: AliasedType,
    expr: Expression,
    span: Span,
}

impl ConstDecl {
    pub fn visibility(&self) -> &Visibility {
        &self.visibility
    }

    pub fn name(&self) -> &Identifier {
        &self.name
    }

    pub fn ty(&self) -> &AliasedType {
        &self.ty
    }

    pub fn expr(&self) -> &Expression {
        &self.expr
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(ConstDecl; visibility, name, ty, expr);

impl_require_feature!(ConstDecl { recurse: ty, expr; });

impl AsRef<Span> for ConstDecl {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

/// A single variant in an enum declaration.
///
/// A variant's position among the declared variants determines its leaf
/// in the enum's balanced sum, i.e. its wire encoding.
/// A variant may carry payload types (`Refresh(Signature, u8)`).
/// A variant without payload is a unit variant.
#[derive(Clone, Debug)]
pub struct EnumVariant {
    name: Identifier,
    payload: Arc<[AliasedType]>,
    span: Span,
}

impl EnumVariant {
    pub fn name(&self) -> &Identifier {
        &self.name
    }

    /// Access the payload types of the variant. Empty for unit variants.
    pub fn payload(&self) -> &[AliasedType] {
        &self.payload
    }

    /// Access the source span of the complete variant.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(EnumVariant; name, payload);

impl AsRef<Span> for EnumVariant {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

/// An enum declaration.
#[derive(Clone, Debug)]
pub struct EnumDeclaration {
    visibility: Visibility,
    name: AliasName,
    variants: Arc<[EnumVariant]>,
    span: Span,
}

impl EnumDeclaration {
    pub fn visibility(&self) -> &Visibility {
        &self.visibility
    }

    pub fn name(&self) -> &AliasName {
        &self.name
    }

    pub fn variants(&self) -> &[EnumVariant] {
        &self.variants
    }

    /// Access the source span of the complete declaration.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_require_feature!(EnumVariant { recurse: payload; });

impl_require_feature!(EnumDeclaration {
    requires: UnstableFeature::Enums, span: span;
    recurse: variants;
});

impl_eq_hash!(EnumDeclaration; name, variants);

impl AsRef<Span> for EnumDeclaration {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

/// An expression is something that returns a value.
#[derive(Clone, Debug)]
pub struct Expression {
    inner: ExpressionInner,
    span: Span,
}

impl Expression {
    /// Access the inner expression.
    pub fn inner(&self) -> &ExpressionInner {
        &self.inner
    }

    /// Access the span of the expression.
    pub fn span(&self) -> &Span {
        &self.span
    }

    /// Convert the expression into a block expression.
    #[cfg(feature = "arbitrary")]
    fn into_block(self) -> Self {
        match self.inner {
            ExpressionInner::Single(_) => Expression {
                span: self.span,
                inner: ExpressionInner::Block(Arc::from([]), Some(Arc::new(self))),
            },
            _ => self,
        }
    }

    pub fn empty(span: Span) -> Self {
        Self {
            inner: ExpressionInner::Single(SingleExpression {
                inner: SingleExpressionInner::Tuple(Arc::new([])),
                span,
            }),
            span,
        }
    }
}

impl_eq_hash!(Expression; inner);

impl_require_feature!(Expression { recurse: inner; });

/// The kind of expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum ExpressionInner {
    /// A single expression directly returns a value.
    Single(SingleExpression),
    /// A block expression first executes a series of statements inside a local scope.
    /// Then, the block returns the value of its final expression.
    /// The block returns nothing (unit) if there is no final expression.
    Block(Arc<[Statement]>, Option<Arc<Expression>>),
}

impl_require_feature!(ExpressionInner {
    variants:
        Single(single),
        Block(statements, maybe_expr),
});

/// A single expression directly returns a value.
#[derive(Clone, Debug)]
pub struct SingleExpression {
    inner: SingleExpressionInner,
    span: Span,
}

impl SingleExpression {
    /// Access the inner expression.
    pub fn inner(&self) -> &SingleExpressionInner {
        &self.inner
    }

    /// Access the span of the expression.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(SingleExpression; inner);

impl_require_feature!(SingleExpression {recurse: inner; });

/// The kind of single expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum SingleExpressionInner {
    /// Either wrapper expression
    Either(Either<Arc<Expression>, Arc<Expression>>),
    /// Option wrapper expression
    Option(Option<Arc<Expression>>),
    /// Boolean literal expression
    Boolean(bool),
    /// Decimal string literal.
    Decimal(Decimal),
    /// Binary string literal.
    Binary(Binary),
    /// Hexadecimal string literal.
    Hexadecimal(Hexadecimal),
    /// Witness value.
    Witness(TemplateProgramWitness),
    /// Parameter value.
    Parameter(TemplateProgramWitness),
    /// Variable identifier expression
    Variable(Identifier),
    /// Function call
    Call(Call),
    /// Expression in parentheses
    Expression(Arc<Expression>),
    /// Match expression over a sum type
    Match(Match),
    /// Match expression over an enum's variants
    EnumMatch(EnumMatch),
    /// Construction of an enum variant
    EnumConstruction(EnumConstruction),
    /// Tuple wrapper expression
    Tuple(Arc<[Expression]>),
    /// Array wrapper expression
    Array(Arc<[Expression]>),
    /// List wrapper expression
    ///
    /// The exclusive upper bound on the list size is not known at this point
    List(Arc<[Expression]>),
}

impl_require_feature!(SingleExpressionInner {
    variants:
        Either(either),
        Option(maybe_expr),
        Boolean(_),
        Decimal(_),
        Binary(_),
        Hexadecimal(_),
        Witness(_),
        Parameter(_),
        Variable(_),
        Call(call),
        Expression(expr),
        Match(match_),
        EnumMatch(enum_match),
        EnumConstruction(construction),
        Tuple(exprs),
        Array(exprs),
        List(exprs),
});

/// Match expression.
#[derive(Clone, Debug)]
pub struct Match {
    scrutinee: Arc<Expression>,
    left: MatchArm,
    right: MatchArm,
    span: Span,
}

impl Match {
    /// Access the expression that is matched.
    pub fn scrutinee(&self) -> &Expression {
        &self.scrutinee
    }

    /// Access the match arm for left sum values.
    pub fn left(&self) -> &MatchArm {
        &self.left
    }

    /// Access the match arm for right sum values.
    pub fn right(&self) -> &MatchArm {
        &self.right
    }

    /// Access the span of the match statement.
    pub fn span(&self) -> &Span {
        &self.span
    }

    /// Get the type of the expression that is matched.
    pub fn scrutinee_type(&self) -> AliasedType {
        match (&self.left.pattern, &self.right.pattern) {
            (MatchPattern::Left(_, ty_l), MatchPattern::Right(_, ty_r)) => {
                AliasedType::either(ty_l.clone(), ty_r.clone())
            }
            (MatchPattern::None, MatchPattern::Some(_, ty_r)) => AliasedType::option(ty_r.clone()),
            (MatchPattern::False, MatchPattern::True) => AliasedType::boolean(),
            _ => unreachable!("Match expressions have valid left and right arms"),
        }
    }
}

impl_eq_hash!(Match; scrutinee, left, right);

impl_require_feature!(Match {recurse: scrutinee, left, right; });

/// Match expression over a named enum type.
#[derive(Clone, Debug)]
pub struct EnumMatch {
    scrutinee: Arc<Expression>,
    arms: Arc<[EnumMatchArm]>,
    span: Span,
}

impl EnumMatch {
    /// Access the expression that is matched.
    pub fn scrutinee(&self) -> &Expression {
        &self.scrutinee
    }

    /// Access the match arms.
    pub fn arms(&self) -> &[EnumMatchArm] {
        &self.arms
    }

    /// Access the span of the match statement.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_require_feature!(EnumMatch {
    requires: UnstableFeature::Enums, span: span;
    recurse: scrutinee, arms;
});

impl_eq_hash!(EnumMatch; scrutinee, arms);

impl AsRef<Span> for EnumMatch {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

/// Arm of an enum match expression: `Enum::Variant(bindings..) => expression`.
///
/// The arm type carries the classification the parser proved.
/// Every arm of an [`EnumMatch`] names an enum variant, so no other pattern kind is representable here.
#[derive(Clone, Debug)]
pub struct EnumMatchArm {
    enum_path: Arc<[Identifier]>,
    variant: Identifier,
    bindings: Arc<[(Pattern, AliasedType)]>,
    expression: Arc<Expression>,
    span: Span,
}

impl EnumMatchArm {
    /// Access the written enum path of the arm, e.g. `["m", "Choice"]`.
    pub fn enum_path(&self) -> &[Identifier] {
        &self.enum_path
    }

    /// The written enum path as one string, e.g. `m::Choice`.
    pub fn enum_path_string(&self) -> String {
        self.enum_path
            .iter()
            .map(Identifier::as_str)
            .collect::<Vec<_>>()
            .join("::")
    }

    /// Access the name of the matched variant.
    pub fn variant(&self) -> &Identifier {
        &self.variant
    }

    /// Access the payload bindings of the arm. Empty for unit variants.
    pub fn bindings(&self) -> &[(Pattern, AliasedType)] {
        &self.bindings
    }

    /// Access the expression that is executed in the match arm.
    pub fn expression(&self) -> &Expression {
        &self.expression
    }

    /// Access the source span of the complete arm, including its optional comma.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(EnumMatchArm; enum_path, variant, bindings, expression);

impl_require_feature!(EnumMatchArm { recurse: expression; });

/// Construction of an enum variant: `Action::Refresh(sig, 3)`.
///
/// The written enum name is either an alias in scope (`MyChoice`) or the
/// enum's declared name itself (`Action`), which needs no scope.
/// Unit variants take no argument list.
#[derive(Clone, Debug)]
pub struct EnumConstruction {
    enum_path: Arc<[Identifier]>,
    variant: Identifier,
    args: Arc<[Expression]>,
    span: Span,
}

impl EnumConstruction {
    /// Access the written enum path, e.g. `["m", "Action"]`.
    pub fn enum_path(&self) -> &[Identifier] {
        &self.enum_path
    }

    /// Access the name of the constructed variant.
    pub fn variant(&self) -> &Identifier {
        &self.variant
    }

    /// Access the payload arguments. Empty for unit variants.
    pub fn args(&self) -> &[Expression] {
        &self.args
    }

    /// Access the span of the construction expression.
    pub fn span(&self) -> &Span {
        &self.span
    }

    /// The written enum path as one string, e.g. `m::Action`.
    pub fn enum_path_string(&self) -> String {
        self.enum_path
            .iter()
            .map(Identifier::as_str)
            .collect::<Vec<_>>()
            .join("::")
    }
}

impl_eq_hash!(EnumConstruction; enum_path, variant, args);

impl_require_feature!(EnumConstruction {
    requires: UnstableFeature::Enums, span: span;
    recurse: args;
});

impl AsRef<Span> for EnumConstruction {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

/// Arm of a match expression.
#[derive(Clone, Debug)]
pub struct MatchArm {
    pattern: MatchPattern,
    expression: Arc<Expression>,
    span: Span,
}

impl MatchArm {
    /// Access the pattern that guards the match arm.
    pub fn pattern(&self) -> &MatchPattern {
        &self.pattern
    }

    /// Access the expression that is executed in the match arm.
    pub fn expression(&self) -> &Expression {
        &self.expression
    }

    /// Access the source span of the complete arm, including its optional comma.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(MatchArm; pattern, expression);

impl_require_feature!(MatchArm {recurse: pattern, expression; });

/// Pattern of a match arm.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum MatchPattern {
    /// Bind inner value of left value to a pattern.
    Left(Pattern, AliasedType),
    /// Bind inner value of right value to a pattern.
    Right(Pattern, AliasedType),
    /// Match none value (no binding).
    None,
    /// Bind inner value of some value to a pattern.
    Some(Pattern, AliasedType),
    /// Match false value (no binding).
    False,
    /// Match true value (no binding).
    True,
}

impl_require_feature!(MatchPattern {
    variants:
        Left(pattern, ty),
        Right(pattern, ty),
        None,
        Some(pattern, ty),
        False,
        True,
});

impl MatchPattern {
    /// Access the pattern of a match pattern that binds a variables.
    pub fn as_pattern(&self) -> Option<&Pattern> {
        match self {
            MatchPattern::Left(i, _) | MatchPattern::Right(i, _) | MatchPattern::Some(i, _) => {
                Some(i)
            }
            MatchPattern::None | MatchPattern::False | MatchPattern::True => None,
        }
    }

    /// Access the pattern and the type of a match pattern that binds a variables.
    pub fn as_typed_pattern(&self) -> Option<(&Pattern, &AliasedType)> {
        match self {
            MatchPattern::Left(i, ty) | MatchPattern::Right(i, ty) | MatchPattern::Some(i, ty) => {
                Some((i, ty))
            }
            MatchPattern::None | MatchPattern::False | MatchPattern::True => None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Module {
    visibility: Visibility,
    name: ModuleName,
    items: Arc<[Item]>,
    span: Span,
}

impl_require_feature!(Module {
    requires: UnstableFeature::Imports, span: span;
    recurse: items;
});

impl Module {
    /// Needed by the driver to wrap a single file into a module.
    pub(crate) fn new(
        file_id: usize,
        visibility: Visibility,
        name: ModuleName,
        items: &[Item],
    ) -> Module {
        Self {
            visibility,
            name,
            items: Arc::from(items),
            span: Span::new(file_id, 0..0),
        }
    }

    pub fn visibility(&self) -> &Visibility {
        &self.visibility
    }

    /// Access the name of the module.
    pub fn name(&self) -> &ModuleName {
        &self.name
    }

    /// Access the assignments of the module.
    pub fn items(&self) -> &[Item] {
        &self.items
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
    EnumMatch(&'a EnumMatch),
    EnumConstruction(&'a EnumConstruction),
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
                S::Boolean(_)
                | S::Binary(_)
                | S::Decimal(_)
                | S::Hexadecimal(_)
                | S::Variable(_)
                | S::Witness(_)
                | S::Parameter(_)
                | S::Option(None) => Tree::Nullary,
                S::Option(Some(l))
                | S::Either(Either::Left(l))
                | S::Either(Either::Right(l))
                | S::Expression(l) => Tree::Unary(Self::Expression(l)),
                S::Call(call) => Tree::Unary(Self::Call(call)),
                S::Match(match_) => Tree::Unary(Self::Match(match_)),
                S::EnumMatch(enum_match) => Tree::Unary(Self::EnumMatch(enum_match)),
                S::EnumConstruction(construction) => {
                    Tree::Unary(Self::EnumConstruction(construction))
                }
                S::Tuple(elements) | S::Array(elements) | S::List(elements) => {
                    Tree::Nary(elements.iter().map(Self::Expression).collect())
                }
            },
            Self::Call(call) => Tree::Nary(call.args().iter().map(Self::Expression).collect()),
            Self::EnumConstruction(construction) => {
                Tree::Nary(construction.args().iter().map(Self::Expression).collect())
            }
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
                            .map(|arm| Self::Expression(arm.expression())),
                    )
                    .collect(),
            ),
        }
    }
}

impl<'a, A: AsRef<Span>> From<&'a A> for Span {
    fn from(value: &'a A) -> Self {
        *value.as_ref()
    }
}

impl AsRef<Span> for Program {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for Function {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for FunctionParam {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for Assignment {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for TypeAlias {
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

impl AsRef<Span> for UseDecl {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}

impl AsRef<Span> for Module {
    fn as_ref(&self) -> &Span {
        &self.span
    }
}
