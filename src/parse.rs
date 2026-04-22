//! This module contains the parsing code to convert the
//! tokens into an AST.

use std::fmt;
use std::num::NonZeroUsize;
use std::str::FromStr;
use std::sync::Arc;

use chumsky::input::{Input, ValueInput};
use chumsky::prelude::{
    any, choice, empty, just, nested_delimiters, none_of, one_of, recursive, skip_then_retry_until,
    via_parser,
};
use chumsky::{extra, select, IterParser, Parser};

use either::Either;
use miniscript::iter::{Tree, TreeLike};

use crate::error::ErrorCollector;
use crate::error::{Error, RichError, Span};
use crate::impl_eq_hash;
use crate::lexer::Token;
use crate::num::NonZeroPow2Usize;
use crate::pattern::Pattern;
use crate::str::{
    AliasName, Binary, Decimal, FunctionName, Hexadecimal, Identifier, JetName, ModuleName,
    WitnessName,
};
use crate::types::{AliasedType, BuiltinAlias, TypeConstructible, UIntType};

/// A program is a sequence of items.
#[derive(Clone, Debug)]
pub struct Program {
    items: Arc<[Item]>,
    span: Span,
}

impl Program {
    /// Access the items of the program.
    pub fn items(&self) -> &[Item] {
        &self.items
    }
}

impl_eq_hash!(Program; items);

/// An item is a component of a program.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum Item {
    /// A type alias.
    TypeAlias(TypeAlias),
    /// A function.
    Function(Function),
    /// A module, which is ignored.
    Module,
}

/// Definition of a function.
#[derive(Clone, Debug)]
pub struct Function {
    name: FunctionName,
    params: Arc<[FunctionParam]>,
    ret: Option<AliasedType>,
    body: Expression,
    span: Span,
}

impl Function {
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

impl_eq_hash!(Function; name, params, ret, body);

/// Parameter of a function.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct FunctionParam {
    identifier: Identifier,
    ty: AliasedType,
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
}

/// A statement is a component of a block expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Statement {
    /// A declaration of variables inside a pattern.
    Assignment(Assignment),
    /// An expression that returns nothing (the unit value).
    Expression(Expression),
}

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
}

/// A type alias.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct TypeAlias {
    name: AliasName,
    ty: AliasedType,
    span: Span,
}

impl TypeAlias {
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
    Witness(WitnessName),
    /// Parameter value.
    Parameter(WitnessName),
    /// Variable identifier expression
    Variable(Identifier),
    /// Function call
    Call(Call),
    /// Expression in parentheses
    Expression(Arc<Expression>),
    /// Match expression over a sum type
    Match(Match),
    /// Tuple wrapper expression
    Tuple(Arc<[Expression]>),
    /// Array wrapper expression
    Array(Arc<[Expression]>),
    /// List wrapper expression
    ///
    /// The exclusive upper bound on the list size is not known at this point
    List(Arc<[Expression]>),
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

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
enum ParsedMatchCtor {
    Left,
    Right,
    Some,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum ParsedMatchPattern {
    False,
    True,
    None,
    Ctor(ParsedMatchCtor, Box<ParsedMatchPattern>),
    Bind(Pattern, AliasedType),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct ParsedMatchArm {
    pattern: ParsedMatchPattern,
    expression: Arc<Expression>,
    span: Span,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum MatchFamily {
    Either,
    Option,
    Bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum PatternCtorTag {
    Left,
    Right,
    Some,
    None,
    False,
    True,
}

impl PatternCtorTag {
    fn family(self) -> MatchFamily {
        match self {
            PatternCtorTag::Left | PatternCtorTag::Right => MatchFamily::Either,
            PatternCtorTag::Some | PatternCtorTag::None => MatchFamily::Option,
            PatternCtorTag::False | PatternCtorTag::True => MatchFamily::Bool,
        }
    }

    fn is_payload(self) -> bool {
        matches!(
            self,
            PatternCtorTag::Left | PatternCtorTag::Right | PatternCtorTag::Some
        )
    }

    fn as_payload_tag(self) -> &'static str {
        match self {
            PatternCtorTag::Left => "left",
            PatternCtorTag::Right => "right",
            PatternCtorTag::Some => "some",
            PatternCtorTag::None | PatternCtorTag::False | PatternCtorTag::True => {
                unreachable!("Nullary constructors do not carry payloads")
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum PatternIr {
    Wildcard(AliasedType),
    Bind(Pattern, AliasedType),
    Constructor(PatternCtorTag, Option<Box<PatternIr>>),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum TypedPatternIr {
    Wildcard(AliasedType),
    Bind(Pattern, AliasedType),
    Constructor {
        family: MatchFamily,
        tag: PatternCtorTag,
        inner: Option<Box<TypedPatternIr>>,
    },
}

impl TypedPatternIr {
    fn family(&self) -> Option<MatchFamily> {
        match self {
            TypedPatternIr::Constructor { family, .. } => Some(*family),
            TypedPatternIr::Wildcard(_) | TypedPatternIr::Bind(_, _) => None,
        }
    }
}

#[derive(Clone, Debug)]
struct TypedMatchArm {
    pattern: TypedPatternIr,
    expression: Arc<Expression>,
    span: Span,
}

#[derive(Clone, Debug)]
enum DecisionTree {
    Switch {
        family: MatchFamily,
        scrutinee: Arc<Expression>,
        branches: Vec<(PatternCtorTag, DecisionBranchKind)>,
        span: Span,
    },
}

#[derive(Clone, Debug)]
enum DecisionBranchKind {
    Nullary {
        expression: Arc<Expression>,
    },
    UnaryBind {
        pattern: Pattern,
        ty: AliasedType,
        expression: Arc<Expression>,
    },
    UnarySwitch {
        payload_pattern: Pattern,
        payload_expr: Arc<Expression>,
        payload_ty: AliasedType,
        tree: Box<DecisionTree>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ConstructorSpec {
    tag: PatternCtorTag,
    has_payload: bool,
}

/// Arm of a match expression.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct MatchArm {
    pattern: MatchPattern,
    expression: Arc<Expression>,
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
}

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

    /// Access the pattern and the type of match pattern that binds a variables.
    pub fn as_typed_pattern(&self) -> Option<(&Pattern, &AliasedType)> {
        match self {
            MatchPattern::Left(i, ty) | MatchPattern::Right(i, ty) | MatchPattern::Some(i, ty) => {
                Some((i, ty))
            }
            MatchPattern::None | MatchPattern::False | MatchPattern::True => None,
        }
    }
}

/// Program root when parsing modules.
#[derive(Clone, Debug)]
pub struct ModuleProgram {
    items: Arc<[ModuleItem]>,
    span: Span,
}

impl ModuleProgram {
    /// Access the items of the program.
    pub fn items(&self) -> &[ModuleItem] {
        &self.items
    }

    /// Access the span of the program.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(ModuleProgram; items);

/// Item when parsing modules.
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
    /// Access the name of the module.
    pub fn name(&self) -> &ModuleName {
        &self.name
    }

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
    ty: AliasedType,
    expression: Expression,
    span: Span,
}

impl ModuleAssignment {
    /// Access the assigned witness name.
    pub fn name(&self) -> &WitnessName {
        &self.name
    }

    /// Access the assigned witness type.
    pub fn ty(&self) -> &AliasedType {
        &self.ty
    }

    /// Access the assigned witness expression.
    pub fn expression(&self) -> &Expression {
        &self.expression
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for item in self.items() {
            writeln!(f, "{item}")?;
        }
        Ok(())
    }
}

impl fmt::Display for Item {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TypeAlias(alias) => write!(f, "{alias}"),
            Self::Function(function) => write!(f, "{function}"),
            // The parse tree contains no information about the contents of modules.
            // We print a random empty module `mod witness {}` here
            // so that `from_string(to_string(x)) = x` holds for all trees `x`.
            Self::Module => write!(f, "mod witness {{}}"),
        }
    }
}

impl fmt::Display for TypeAlias {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "type {} = {};", self.name(), self.ty())
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fn {}(", self.name())?;
        for (i, param) in self.params().iter().enumerate() {
            if 0 < i {
                write!(f, ", ")?;
            }
            write!(f, "{param}")?;
        }
        write!(f, ")")?;
        if let Some(ty) = self.ret() {
            write!(f, " -> {ty}")?;
        }
        write!(f, " {}", self.body())
    }
}

impl fmt::Display for FunctionParam {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.identifier(), self.ty())
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
                S::Tuple(elements) | S::Array(elements) | S::List(elements) => {
                    Tree::Nary(elements.iter().map(Self::Expression).collect())
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

impl fmt::Display for ExprTree<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use SingleExpressionInner as S;

        for data in self.verbose_pre_order_iter() {
            match &data.node {
                Self::Statement(..) if data.is_complete => writeln!(f, ";")?,
                Self::Expression(..) | Self::Statement(..) => {}
                Self::Block(..) => {
                    if data.n_children_yielded == 0 {
                        writeln!(f, "{{")?;
                    } else if !data.is_complete {
                        write!(f, "    ")?;
                    }
                    if data.is_complete {
                        writeln!(f, "}}")?;
                    }
                }
                Self::Assignment(assignment) => match data.n_children_yielded {
                    0 => write!(f, "let {}: {} = ", assignment.pattern(), assignment.ty())?,
                    n => debug_assert_eq!(n, 1),
                },
                Self::Single(single) => match single.inner() {
                    S::Boolean(bit) => write!(f, "{bit}")?,
                    S::Binary(binary) => write!(f, "0b{binary}")?,
                    S::Decimal(decimal) => write!(f, "{decimal}")?,
                    S::Hexadecimal(hexadecimal) => write!(f, "0x{hexadecimal}")?,
                    S::Variable(name) => write!(f, "{name}")?,
                    S::Witness(name) => write!(f, "witness::{name}")?,
                    S::Parameter(name) => write!(f, "param::{name}")?,
                    S::Option(None) => write!(f, "None")?,
                    S::Option(Some(_)) => match data.n_children_yielded {
                        0 => write!(f, "Some(")?,
                        n => {
                            debug_assert_eq!(n, 1);
                            write!(f, ")")?;
                        }
                    },
                    S::Either(Either::Left(_)) => match data.n_children_yielded {
                        0 => write!(f, "Left(")?,
                        n => {
                            debug_assert_eq!(n, 1);
                            write!(f, ")")?;
                        }
                    },
                    S::Either(Either::Right(_)) => match data.n_children_yielded {
                        0 => write!(f, "Right(")?,
                        n => {
                            debug_assert_eq!(n, 1);
                            write!(f, ")")?;
                        }
                    },
                    S::Expression(_) => match data.n_children_yielded {
                        0 => write!(f, "(")?,
                        n => {
                            debug_assert_eq!(n, 1);
                            write!(f, ")")?;
                        }
                    },
                    S::Call(..) | S::Match(..) => {}
                    S::Tuple(tuple) => {
                        if data.n_children_yielded == 0 {
                            write!(f, "(")?;
                        } else if !data.is_complete || tuple.len() == 1 {
                            write!(f, ", ")?;
                        }
                        if data.is_complete {
                            write!(f, ")")?;
                        }
                    }
                    S::Array(..) => {
                        if data.n_children_yielded == 0 {
                            write!(f, "[")?;
                        } else if !data.is_complete {
                            write!(f, ", ")?;
                        }
                        if data.is_complete {
                            write!(f, "]")?;
                        }
                    }
                    S::List(..) => {
                        if data.n_children_yielded == 0 {
                            write!(f, "list![")?;
                        } else if !data.is_complete {
                            write!(f, ", ")?;
                        }
                        if data.is_complete {
                            write!(f, "]")?;
                        }
                    }
                },
                Self::Call(call) => {
                    if data.n_children_yielded == 0 {
                        write!(f, "{}(", call.name())?;
                    } else if !data.is_complete {
                        write!(f, ", ")?;
                    }
                    if data.is_complete {
                        write!(f, ")")?;
                    }
                }
                Self::Match(match_) => match data.n_children_yielded {
                    0 => write!(f, "match ")?,
                    1 => write!(f, "{{\n{} => ", match_.left().pattern())?,
                    2 => write!(f, ",\n{} => ", match_.right().pattern())?,
                    n => {
                        debug_assert_eq!(n, 3);
                        write!(f, ",\n}}")?;
                    }
                },
            }
        }

        Ok(())
    }
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", ExprTree::Expression(self))
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", ExprTree::Statement(self))
    }
}

impl fmt::Display for Assignment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", ExprTree::Assignment(self))
    }
}

impl fmt::Display for SingleExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", ExprTree::Single(self))
    }
}

impl fmt::Display for Call {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", ExprTree::Call(self))
    }
}

impl fmt::Display for CallName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CallName::Jet(jet) => write!(f, "jet::{jet}"),
            CallName::UnwrapLeft(ty) => write!(f, "unwrap_left::<{ty}>"),
            CallName::UnwrapRight(ty) => write!(f, "unwrap_right::<{ty}>"),
            CallName::Unwrap => write!(f, "unwrap"),
            CallName::IsNone(ty) => write!(f, "is_none::<{ty}>"),
            CallName::Assert => write!(f, "assert!"),
            CallName::Panic => write!(f, "panic!"),
            CallName::Debug => write!(f, "dbg!"),
            CallName::TypeCast(ty) => write!(f, "<{ty}>::into"),
            CallName::Custom(name) => write!(f, "{name}"),
            CallName::Fold(name, bound) => write!(f, "fold::<{name}, {bound}>"),
            CallName::ArrayFold(name, size) => write!(f, "array_fold::<{name}, {size}>"),
            CallName::ForWhile(name) => write!(f, "for_while::<{name}>"),
        }
    }
}

impl fmt::Display for Match {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", ExprTree::Match(self))
    }
}

impl fmt::Display for MatchPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MatchPattern::Left(i, ty) => write!(f, "Left({i}: {ty})"),
            MatchPattern::Right(i, ty) => write!(f, "Right({i}: {ty})"),
            MatchPattern::None => write!(f, "None"),
            MatchPattern::Some(i, ty) => write!(f, "Some({i}: {ty})"),
            MatchPattern::False => write!(f, "false"),
            MatchPattern::True => write!(f, "true"),
        }
    }
}

macro_rules! impl_parse_wrapped_string {
    ($wrapper: ident, $label: literal) => {
        impl ChumskyParse for $wrapper {
            fn parser<'tokens, 'src: 'tokens, I>(
            ) -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
            where
                I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
            {
                select! {
                    Token::Ident(ident) => Self::from_str_unchecked(ident)
                }
                .labelled($label)
            }
        }
    };
}

impl_parse_wrapped_string!(FunctionName, "function name");
impl_parse_wrapped_string!(Identifier, "identifier");
impl_parse_wrapped_string!(WitnessName, "witness name");
impl_parse_wrapped_string!(AliasName, "alias name");
impl_parse_wrapped_string!(ModuleName, "module name");

/// Copy of [`FromStr`] that internally uses the `chumsky` parser.
pub trait ParseFromStr: Sized {
    /// Parse a value from the string `s`.
    fn parse_from_str(s: &str) -> Result<Self, RichError>;
}

/// Trait for parsing with collection of errors.
pub trait ParseFromStrWithErrors: Sized {
    /// Parse a value from the string `s` with Errors.
    fn parse_from_str_with_errors(s: &str, handler: &mut ErrorCollector) -> Option<Self>;
}

/// Trait for generating parsers of themselves.
///
/// Replacement for previous `PestParse` trait.
pub trait ChumskyParse: Sized {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>;
}

type ParseError<'src> = extra::Err<RichError>;

/// This implementation only returns first encountered error.
impl<A: ChumskyParse + fmt::Debug> ParseFromStr for A {
    fn parse_from_str(s: &str) -> Result<Self, RichError> {
        let (tokens, mut lex_errs) = crate::lexer::lex(s);

        let Some(tokens) = tokens else {
            return Err(lex_errs.pop().unwrap_or(RichError::parsing_error(
                "Empty token stream without an error.",
            )));
        };

        let (ast, parse_errs) = A::parser()
            .map_with(|parsed, _| parsed)
            .parse(
                tokens
                    .as_slice()
                    .map((s.len()..s.len()).into(), |(t, s)| (t, s)),
            )
            .into_output_errors();

        if parse_errs.is_empty() {
            Ok(ast.ok_or(RichError::parsing_error("Empty AST without an error."))?)
        } else {
            let err = parse_errs.first().unwrap().clone();
            Err(err)
        }
    }
}

impl<A: ChumskyParse + fmt::Debug> ParseFromStrWithErrors for A {
    fn parse_from_str_with_errors(s: &str, handler: &mut ErrorCollector) -> Option<Self> {
        let (tokens, lex_errs) = crate::lexer::lex(s);

        handler.update(lex_errs);
        let tokens = tokens?;

        let (ast, parse_errs) = A::parser()
            .map_with(|parsed, _| parsed)
            .parse(
                tokens
                    .as_slice()
                    .map((s.len()..s.len()).into(), |(t, s)| (t, s)),
            )
            .into_output_errors();

        handler.update(parse_errs);

        // TODO: We should return parsed result if we found errors, but because analyzing in `ast` module
        // is not handling poisoned tree right now, we don't return parsed result
        if handler.get().is_empty() {
            ast
        } else {
            None
        }
    }
}

/// Parse a token, and, if not found, place itself in place of missing one.
///
/// Should be only used when we know that this token should be there. For example, type of
/// `List<ty, bound>` would require comma inside angle brackets.
fn parse_token_with_recovery<'tokens, 'src: 'tokens, I>(
    tok: Token<'src>,
) -> impl Parser<'tokens, I, Token<'src>, ParseError<'src>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
{
    just(tok.clone()).recover_with(via_parser(empty().to(tok)))
}

/// Parser with error recovery for expressions, which would always contains given delimiters.
///
/// Can track span of open delimiter (if any).
fn delimited_with_recovery<'tokens, 'src: 'tokens, I, P, T, F>(
    parser: P,
    open: Token<'src>,
    close: Token<'src>,
    fallback: F,
) -> impl Parser<'tokens, I, T, ParseError<'src>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    P: Parser<'tokens, I, T, ParseError<'src>> + Clone,
    T: Clone + 'tokens,
    F: Fn(Span) -> T + Clone + 'tokens,
{
    just(open.clone())
        .map_with(|_, e| e.span())
        .then(parser.recover_with(via_parser(nested_delimiters(
            open.clone(),
            close.clone(),
            [
                (Token::LParen, Token::RParen),
                (Token::LBracket, Token::RBracket),
                (Token::LBrace, Token::RBrace),
                (Token::LAngle, Token::RAngle),
            ],
            fallback,
        ))))
        .then(just(close).or_not())
        // TODO: we should use information about open delimiter
        .validate(move |((open_span, content), close_token), _, emit| {
            if close_token.is_none() {
                emit.emit(Error::Grammar(format!("Unclosed delimiter {open}")).with_span(open_span))
            }
            content
        })
}

impl ChumskyParse for AliasedType {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let atom = select! {
                Token::Ident(ident) => {
                    if ident == "bool" {
                        AliasedType::boolean()
                    } else if let Ok(uint_type) = UIntType::from_str(ident) {
                        AliasedType::from(uint_type)
                    } else if let Ok(builtin) = BuiltinAlias::from_str(ident) {
                        AliasedType::builtin(builtin)
                    } else {
                        AliasedType::alias(AliasName::from_str_unchecked(ident))
                    }
                }
        };

        let num = select! {
            Token::DecLiteral(i) => i.clone()
        }
        .labelled("decimal number")
        .recover_with(via_parser(
            none_of([Token::RAngle, Token::RBracket])
                .ignored()
                .or(empty())
                .to(Decimal::from_str_unchecked("0")),
        ));

        recursive(|ty| {
            let args = delimited_with_recovery(
                ty.clone()
                    .then_ignore(parse_token_with_recovery(Token::Comma))
                    .then(ty.clone()),
                Token::LAngle,
                Token::RAngle,
                |_| {
                    (
                        AliasedType::alias(AliasName::from_str_unchecked("error")),
                        AliasedType::alias(AliasName::from_str_unchecked("error")),
                    )
                },
            );

            let sum_type = just(Token::Ident("Either"))
                .ignore_then(args)
                .map(|(left, right)| AliasedType::either(left, right))
                .labelled("Either");

            let option_type = just(Token::Ident("Option"))
                .ignore_then(delimited_with_recovery(
                    ty.clone(),
                    Token::LAngle,
                    Token::RAngle,
                    |_| AliasedType::alias(AliasName::from_str_unchecked("error")),
                ))
                .map(AliasedType::option)
                .labelled("Option");

            let tuple = delimited_with_recovery(
                ty.clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .collect()
                    .map(|s: Vec<AliasedType>| AliasedType::tuple(s)),
                Token::LParen,
                Token::RParen,
                |_| AliasedType::tuple(Vec::new()),
            )
            .labelled("tuple");

            let array = delimited_with_recovery(
                ty.clone()
                    .then_ignore(parse_token_with_recovery(Token::Semi))
                    .then(num.clone())
                    .map(|(ty, size)| {
                        AliasedType::array(ty, usize::from_str(size.as_inner()).unwrap_or_default())
                    }),
                Token::LBracket,
                Token::RBracket,
                |_| {
                    AliasedType::array(
                        AliasedType::alias(AliasName::from_str_unchecked("error")),
                        0,
                    )
                },
            )
            .labelled("array");

            let list = just(Token::Ident("List"))
                .ignore_then(delimited_with_recovery(
                    ty.then_ignore(parse_token_with_recovery(Token::Comma))
                        .then(num.clone().validate(|num, e, emit| {
                            match NonZeroPow2Usize::from_str(num.as_inner()) {
                                Ok(number) => number,
                                Err(err) => {
                                    emit.emit(
                                        Error::Grammar(format!("Cannot parse list bound: {err}"))
                                            .with_span(e.span()),
                                    );
                                    // fallback to default value
                                    NonZeroPow2Usize::TWO
                                }
                            }
                        })),
                    Token::LAngle,
                    Token::RAngle,
                    |_| {
                        (
                            AliasedType::alias(AliasName::from_str_unchecked("error")),
                            NonZeroPow2Usize::TWO,
                        )
                    },
                ))
                .map(|(ty, size)| AliasedType::list(ty, size))
                .labelled("List");

            choice((sum_type, option_type, tuple, array, list, atom))
                .map_with(|inner, _| inner)
                .labelled("type")
        })
    }
}

impl ChumskyParse for Program {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let skip_until_next_item = any()
            .then(
                any()
                    .filter(|t| !matches!(t, Token::Fn | Token::Type | Token::Mod))
                    .repeated(),
            )
            // map to empty module
            .map_with(|_, _| Item::Module);

        Item::parser()
            .recover_with(via_parser(skip_until_next_item))
            .repeated()
            .collect::<Vec<Item>>()
            .map_with(|items, e| Program {
                items: Arc::from(items),
                span: e.span(),
            })
    }
}

impl ChumskyParse for Item {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let func_parser = Function::parser().map(Item::Function);
        let type_parser = TypeAlias::parser().map(Item::TypeAlias);
        let mod_parser = Module::parser().map(|_| Item::Module);

        choice((func_parser, type_parser, mod_parser))
    }
}

impl ChumskyParse for Function {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let params = delimited_with_recovery(
            FunctionParam::parser()
                .separated_by(just(Token::Comma))
                .allow_trailing()
                .collect::<Vec<_>>(),
            Token::LParen,
            Token::RParen,
            |_| Vec::new(),
        )
        .map(Arc::from)
        .labelled("function parameters");

        let ret = just(Token::Arrow)
            .ignore_then(AliasedType::parser())
            .or_not()
            .labelled("return type");

        let body = just(Token::LBrace)
            .rewind()
            .ignore_then(Expression::parser())
            .recover_with(via_parser(nested_delimiters(
                Token::LBrace,
                Token::RBrace,
                [
                    (Token::LParen, Token::RParen),
                    (Token::LBracket, Token::RBracket),
                ],
                Expression::empty,
            )))
            .labelled("function body");

        just(Token::Fn)
            .ignore_then(FunctionName::parser())
            .then(params)
            .then(ret)
            .then(body)
            .map_with(|(((name, params), ret), body), e| Self {
                name,
                params,
                ret,
                body,
                span: e.span(),
            })
    }
}

impl ChumskyParse for FunctionParam {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let identifier = Identifier::parser();

        let ty = AliasedType::parser();

        identifier
            .then_ignore(just(Token::Colon))
            .then(ty)
            .map(|(identifier, ty)| Self { identifier, ty })
    }
}

impl Statement {
    fn parser<'tokens, 'src: 'tokens, I, E>(
        expr: E,
    ) -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
        E: Parser<'tokens, I, Expression, ParseError<'src>> + Clone + 'tokens,
    {
        let assignment = Assignment::parser(expr.clone()).map(Statement::Assignment);

        let expression = expr.map(Statement::Expression);

        choice((assignment, expression))
    }
}

impl Assignment {
    fn parser<'tokens, 'src: 'tokens, I, E>(
        expr: E,
    ) -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
        E: Parser<'tokens, I, Expression, ParseError<'src>> + Clone + 'tokens,
    {
        just(Token::Let)
            .ignore_then(Pattern::parser())
            .then_ignore(parse_token_with_recovery(Token::Colon))
            .then(AliasedType::parser())
            .then_ignore(parse_token_with_recovery(Token::Eq))
            .then(expr)
            .map_with(|((pattern, ty), expression), e| Self {
                pattern,
                ty,
                expression,
                span: e.span(),
            })
    }
}

impl ChumskyParse for Pattern {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        recursive(|pat| {
            let variable = Identifier::parser().map(Pattern::Identifier);

            let ignore = select! {
                Token::Ident("_") => Pattern::Ignore,
            };

            let tuple = delimited_with_recovery(
                pat.clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .collect::<Vec<_>>(),
                Token::LParen,
                Token::RParen,
                |_| Vec::new(),
            )
            .map(Pattern::tuple);

            let array = delimited_with_recovery(
                pat.clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .collect::<Vec<_>>(),
                Token::LBracket,
                Token::RBracket,
                |_| Vec::new(),
            )
            .map(Pattern::array);

            choice((ignore, variable, tuple, array)).labelled("pattern")
        })
    }
}

impl Call {
    fn parser<'tokens, 'src: 'tokens, I, E>(
        expr: E,
    ) -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
        E: Parser<'tokens, I, Expression, ParseError<'src>> + Clone + 'tokens,
    {
        let args = delimited_with_recovery(
            expr.separated_by(just(Token::Comma))
                .allow_trailing()
                .collect::<Vec<_>>(),
            Token::LParen,
            Token::RParen,
            |_| Vec::new(),
        )
        .map(Arc::from)
        .labelled("call arguments");

        CallName::parser()
            .then(args)
            .map_with(|(name, args), e| Self {
                name,
                args,
                span: e.span(),
            })
    }
}

impl ChumskyParse for CallName {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let turbofish_start = just(Token::DoubleColon).then(just(Token::LAngle)).ignored();

        let generics_close = just(Token::RAngle);

        let type_cast = just(Token::LAngle)
            .ignore_then(AliasedType::parser())
            .then_ignore(generics_close.clone())
            .then_ignore(just(Token::DoubleColon))
            .then_ignore(just(Token::Ident("into")))
            .map(CallName::TypeCast);

        let builtin_generic_ty = |name: &'static str, ctor: fn(AliasedType) -> Self| {
            just(Token::Ident(name))
                .ignore_then(turbofish_start.clone())
                .ignore_then(AliasedType::parser())
                .then_ignore(generics_close.clone())
                .map(ctor)
        };

        let unwrap_left = builtin_generic_ty("unwrap_left", CallName::UnwrapLeft);
        let unwrap_right = builtin_generic_ty("unwrap_right", CallName::UnwrapRight);
        let is_none = builtin_generic_ty("is_none", CallName::IsNone);

        let fold = just(Token::Ident("fold"))
            .ignore_then(turbofish_start.clone())
            .ignore_then(FunctionName::parser())
            .then_ignore(parse_token_with_recovery(Token::Comma))
            .then(select! { Token::DecLiteral(s) => s }.labelled("list size"))
            .then_ignore(generics_close.clone())
            .validate(|(func, bound_str), e, emit| {
                let bound = match bound_str.as_inner().parse::<usize>() {
                    Ok(num) => match NonZeroPow2Usize::new(num) {
                        Some(val) => val,
                        None => {
                            emit.emit(Error::ListBoundPow2(num).with_span(e.span()));
                            NonZeroPow2Usize::TWO
                        }
                    },
                    Err(_) => {
                        emit.emit(
                            Error::CannotParse(format!("Invalid number: {}", bound_str))
                                .with_span(e.span()),
                        );
                        NonZeroPow2Usize::TWO
                    }
                };

                CallName::Fold(func, bound)
            });

        let array_fold = just(Token::Ident("array_fold"))
            .ignore_then(turbofish_start.clone())
            .ignore_then(FunctionName::parser())
            .then_ignore(parse_token_with_recovery(Token::Comma))
            .then(select! { Token::DecLiteral(s) => s }.labelled("array size"))
            .then_ignore(generics_close.clone())
            .validate(|(func, size_str), e, emit| {
                let size = match size_str.as_inner().parse::<usize>() {
                    Ok(0) => {
                        emit.emit(Error::ArraySizeNonZero(0).with_span(e.span()));
                        NonZeroUsize::new(1).unwrap()
                    }
                    Ok(n) => NonZeroUsize::new(n).unwrap(),
                    Err(_) => {
                        emit.emit(
                            Error::CannotParse(format!("Invalid number: {}", size_str))
                                .with_span(e.span()),
                        );
                        NonZeroUsize::new(1).unwrap()
                    }
                };

                CallName::ArrayFold(func, size)
            });

        let for_while = just(Token::Ident("for_while"))
            .ignore_then(turbofish_start.clone())
            .ignore_then(FunctionName::parser())
            .then_ignore(generics_close.clone())
            .map(CallName::ForWhile);

        let simple_builtins = select! {
            Token::Ident("unwrap") => CallName::Unwrap,
            Token::Macro("assert!") => CallName::Assert,
            Token::Macro("panic!") => CallName::Panic,
            Token::Macro("dbg!") => CallName::Debug,
        };

        let jet = select! { Token::Jet(s) => JetName::from_str_unchecked(s) }.map(CallName::Jet);

        let custom_func = FunctionName::parser().map(CallName::Custom);

        choice((
            type_cast,
            unwrap_left,
            unwrap_right,
            is_none,
            fold,
            array_fold,
            for_while,
            simple_builtins,
            jet,
            custom_func,
        ))
    }
}

impl ChumskyParse for TypeAlias {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let name = AliasName::parser()
            .validate(|name, e, emit| {
                let ident = name.as_inner();
                let known_type = if ident == "bool" {
                    Some(AliasedType::boolean())
                } else if let Ok(uint_type) = UIntType::from_str(ident) {
                    Some(AliasedType::from(uint_type))
                } else if let Ok(builtin) = BuiltinAlias::from_str(ident) {
                    Some(AliasedType::builtin(builtin))
                } else {
                    None
                };

                if known_type.is_some() {
                    emit.emit(Error::RedefinedAliasAsBuiltin(name.clone()).with_span(e.span()));
                }
                name
            })
            .map_with(|name, e| (name, e.span()));

        just(Token::Type)
            .ignore_then(name)
            .then_ignore(parse_token_with_recovery(Token::Eq))
            .then(AliasedType::parser())
            .then_ignore(just(Token::Semi))
            .map_with(|(name, ty), e| Self {
                name: name.0,
                ty,
                span: e.span(),
            })
    }
}

impl ChumskyParse for Expression {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        recursive(|expr| {
            let block = {
                let statement = Statement::parser(expr.clone()).then_ignore(just(Token::Semi));

                let block_recovery = nested_delimiters(
                    Token::LBrace,
                    Token::RBrace,
                    [
                        (Token::LParen, Token::RParen),
                        (Token::LAngle, Token::RAngle),
                        (Token::LBracket, Token::RBracket),
                    ],
                    |span| Expression::empty(span).inner().clone(),
                );

                let statements = statement
                    .repeated()
                    .collect::<Vec<_>>()
                    .map(Arc::from)
                    .recover_with(skip_then_retry_until(
                        block_recovery.ignored().or(any().ignored()),
                        one_of([Token::Semi, Token::RParen, Token::RBracket, Token::RBrace])
                            .ignored(),
                    ));

                let final_expr = expr.clone().map(Arc::new).or_not();

                delimited_with_recovery(
                    statements.then(final_expr),
                    Token::LBrace,
                    Token::RBrace,
                    |_| (Arc::from(Vec::new()), None),
                )
                .map(|(stmts, end_expr)| ExpressionInner::Block(stmts, end_expr))
            };

            let single = SingleExpression::parser(expr.clone()).map(ExpressionInner::Single);

            choice((block, single))
                .map_with(|inner, e| Expression {
                    inner,
                    span: e.span(),
                })
                .labelled("expression")
        })
    }
}

impl SingleExpression {
    fn parser<'tokens, 'src: 'tokens, I, E>(
        expr: E,
    ) -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
        E: Parser<'tokens, I, Expression, ParseError<'src>> + Clone + 'tokens,
    {
        let wrapper = |name: &'static str| {
            select! { Token::Ident(i) if i == name => i }.ignore_then(
                expr.clone()
                    .delimited_by(just(Token::LParen), just(Token::RParen)),
            )
        };

        let left =
            wrapper("Left").map(|e| SingleExpressionInner::Either(Either::Left(Arc::new(e))));

        let right =
            wrapper("Right").map(|e| SingleExpressionInner::Either(Either::Right(Arc::new(e))));

        let some = wrapper("Some").map(|e| SingleExpressionInner::Option(Some(Arc::new(e))));

        let none = select! { Token::Ident("None") => SingleExpressionInner::Option(None) };

        let boolean = select! { Token::Bool(b) => SingleExpressionInner::Boolean(b) };

        let comma_separated = expr
            .clone()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .collect::<Vec<_>>();

        let array = delimited_with_recovery(
            comma_separated.clone(),
            Token::LBracket,
            Token::RBracket,
            |_| Vec::new(),
        )
        .map(|es| SingleExpressionInner::Array(Arc::from(es)));

        let list = just(Token::Macro("list!"))
            .ignore_then(delimited_with_recovery(
                comma_separated.clone(),
                Token::LBracket,
                Token::RBracket,
                |_| Vec::new(),
            ))
            .map(|es| SingleExpressionInner::List(Arc::from(es)));

        let tuple = delimited_with_recovery(
            comma_separated.clone(),
            Token::LParen,
            Token::RParen,
            |_| Vec::new(),
        )
        .map(|es| SingleExpressionInner::Tuple(Arc::from(es)));

        let literal = select! {
            Token::DecLiteral(s) => SingleExpressionInner::Decimal(s),
            Token::HexLiteral(s) => SingleExpressionInner::Hexadecimal(s),
            Token::BinLiteral(s) => SingleExpressionInner::Binary(s),
            Token::Witness(s) => SingleExpressionInner::Witness(WitnessName::from_str_unchecked(s)),
            Token::Param(s) => SingleExpressionInner::Parameter(WitnessName::from_str_unchecked(s)),
        };

        let call = Call::parser(expr.clone()).map(SingleExpressionInner::Call);

        let match_expr = Match::parser(expr.clone()).map(SingleExpressionInner::Match);

        let variable = Identifier::parser().map(SingleExpressionInner::Variable);

        // Expression delimeted by parentheses
        let expression = expr
            .clone()
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map(|es| SingleExpressionInner::Expression(Arc::from(es)));

        choice((
            left, right, some, none, boolean, match_expr, expression, list, array, tuple, call,
            literal, variable,
        ))
        .map_with(|inner, e| Self {
            inner,
            span: e.span(),
        })
    }
}

impl ChumskyParse for ParsedMatchPattern {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        recursive(|pat| {
            let bind = Pattern::parser()
                .then_ignore(just(Token::Colon))
                .then(AliasedType::parser())
                .map(|(pattern, ty)| ParsedMatchPattern::Bind(pattern, ty));

            let ctor = move |name: &'static str, ctor: ParsedMatchCtor| {
                select! { Token::Ident(i) if i == name => i }
                    .ignore_then(delimited_with_recovery(
                        pat.clone(),
                        Token::LParen,
                        Token::RParen,
                        |_| ParsedMatchPattern::Bind(Pattern::Ignore, error_aliased_type()),
                    ))
                    .map(move |inner| ParsedMatchPattern::Ctor(ctor, Box::new(inner)))
            };

            choice((
                ctor("Left", ParsedMatchCtor::Left),
                ctor("Right", ParsedMatchCtor::Right),
                ctor("Some", ParsedMatchCtor::Some),
                select! { Token::Ident("None") => ParsedMatchPattern::None },
                select! { Token::Bool(true) => ParsedMatchPattern::True },
                select! { Token::Bool(false) => ParsedMatchPattern::False },
                bind,
            ))
        })
    }
}

impl ParsedMatchArm {
    fn parser<'tokens, 'src: 'tokens, I, E>(
        expr: E,
    ) -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
        E: Parser<'tokens, I, Expression, ParseError<'src>> + Clone + 'tokens,
    {
        ParsedMatchPattern::parser()
            .then_ignore(just(Token::FatArrow))
            .then(expr.map(Arc::new))
            .then(just(Token::Comma).or_not())
            .validate(|((pattern, expression), comma), e, emitter| {
                let is_block = matches!(expression.as_ref().inner, ExpressionInner::Block(_, _));

                if !is_block && comma.is_none() {
                    emitter.emit(
                        Error::Grammar(
                            "Missing ',' after a match arm that isn't block expression".to_string(),
                        )
                        .with_span(e.span()),
                    );
                }

                Self {
                    pattern,
                    expression,
                    span: e.span(),
                }
            })
    }
}

fn lower_pattern_for_error(pattern: &ParsedMatchPattern) -> MatchPattern {
    match pattern {
        ParsedMatchPattern::Ctor(ParsedMatchCtor::Left, _) => {
            MatchPattern::Left(Pattern::Ignore, error_aliased_type())
        }
        ParsedMatchPattern::Ctor(ParsedMatchCtor::Right, _) => {
            MatchPattern::Right(Pattern::Ignore, error_aliased_type())
        }
        ParsedMatchPattern::Ctor(ParsedMatchCtor::Some, _) => {
            MatchPattern::Some(Pattern::Ignore, error_aliased_type())
        }
        ParsedMatchPattern::None => MatchPattern::None,
        ParsedMatchPattern::False => MatchPattern::False,
        ParsedMatchPattern::True => MatchPattern::True,
        ParsedMatchPattern::Bind(_, ty) => MatchPattern::Left(Pattern::Ignore, ty.clone()),
    }
}

fn payload_identifier(span: Span, branch: &str) -> Identifier {
    Identifier::from_str_unchecked(&format!(
        "__match_payload_{}_{}_{}",
        branch, span.start, span.end
    ))
}

fn payload_expression(identifier: &Identifier, span: Span) -> Arc<Expression> {
    Arc::new(Expression {
        inner: ExpressionInner::Single(SingleExpression {
            inner: SingleExpressionInner::Variable(identifier.clone()),
            span,
        }),
        span,
    })
}

fn match_arm(pattern: MatchPattern, expression: Arc<Expression>) -> MatchArm {
    MatchArm {
        pattern,
        expression,
    }
}

fn match_node(scrutinee: Arc<Expression>, left: MatchArm, right: MatchArm, span: Span) -> Match {
    Match {
        scrutinee,
        left,
        right,
        span,
    }
}

fn error_aliased_type() -> AliasedType {
    AliasedType::alias(AliasName::from_str_unchecked("error"))
}

fn wrap_nested_match(
    scrutinee: Arc<Expression>,
    left: MatchArm,
    right: MatchArm,
    span: Span,
) -> Arc<Expression> {
    Arc::new(Expression {
        inner: ExpressionInner::Single(SingleExpression {
            inner: SingleExpressionInner::Match(match_node(scrutinee, left, right, span)),
            span,
        }),
        span,
    })
}

fn pattern_ctor_tag_from_parsed_ctor(ctor: ParsedMatchCtor) -> PatternCtorTag {
    match ctor {
        ParsedMatchCtor::Left => PatternCtorTag::Left,
        ParsedMatchCtor::Right => PatternCtorTag::Right,
        ParsedMatchCtor::Some => PatternCtorTag::Some,
    }
}

fn constructor_specs(family: MatchFamily) -> &'static [ConstructorSpec] {
    match family {
        MatchFamily::Either => &[
            ConstructorSpec {
                tag: PatternCtorTag::Left,
                has_payload: true,
            },
            ConstructorSpec {
                tag: PatternCtorTag::Right,
                has_payload: true,
            },
        ],
        MatchFamily::Option => &[
            ConstructorSpec {
                tag: PatternCtorTag::None,
                has_payload: false,
            },
            ConstructorSpec {
                tag: PatternCtorTag::Some,
                has_payload: true,
            },
        ],
        MatchFamily::Bool => &[
            ConstructorSpec {
                tag: PatternCtorTag::False,
                has_payload: false,
            },
            ConstructorSpec {
                tag: PatternCtorTag::True,
                has_payload: false,
            },
        ],
    }
}

fn pattern_ir_from_parsed(pattern: ParsedMatchPattern) -> PatternIr {
    match pattern {
        ParsedMatchPattern::False => PatternIr::Constructor(PatternCtorTag::False, None),
        ParsedMatchPattern::True => PatternIr::Constructor(PatternCtorTag::True, None),
        ParsedMatchPattern::None => PatternIr::Constructor(PatternCtorTag::None, None),
        ParsedMatchPattern::Ctor(ctor, inner) => PatternIr::Constructor(
            pattern_ctor_tag_from_parsed_ctor(ctor),
            Some(Box::new(pattern_ir_from_parsed(*inner))),
        ),
        ParsedMatchPattern::Bind(Pattern::Ignore, ty) => PatternIr::Wildcard(ty),
        ParsedMatchPattern::Bind(pattern, ty) => PatternIr::Bind(pattern, ty),
    }
}

fn root_family_from_arm(arm: &ParsedMatchArm) -> Result<MatchFamily, Error> {
    match &arm.pattern {
        ParsedMatchPattern::Ctor(ctor, _) => Ok(pattern_ctor_tag_from_parsed_ctor(*ctor).family()),
        ParsedMatchPattern::None => Ok(MatchFamily::Option),
        ParsedMatchPattern::False | ParsedMatchPattern::True => Ok(MatchFamily::Bool),
        ParsedMatchPattern::Bind(_, _) => Err(Error::Grammar(
            "Top-level match arms must start with Left(..), Right(..), Some(..), None, false, or true"
                .to_string(),
        )),
    }
}

fn type_pattern_ir(
    pattern: PatternIr,
    top_level_family: MatchFamily,
    nested: bool,
) -> Result<TypedPatternIr, Error> {
    match pattern {
        PatternIr::Wildcard(ty) => {
            if nested {
                Ok(TypedPatternIr::Wildcard(ty))
            } else {
                Err(Error::Grammar(
                    "Top-level match arms must start with Left(..), Right(..), Some(..), None, false, or true"
                        .to_string(),
                ))
            }
        }
        PatternIr::Bind(pattern, ty) => {
            if nested {
                Ok(TypedPatternIr::Bind(pattern, ty))
            } else {
                Err(Error::Grammar(
                    "Top-level match arms must start with Left(..), Right(..), Some(..), None, false, or true"
                        .to_string(),
                ))
            }
        }
        PatternIr::Constructor(tag, inner) => {
            let family = tag.family();
            if !nested && family != top_level_family {
                return Err(Error::Grammar("Mixed match families".to_string()));
            }

            if nested && !tag.is_payload() {
                return Err(Error::Grammar(
                    "Unexpected terminal pattern under constructor".to_string(),
                ));
            }

            let typed_inner = if tag.is_payload() {
                let inner = inner.ok_or_else(|| {
                    Error::Grammar("Payload constructor missing inner pattern".to_string())
                })?;
                Some(Box::new(type_pattern_ir(*inner, top_level_family, true)?))
            } else {
                None
            };

            Ok(TypedPatternIr::Constructor {
                family,
                tag,
                inner: typed_inner,
            })
        }
    }
}

fn typed_arms_from_parsed(
    arms: &[ParsedMatchArm],
) -> Result<(MatchFamily, Vec<TypedMatchArm>), Error> {
    let first = arms
        .first()
        .ok_or_else(|| Error::Grammar("Match requires at least two arms".to_string()))?;
    let top_level_family = root_family_from_arm(first)?;

    let mut typed = Vec::with_capacity(arms.len());
    for arm in arms {
        let family = root_family_from_arm(arm)?;
        if family != top_level_family {
            return Err(Error::IncompatibleMatchArms(
                lower_pattern_for_error(&first.pattern),
                lower_pattern_for_error(&arm.pattern),
            ));
        }

        typed.push(TypedMatchArm {
            pattern: type_pattern_ir(
                pattern_ir_from_parsed(arm.pattern.clone()),
                top_level_family,
                false,
            )?,
            expression: arm.expression.clone(),
            span: arm.span,
        });
    }

    Ok((top_level_family, typed))
}

fn is_typed_wildcard(pattern: &TypedPatternIr) -> bool {
    matches!(
        pattern,
        TypedPatternIr::Wildcard(_) | TypedPatternIr::Bind(_, _)
    )
}

fn infer_family_from_patterns(patterns: &[TypedPatternIr]) -> Result<Option<MatchFamily>, Error> {
    let mut family: Option<MatchFamily> = None;

    for pattern in patterns {
        if let Some(current) = pattern.family() {
            if let Some(existing) = family {
                if existing != current {
                    return Err(Error::Grammar("Mixed match families".to_string()));
                }
            } else {
                family = Some(current);
            }
        }
    }

    Ok(family)
}

fn specialize_pattern_for_tag(
    pattern: &TypedPatternIr,
    tag: PatternCtorTag,
) -> Option<TypedPatternIr> {
    match pattern {
        TypedPatternIr::Wildcard(ty) => Some(TypedPatternIr::Wildcard(ty.clone())),
        TypedPatternIr::Bind(pattern, ty) => {
            Some(TypedPatternIr::Bind(pattern.clone(), ty.clone()))
        }
        TypedPatternIr::Constructor {
            tag: pattern_tag,
            inner,
            ..
        } if *pattern_tag == tag => {
            if tag.is_payload() {
                inner.as_ref().map(|inner| (**inner).clone())
            } else {
                Some(pattern.clone())
            }
        }
        TypedPatternIr::Constructor { .. } => None,
    }
}

fn branch_patterns_for_tag(
    patterns: &[TypedPatternIr],
    tag: PatternCtorTag,
) -> Vec<TypedPatternIr> {
    patterns
        .iter()
        .filter_map(|pattern| specialize_pattern_for_tag(pattern, tag))
        .collect()
}

fn typed_pattern_same_shape(a: &TypedPatternIr, b: &TypedPatternIr) -> bool {
    match (a, b) {
        (TypedPatternIr::Wildcard(ty_a), TypedPatternIr::Wildcard(ty_b)) => ty_a == ty_b,
        (TypedPatternIr::Bind(_, ty_a), TypedPatternIr::Bind(_, ty_b)) => ty_a == ty_b,
        (TypedPatternIr::Wildcard(ty_a), TypedPatternIr::Bind(_, ty_b))
        | (TypedPatternIr::Bind(_, ty_a), TypedPatternIr::Wildcard(ty_b)) => ty_a == ty_b,
        (
            TypedPatternIr::Constructor {
                family: family_a,
                tag: tag_a,
                inner: inner_a,
            },
            TypedPatternIr::Constructor {
                family: family_b,
                tag: tag_b,
                inner: inner_b,
            },
        ) if family_a == family_b && tag_a == tag_b => match (inner_a, inner_b) {
            (Some(inner_a), Some(inner_b)) => typed_pattern_same_shape(inner_a, inner_b),
            (None, None) => true,
            _ => false,
        },
        _ => false,
    }
}

fn typed_pattern_covers(cover: &TypedPatternIr, candidate: &TypedPatternIr) -> bool {
    match (cover, candidate) {
        (TypedPatternIr::Wildcard(_), _) | (TypedPatternIr::Bind(_, _), _) => true,
        (
            TypedPatternIr::Constructor {
                family: family_a,
                tag: tag_a,
                inner: inner_a,
            },
            TypedPatternIr::Constructor {
                family: family_b,
                tag: tag_b,
                inner: inner_b,
            },
        ) if family_a == family_b && tag_a == tag_b => match (inner_a, inner_b) {
            (Some(inner_a), Some(inner_b)) => typed_pattern_covers(inner_a, inner_b),
            (None, None) => true,
            _ => false,
        },
        _ => false,
    }
}

fn validate_duplicate_patterns(arms: &[TypedMatchArm]) -> Result<(), Error> {
    for i in 0..arms.len() {
        for j in (i + 1)..arms.len() {
            if typed_pattern_same_shape(&arms[i].pattern, &arms[j].pattern) {
                return Err(Error::Grammar("Duplicate match arm".to_string())
                    .with_span(arms[j].span)
                    .into());
            }
        }
    }

    Ok(())
}

fn validate_constructor_overlap_patterns(
    family: MatchFamily,
    patterns: &[TypedPatternIr],
    spans: &[Span],
) -> Result<(), Error> {
    for spec in constructor_specs(family) {
        if !spec.has_payload {
            continue;
        }

        let mut child_patterns = Vec::new();
        let mut child_spans = Vec::new();
        let mut saw_nested = false;

        for (pattern, span) in patterns.iter().zip(spans.iter().copied()) {
            if let Some(child) = specialize_pattern_for_tag(pattern, spec.tag) {
                if is_typed_wildcard(&child) {
                    if saw_nested {
                        return Err(Error::Grammar(
                            "Overlapping match arms in constructor branch".to_string(),
                        )
                        .with_span(span)
                        .into());
                    }
                } else if matches!(child, TypedPatternIr::Constructor { .. }) {
                    saw_nested = true;
                }

                child_patterns.push(child);
                child_spans.push(span);
            }
        }

        if child_patterns.is_empty() {
            continue;
        }

        let nested_children: Vec<_> = child_patterns
            .iter()
            .filter(|pattern| matches!(pattern, TypedPatternIr::Constructor { .. }))
            .cloned()
            .collect();
        let nested_spans: Vec<_> = child_patterns
            .iter()
            .zip(child_spans.iter().copied())
            .filter_map(|(pattern, span)| {
                matches!(pattern, TypedPatternIr::Constructor { .. }).then_some(span)
            })
            .collect();

        if !nested_children.is_empty() {
            let nested_family = infer_family_from_patterns(&nested_children)?
                .ok_or_else(|| Error::Grammar("Mixed match families".to_string()))?;
            validate_constructor_overlap_patterns(nested_family, &nested_children, &nested_spans)?;
        }
    }

    Ok(())
}

fn is_pattern_useful(previous: &[TypedPatternIr], new_pattern: &TypedPatternIr) -> bool {
    !previous
        .iter()
        .any(|previous_pattern| typed_pattern_covers(previous_pattern, new_pattern))
}

fn validate_pattern_usefulness(arms: &[TypedMatchArm]) -> Result<(), Error> {
    let mut previous = Vec::new();

    for arm in arms {
        if !is_pattern_useful(&previous, &arm.pattern) {
            return Err(Error::Grammar(
                "This match arm is unreachable because it is covered by a previous arm".to_string(),
            )
            .with_span(arm.span)
            .into());
        }

        previous.push(arm.pattern.clone());
    }

    Ok(())
}

fn missing_branch_message(tag: PatternCtorTag) -> &'static str {
    match tag {
        PatternCtorTag::Left => "Non-exhaustive Either match: missing Left branch",
        PatternCtorTag::Right => "Non-exhaustive Either match: missing Right branch",
        PatternCtorTag::Some => "Non-exhaustive Option match: missing Some",
        PatternCtorTag::None => "Non-exhaustive Option match: missing None",
        PatternCtorTag::False => "Non-exhaustive bool match: missing false",
        PatternCtorTag::True => "Non-exhaustive bool match: missing true",
    }
}

fn first_missing_pattern_message(
    family: MatchFamily,
    patterns: &[TypedPatternIr],
) -> Result<Option<String>, Error> {
    if patterns.iter().any(is_typed_wildcard) {
        return Ok(None);
    }

    for spec in constructor_specs(family) {
        let branch_patterns = branch_patterns_for_tag(patterns, spec.tag);
        if branch_patterns.is_empty() {
            return Ok(Some(missing_branch_message(spec.tag).to_string()));
        }

        if spec.has_payload {
            if branch_patterns.iter().any(is_typed_wildcard) {
                continue;
            }

            let nested_family = infer_family_from_patterns(&branch_patterns)?
                .ok_or_else(|| Error::Grammar("Mixed match families".to_string()))?;

            if let Some(message) = first_missing_pattern_message(nested_family, &branch_patterns)? {
                return Ok(Some(message));
            }
        }
    }

    Ok(None)
}

fn validate_pattern_exhaustiveness(
    family: MatchFamily,
    arms: &[TypedMatchArm],
) -> Result<(), Error> {
    let patterns: Vec<_> = arms.iter().map(|arm| arm.pattern.clone()).collect();

    if let Some(message) = first_missing_pattern_message(family, &patterns)? {
        return Err(Error::Grammar(message));
    }

    Ok(())
}

fn make_branch_typed_arm(pattern: TypedPatternIr, arm: &TypedMatchArm) -> TypedMatchArm {
    TypedMatchArm {
        pattern,
        expression: arm.expression.clone(),
        span: arm.span,
    }
}

fn compile_decision_branch(
    spec: ConstructorSpec,
    arms: &[TypedMatchArm],
    span: Span,
) -> Result<DecisionBranchKind, Error> {
    let mut applicable = Vec::new();
    for arm in arms {
        if let Some(pattern) = specialize_pattern_for_tag(&arm.pattern, spec.tag) {
            applicable.push(make_branch_typed_arm(pattern, arm));
        }
    }

    debug_assert!(!applicable.is_empty());

    if !spec.has_payload {
        return Ok(DecisionBranchKind::Nullary {
            expression: applicable[0].expression.clone(),
        });
    }

    let first = &applicable[0];
    match &first.pattern {
        TypedPatternIr::Wildcard(ty) => Ok(DecisionBranchKind::UnaryBind {
            pattern: Pattern::Ignore,
            ty: ty.clone(),
            expression: first.expression.clone(),
        }),
        TypedPatternIr::Bind(pattern, ty) => Ok(DecisionBranchKind::UnaryBind {
            pattern: pattern.clone(),
            ty: ty.clone(),
            expression: first.expression.clone(),
        }),
        TypedPatternIr::Constructor { .. } => {
            let payload_id = payload_identifier(span, spec.tag.as_payload_tag());
            let payload_pattern = Pattern::Identifier(payload_id.clone());
            let payload_expr = payload_expression(&payload_id, span);
            let nested_family = infer_family_from_patterns(
                &applicable
                    .iter()
                    .map(|arm| arm.pattern.clone())
                    .collect::<Vec<_>>(),
            )?
            .ok_or_else(|| Error::Grammar("Mixed match families".to_string()))?;
            let nested_tree =
                compile_decision_tree(payload_expr.clone(), nested_family, &applicable, span)?;
            let payload_ty = decision_tree_scrutinee_type(&nested_tree);

            Ok(DecisionBranchKind::UnarySwitch {
                payload_pattern,
                payload_expr,
                payload_ty,
                tree: Box::new(nested_tree),
            })
        }
    }
}

fn compile_decision_tree(
    scrutinee: Arc<Expression>,
    family: MatchFamily,
    arms: &[TypedMatchArm],
    span: Span,
) -> Result<DecisionTree, Error> {
    let mut branches = Vec::new();

    for spec in constructor_specs(family) {
        branches.push((spec.tag, compile_decision_branch(*spec, arms, span)?));
    }

    Ok(DecisionTree::Switch {
        family,
        scrutinee,
        branches,
        span,
    })
}

fn branch_payload_ty(branch: &DecisionBranchKind) -> Option<AliasedType> {
    match branch {
        DecisionBranchKind::Nullary { .. } => None,
        DecisionBranchKind::UnaryBind { ty, .. } => Some(ty.clone()),
        DecisionBranchKind::UnarySwitch { payload_ty, .. } => Some(payload_ty.clone()),
    }
}

fn decision_tree_scrutinee_type(tree: &DecisionTree) -> AliasedType {
    match tree {
        DecisionTree::Switch {
            family, branches, ..
        } => match family {
            MatchFamily::Bool => AliasedType::boolean(),
            MatchFamily::Option => {
                let some_ty = branches
                    .iter()
                    .find(|(tag, _)| *tag == PatternCtorTag::Some)
                    .and_then(|(_, branch)| branch_payload_ty(branch))
                    .unwrap_or_else(error_aliased_type);
                AliasedType::option(some_ty)
            }
            MatchFamily::Either => {
                let left_ty = branches
                    .iter()
                    .find(|(tag, _)| *tag == PatternCtorTag::Left)
                    .and_then(|(_, branch)| branch_payload_ty(branch))
                    .unwrap_or_else(error_aliased_type);
                let right_ty = branches
                    .iter()
                    .find(|(tag, _)| *tag == PatternCtorTag::Right)
                    .and_then(|(_, branch)| branch_payload_ty(branch))
                    .unwrap_or_else(error_aliased_type);
                AliasedType::either(left_ty, right_ty)
            }
        },
    }
}

fn lower_branch_kind_to_match_arm(
    tag: PatternCtorTag,
    branch: DecisionBranchKind,
    span: Span,
) -> Result<MatchArm, Error> {
    match branch {
        DecisionBranchKind::Nullary { expression } => {
            let pattern = match tag {
                PatternCtorTag::None => MatchPattern::None,
                PatternCtorTag::False => MatchPattern::False,
                PatternCtorTag::True => MatchPattern::True,
                PatternCtorTag::Left | PatternCtorTag::Right | PatternCtorTag::Some => {
                    return Err(Error::Grammar("Invalid nullary branch".to_string()))
                }
            };
            Ok(match_arm(pattern, expression))
        }
        DecisionBranchKind::UnaryBind {
            pattern,
            ty,
            expression,
        } => {
            let match_pattern = match tag {
                PatternCtorTag::Left => MatchPattern::Left(pattern, ty),
                PatternCtorTag::Right => MatchPattern::Right(pattern, ty),
                PatternCtorTag::Some => MatchPattern::Some(pattern, ty),
                PatternCtorTag::None | PatternCtorTag::False | PatternCtorTag::True => {
                    return Err(Error::Grammar("Invalid payload branch".to_string()))
                }
            };
            Ok(match_arm(match_pattern, expression))
        }
        DecisionBranchKind::UnarySwitch {
            payload_pattern,
            payload_expr,
            payload_ty,
            tree,
        } => {
            let nested = lower_decision_tree_to_match(*tree)?;
            let match_pattern = match tag {
                PatternCtorTag::Left => MatchPattern::Left(payload_pattern, payload_ty),
                PatternCtorTag::Right => MatchPattern::Right(payload_pattern, payload_ty),
                PatternCtorTag::Some => MatchPattern::Some(payload_pattern, payload_ty),
                PatternCtorTag::None | PatternCtorTag::False | PatternCtorTag::True => {
                    return Err(Error::Grammar("Invalid payload branch".to_string()))
                }
            };

            Ok(match_arm(
                match_pattern,
                wrap_nested_match(payload_expr, nested.left, nested.right, span),
            ))
        }
    }
}

fn lower_decision_tree_to_match(tree: DecisionTree) -> Result<Match, Error> {
    match tree {
        DecisionTree::Switch {
            family,
            scrutinee,
            branches,
            span,
        } => {
            let mut branch_map = std::collections::BTreeMap::new();
            for (tag, branch) in branches {
                branch_map.insert(tag, branch);
            }

            match family {
                MatchFamily::Either => Ok(match_node(
                    scrutinee,
                    lower_branch_kind_to_match_arm(
                        PatternCtorTag::Left,
                        branch_map.remove(&PatternCtorTag::Left).unwrap(),
                        span,
                    )?,
                    lower_branch_kind_to_match_arm(
                        PatternCtorTag::Right,
                        branch_map.remove(&PatternCtorTag::Right).unwrap(),
                        span,
                    )?,
                    span,
                )),
                MatchFamily::Option => Ok(match_node(
                    scrutinee,
                    lower_branch_kind_to_match_arm(
                        PatternCtorTag::None,
                        branch_map.remove(&PatternCtorTag::None).unwrap(),
                        span,
                    )?,
                    lower_branch_kind_to_match_arm(
                        PatternCtorTag::Some,
                        branch_map.remove(&PatternCtorTag::Some).unwrap(),
                        span,
                    )?,
                    span,
                )),
                MatchFamily::Bool => Ok(match_node(
                    scrutinee,
                    lower_branch_kind_to_match_arm(
                        PatternCtorTag::False,
                        branch_map.remove(&PatternCtorTag::False).unwrap(),
                        span,
                    )?,
                    lower_branch_kind_to_match_arm(
                        PatternCtorTag::True,
                        branch_map.remove(&PatternCtorTag::True).unwrap(),
                        span,
                    )?,
                    span,
                )),
            }
        }
    }
}

fn lower_match_arms(
    scrutinee: Arc<Expression>,
    arms: Vec<ParsedMatchArm>,
    span: Span,
) -> Result<Match, Error> {
    let (family, typed_arms) = typed_arms_from_parsed(&arms)?;
    let patterns: Vec<_> = typed_arms.iter().map(|arm| arm.pattern.clone()).collect();
    let spans: Vec<_> = typed_arms.iter().map(|arm| arm.span).collect();

    validate_duplicate_patterns(&typed_arms)?;
    validate_constructor_overlap_patterns(family, &patterns, &spans)?;
    validate_pattern_usefulness(&typed_arms)?;
    validate_pattern_exhaustiveness(family, &typed_arms)?;

    let tree = compile_decision_tree(scrutinee, family, &typed_arms, span)?;
    lower_decision_tree_to_match(tree)
}

impl Match {
    fn parser<'tokens, 'src: 'tokens, I, E>(
        expr: E,
    ) -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
        E: Parser<'tokens, I, Expression, ParseError<'src>> + Clone + 'tokens,
    {
        let scrutinee = expr.clone().map(Arc::new);

        let arms = delimited_with_recovery(
            ParsedMatchArm::parser(expr.clone())
                .repeated()
                .collect::<Vec<_>>(),
            Token::LBrace,
            Token::RBrace,
            |_| Vec::new(),
        );

        just(Token::Match)
            .ignore_then(scrutinee)
            .then(arms)
            .validate(|(scrutinee, arms), e, emit| {
                match lower_match_arms(scrutinee.clone(), arms, e.span()) {
                    Ok(match_) => match_,
                    Err(err) => {
                        emit.emit(err.with_span(e.span()));
                        match_node(
                            scrutinee,
                            match_arm(MatchPattern::False, Arc::new(Expression::empty(e.span()))),
                            match_arm(MatchPattern::True, Arc::new(Expression::empty(e.span()))),
                            e.span(),
                        )
                    }
                }
            })
    }
}

impl ChumskyParse for ModuleItem {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let module = Module::parser().map(Self::Module);

        module
    }
}

impl ChumskyParse for ModuleProgram {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        ModuleItem::parser()
            .repeated()
            .collect::<Vec<_>>()
            .map_with(|items, e| Self {
                items: Arc::from(items),
                span: e.span(),
            })
    }
}

impl ChumskyParse for Module {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let name = ModuleName::parser().map_with(|name, e| (name, e.span()));

        let assignments = ModuleAssignment::parser()
            .repeated()
            .collect::<Vec<_>>()
            .delimited_by(just(Token::LBrace), just(Token::RBrace))
            .recover_with(via_parser(nested_delimiters(
                Token::LBrace,
                Token::RBrace,
                [
                    (Token::LParen, Token::RParen),
                    (Token::LBracket, Token::RBracket),
                ],
                |_| Vec::new(),
            )))
            .map(Arc::from);

        just(Token::Mod)
            .ignore_then(name)
            .then(assignments)
            .map_with(|(name, assignments), e| Self {
                name: name.0,
                assignments,
                span: e.span(),
            })
    }
}

impl ChumskyParse for ModuleAssignment {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let name = WitnessName::parser();

        just(Token::Const)
            .ignore_then(name)
            .then_ignore(just(Token::Colon))
            .then(AliasedType::parser())
            .then_ignore(just(Token::Eq))
            .then(Expression::parser())
            .then_ignore(just(Token::Semi))
            .map_with(|((name, ty), expression), e| Self {
                name,
                ty,
                expression,
                span: e.span(),
            })
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

impl AsRef<Span> for ModuleProgram {
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

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for Program {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let len = u.int_in_range(0..=3)?;
        let items = (0..len)
            .map(|_| Item::arbitrary(u))
            .collect::<arbitrary::Result<Arc<[Item]>>>()?;
        Ok(Self {
            items,
            span: Span::DUMMY,
        })
    }
}

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for Function {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        <Self as crate::ArbitraryRec>::arbitrary_rec(u, 3)
    }
}

#[cfg(feature = "arbitrary")]
impl crate::ArbitraryRec for Function {
    fn arbitrary_rec(u: &mut arbitrary::Unstructured, budget: usize) -> arbitrary::Result<Self> {
        use arbitrary::Arbitrary;

        let name = FunctionName::arbitrary(u)?;
        let len = u.int_in_range(0..=3)?;
        let params = (0..len)
            .map(|_| FunctionParam::arbitrary(u))
            .collect::<arbitrary::Result<Arc<[FunctionParam]>>>()?;
        let ret = Option::<AliasedType>::arbitrary(u)?;
        let body = Expression::arbitrary_rec(u, budget).map(Expression::into_block)?;
        Ok(Self {
            name,
            params,
            ret,
            body,
            span: Span::DUMMY,
        })
    }
}

#[cfg(feature = "arbitrary")]
impl crate::ArbitraryRec for Expression {
    fn arbitrary_rec(u: &mut arbitrary::Unstructured, budget: usize) -> arbitrary::Result<Self> {
        use arbitrary::Arbitrary;

        let inner = match budget.checked_sub(1) {
            None => SingleExpression::arbitrary_rec(u, budget).map(ExpressionInner::Single),
            Some(new_budget) => match bool::arbitrary(u)? {
                false => SingleExpression::arbitrary_rec(u, budget).map(ExpressionInner::Single),
                true => {
                    let len = u.int_in_range(0..=3)?;
                    let statements = (0..len)
                        .map(|_| Statement::arbitrary_rec(u, new_budget))
                        .collect::<arbitrary::Result<Arc<[Statement]>>>()?;
                    let maybe_single = match bool::arbitrary(u)? {
                        false => None,
                        true => Expression::arbitrary_rec(u, new_budget)
                            .map(Arc::new)
                            .map(Some)?,
                    };
                    Ok(ExpressionInner::Block(statements, maybe_single))
                }
            },
        }?;
        Ok(Self {
            inner,
            span: Span::DUMMY,
        })
    }
}

#[cfg(feature = "arbitrary")]
impl crate::ArbitraryRec for Statement {
    fn arbitrary_rec(u: &mut arbitrary::Unstructured, budget: usize) -> arbitrary::Result<Self> {
        use arbitrary::Arbitrary;

        match bool::arbitrary(u)? {
            false => Assignment::arbitrary_rec(u, budget).map(Self::Assignment),
            true => Expression::arbitrary_rec(u, budget).map(Self::Expression),
        }
    }
}

#[cfg(feature = "arbitrary")]
impl crate::ArbitraryRec for Assignment {
    fn arbitrary_rec(u: &mut arbitrary::Unstructured, budget: usize) -> arbitrary::Result<Self> {
        use arbitrary::Arbitrary;

        let pattern = Pattern::arbitrary(u)?;
        let ty = AliasedType::arbitrary(u)?;
        let expression = Expression::arbitrary_rec(u, budget)?;

        Ok(Self {
            pattern,
            ty,
            expression,
            span: Span::DUMMY,
        })
    }
}

#[cfg(feature = "arbitrary")]
impl crate::ArbitraryRec for SingleExpression {
    fn arbitrary_rec(u: &mut arbitrary::Unstructured, budget: usize) -> arbitrary::Result<Self> {
        use arbitrary::Arbitrary;
        use SingleExpressionInner as S;

        let inner = match budget.checked_sub(1) {
            None => match u.int_in_range(0..=6)? {
                0 => bool::arbitrary(u).map(S::Boolean),
                1 => Binary::arbitrary(u).map(S::Binary),
                2 => Decimal::arbitrary(u).map(S::Decimal),
                3 => Hexadecimal::arbitrary(u).map(S::Hexadecimal),
                4 => Identifier::arbitrary(u).map(S::Variable),
                5 => WitnessName::arbitrary(u).map(S::Witness),
                6 => Ok(S::Option(None)),
                _ => unreachable!(),
            },
            Some(new_budget) => match u.int_in_range(0..=15)? {
                0 => bool::arbitrary(u).map(S::Boolean),
                1 => Binary::arbitrary(u).map(S::Binary),
                2 => Decimal::arbitrary(u).map(S::Decimal),
                3 => Hexadecimal::arbitrary(u).map(S::Hexadecimal),
                4 => Identifier::arbitrary(u).map(S::Variable),
                5 => WitnessName::arbitrary(u).map(S::Witness),
                6 => Ok(S::Option(None)),
                7 => Expression::arbitrary_rec(u, new_budget)
                    .map(Arc::new)
                    .map(Some)
                    .map(S::Option),
                8 => Expression::arbitrary_rec(u, new_budget)
                    .map(Arc::new)
                    .map(Either::Left)
                    .map(S::Either),
                9 => Expression::arbitrary_rec(u, new_budget)
                    .map(Arc::new)
                    .map(Either::Right)
                    .map(S::Either),
                10 => Expression::arbitrary_rec(u, new_budget)
                    .map(Arc::new)
                    .map(S::Expression),
                11 => Call::arbitrary_rec(u, new_budget).map(S::Call),
                12 => Match::arbitrary_rec(u, new_budget).map(S::Match),
                13 => {
                    let len = u.int_in_range(0..=3)?;
                    (0..len)
                        .map(|_| Expression::arbitrary_rec(u, new_budget))
                        .collect::<arbitrary::Result<Arc<[Expression]>>>()
                        .map(S::Tuple)
                }
                14 => {
                    let len = u.int_in_range(0..=3)?;
                    (0..len)
                        .map(|_| Expression::arbitrary_rec(u, new_budget))
                        .collect::<arbitrary::Result<Arc<[Expression]>>>()
                        .map(S::Array)
                }
                15 => {
                    let len = u.int_in_range(0..=3)?;
                    let elements = (0..len)
                        .map(|_| Expression::arbitrary_rec(u, new_budget))
                        .collect::<arbitrary::Result<Arc<[Expression]>>>()?;
                    Ok(S::List(elements))
                }
                _ => unreachable!(),
            },
        }?;
        Ok(Self {
            inner,
            span: Span::DUMMY,
        })
    }
}

#[cfg(feature = "arbitrary")]
impl crate::ArbitraryRec for Call {
    fn arbitrary_rec(u: &mut arbitrary::Unstructured, budget: usize) -> arbitrary::Result<Self> {
        use arbitrary::Arbitrary;

        let name = CallName::arbitrary(u)?;
        let len = u.int_in_range(0..=3)?;
        let args = (0..len)
            .map(|_| Expression::arbitrary_rec(u, budget))
            .collect::<arbitrary::Result<Arc<[Expression]>>>()?;
        Ok(Self {
            name,
            args,
            span: Span::DUMMY,
        })
    }
}

#[cfg(feature = "arbitrary")]
impl crate::ArbitraryRec for Match {
    fn arbitrary_rec(u: &mut arbitrary::Unstructured, budget: usize) -> arbitrary::Result<Self> {
        use arbitrary::Arbitrary;

        let scrutinee = Expression::arbitrary_rec(u, budget).map(Arc::new)?;
        let (pat_l, pat_r) = match u.int_in_range(0..=2)? {
            0 => {
                let id_l = Pattern::arbitrary(u)?;
                let ty_l = AliasedType::arbitrary(u)?;
                let pat_l = MatchPattern::Left(id_l, ty_l);
                let id_r = Pattern::arbitrary(u)?;
                let ty_r = AliasedType::arbitrary(u)?;
                let pat_r = MatchPattern::Right(id_r, ty_r);
                (pat_l, pat_r)
            }
            1 => {
                let id_r = Pattern::arbitrary(u)?;
                let ty_r = AliasedType::arbitrary(u)?;
                let pat_r = MatchPattern::Some(id_r, ty_r);
                (MatchPattern::None, pat_r)
            }
            2 => (MatchPattern::False, MatchPattern::True),
            _ => unreachable!(),
        };
        let expr_l = Expression::arbitrary_rec(u, budget).map(Arc::new)?;
        let expr_r = Expression::arbitrary_rec(u, budget).map(Arc::new)?;
        Ok(Self {
            scrutinee,
            left: MatchArm {
                pattern: pat_l,
                expression: expr_l,
            },
            right: MatchArm {
                pattern: pat_r,
                expression: expr_r,
            },
            span: Span::DUMMY,
        })
    }
}

#[cfg(test)]
mod test;
