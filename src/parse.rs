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
use crate::types::{AliasedType, BuiltinAlias, TypeConstructible};

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
    /// Use keyword to load other items
    Use(UseDecl),
    /// A module, which is ignored.
    Module,
}

/// Definition of a declaration
#[derive(Clone, Debug)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub struct UseDecl {
    visibility: Visibility,
    path: Vec<Identifier>, // TODO: Maybe change to Arc<[Identifier]> for consisten
    items: UseItems,
    span: Span,
}

impl UseDecl {
    /// Access the visibility of the use declaration.
    pub fn visibility(&self) -> &Visibility {
        &self.visibility
    }

    /// Access the visibility of the function.
    pub fn path(&self) -> &Vec<Identifier> {
        &self.path
    }

    pub fn path_buf(&self) -> std::path::PathBuf {
        self.path().iter().map(|s| s.as_ref()).collect()
    }

    /// Access the visibility of the function.
    pub fn items(&self) -> &UseItems {
        &self.items
    }

    /// Access the span of the use declaration.
    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl_eq_hash!(UseDecl; visibility, path, items);

// TODO: Add aliases
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum UseItems {
    Single(Identifier),
    List(Vec<Identifier>),
}

/// Definition of a function.
#[derive(Clone, Debug)]
pub struct Function {
    visibility: Visibility,
    name: FunctionName,
    params: Arc<[FunctionParam]>,
    ret: Option<AliasedType>,
    body: Expression,
    span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum Visibility {
    Public,
    Private,
}

impl Function {
    /// Access the visibility of the function.
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
    visibility: Visibility,
    name: AliasName,
    ty: AliasedType,
    span: Span,
}

impl TypeAlias {
    /// Access the visibility of the alias.
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
    /// Bind inner value of left value to variable name.
    Left(Identifier, AliasedType),
    /// Bind inner value of right value to variable name.
    Right(Identifier, AliasedType),
    /// Match none value (no binding).
    None,
    /// Bind inner value of some value to variable name.
    Some(Identifier, AliasedType),
    /// Match false value (no binding).
    False,
    /// Match true value (no binding).
    True,
}

impl MatchPattern {
    /// Access the identifier of a pattern that binds a variable.
    pub fn as_variable(&self) -> Option<&Identifier> {
        match self {
            MatchPattern::Left(i, _) | MatchPattern::Right(i, _) | MatchPattern::Some(i, _) => {
                Some(i)
            }
            MatchPattern::None | MatchPattern::False | MatchPattern::True => None,
        }
    }

    /// Access the identifier and the type of a pattern that binds a variable.
    pub fn as_typed_variable(&self) -> Option<(&Identifier, &AliasedType)> {
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
            Self::Use(use_declaration) => write!(f, "{use_declaration}"),
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

impl fmt::Display for UseDecl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Visibility::Public = self.visibility {
            write!(f, "pub ")?;
        }

        let _ = write!(f, "use ");

        for (i, segment) in self.path.iter().enumerate() {
            if i > 0 {
                write!(f, "::")?;
            }
            write!(f, "{}", segment)?;
        }

        if !self.path.is_empty() {
            write!(f, "::")?;
        }

        write!(f, "{};", self.items)
    }
}

impl fmt::Display for UseItems {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UseItems::Single(ident) => write!(f, "{}", ident),
            UseItems::List(idents) => {
                let _ = write!(f, "{{");
                for (i, ident) in idents.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", ident)?;
                }
                write!(f, "}}")
            }
        }
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
impl<A: ChumskyParse + std::fmt::Debug> ParseFromStr for A {
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

impl<A: ChumskyParse + std::fmt::Debug> ParseFromStrWithErrors for A {
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
                match ident
                {
                    "u1" => AliasedType::u1(),
                    "u2" =>  AliasedType::u2(),
                    "u4" =>  AliasedType::u4(),
                    "u8" => AliasedType::u8(),
                    "u16" => AliasedType::u16(),
                    "u32" => AliasedType::u32(),
                    "u64" => AliasedType::u64(),
                    "u128" => AliasedType::u128(),
                    "u256" => AliasedType::u256(),
                    "Ctx8" | "Pubkey" | "Message64" | "Message" | "Signature" | "Scalar" | "Fe" | "Gej"
                    | "Ge" | "Point" | "Height" | "Time" | "Distance" | "Duration" | "Lock" | "Outpoint"
                    | "Confidential1" | "ExplicitAsset" | "Asset1" | "ExplicitAmount" | "Amount1"
                    | "ExplicitNonce" | "Nonce" | "TokenAmount1" => AliasedType::builtin(BuiltinAlias::from_str(ident).unwrap()),
                    "bool" => AliasedType::boolean(),
                    _ => AliasedType::alias(AliasName::from_str_unchecked(ident)),
                }
            },
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
                    .filter(|t| {
                        !matches!(
                            t,
                            Token::Pub | Token::Use | Token::Fn | Token::Type | Token::Mod
                        )
                    })
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
        let use_parser = UseDecl::parser().map(Item::Use);
        let mod_parser = Module::parser().map(|_| Item::Module);

        choice((func_parser, use_parser, type_parser, mod_parser))
    }
}

impl ChumskyParse for Function {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let visibility = just(Token::Pub)
            .to(Visibility::Public)
            .or_not()
            .map(|v| v.unwrap_or(Visibility::Private))
            .labelled("function visibility");

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

        visibility
            .then_ignore(just(Token::Fn))
            .then(FunctionName::parser())
            .then(params)
            .then(ret)
            .then(body)
            .map_with(|((((visibility, name), params), ret), body), e| Self {
                visibility,
                name,
                params,
                ret,
                body,
                span: e.span(),
            })
    }
}

impl ChumskyParse for UseDecl {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        // TODO: Check does it possible to parse `use a: : smth`, because we need parse only `use a::smth`
        let double_colon = just(Token::Colon).then(just(Token::Colon)).labelled("::");

        let visibility = just(Token::Pub)
            .to(Visibility::Public)
            .or_not()
            .map(|v| v.unwrap_or(Visibility::Private));

        let path = Identifier::parser()
            .then_ignore(double_colon)
            .repeated()
            .at_least(1)
            .collect::<Vec<_>>();

        let list = Identifier::parser()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .collect()
            .delimited_by(just(Token::LBrace), just(Token::RBrace))
            .map(UseItems::List);
        let single = Identifier::parser().map(UseItems::Single);
        let items = choice((list, single));

        visibility
            .then_ignore(just(Token::Use))
            .then(path)
            .then(items)
            .then_ignore(just(Token::Semi))
            .map_with(|((visibility, path), items), e| Self {
                visibility,
                path,
                items,
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
        let double_colon = just(Token::Colon).then(just(Token::Colon)).labelled("::");

        let turbofish_start = double_colon.clone().then(just(Token::LAngle)).ignored();

        let generics_close = just(Token::RAngle);

        let type_cast = just(Token::LAngle)
            .ignore_then(AliasedType::parser())
            .then_ignore(generics_close.clone())
            .then_ignore(just(Token::Colon).then(just(Token::Colon)))
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
        let visibility = just(Token::Pub)
            .to(Visibility::Public)
            .or_not()
            .map(|v| v.unwrap_or(Visibility::Private));

        let name = AliasName::parser().map_with(|name, e| (name, e.span()));

        visibility
            .then(
                just(Token::Type)
                    .ignore_then(name)
                    .then_ignore(parse_token_with_recovery(Token::Eq))
                    .then(AliasedType::parser())
                    .then_ignore(just(Token::Semi)),
            )
            .map_with(|(visibility, (name, ty)), e| Self {
                visibility,
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
                        (Token::RAngle, Token::RAngle),
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

impl ChumskyParse for MatchPattern {
    fn parser<'tokens, 'src: 'tokens, I>() -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
    {
        let wrapper = |name: &'static str, ctor: fn(Identifier, AliasedType) -> Self| {
            select! { Token::Ident(i) if i == name => i }
                .ignore_then(delimited_with_recovery(
                    Identifier::parser()
                        .then_ignore(just(Token::Colon))
                        .then(AliasedType::parser()),
                    Token::LParen,
                    Token::RParen,
                    |_| {
                        (
                            Identifier::from_str_unchecked(""),
                            AliasedType::alias(AliasName::from_str_unchecked("error")),
                        )
                    },
                ))
                .map(move |(id, ty)| ctor(id, ty))
        };

        choice((
            wrapper("Left", MatchPattern::Left),
            wrapper("Right", MatchPattern::Right),
            wrapper("Some", MatchPattern::Some),
            select! { Token::Ident("None") => MatchPattern::None },
            select! { Token::Bool(true) => MatchPattern::True },
            select! { Token::Bool(false) => MatchPattern::False },
        ))
    }
}

impl MatchArm {
    fn parser<'tokens, 'src: 'tokens, I, E>(
        expr: E,
    ) -> impl Parser<'tokens, I, Self, ParseError<'src>> + Clone
    where
        I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
        E: Parser<'tokens, I, Expression, ParseError<'src>> + Clone + 'tokens,
    {
        MatchPattern::parser()
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
                }
            })
    }
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

        let arm_recovery = any()
            .filter(|t| !matches!(t, Token::Comma | Token::RBrace))
            .ignored()
            .or(nested_delimiters(
                Token::LBrace,
                Token::RBrace,
                [
                    (Token::LParen, Token::RParen),
                    (Token::LBracket, Token::RBracket),
                ],
                |_| (),
            )
            .ignored())
            .repeated()
            .map_with(|(), _| None);

        let arm_parser = MatchArm::parser(expr.clone())
            .map(Some)
            .recover_with(via_parser(arm_recovery.clone()));

        let arms = delimited_with_recovery(
            arm_parser.clone().then(arm_parser.clone()),
            Token::LBrace,
            Token::RBrace,
            |_| (None, None),
        );

        just(Token::Match)
            .ignore_then(scrutinee)
            .then(arms)
            .validate(|(scrutinee, arms), e, emit| match arms {
                (Some(first), Some(second)) => {
                    let (left, right) = match (&first.pattern, &second.pattern) {
                        (MatchPattern::Left(..), MatchPattern::Right(..)) => (first, second),
                        (MatchPattern::Right(..), MatchPattern::Left(..)) => (second, first),

                        (MatchPattern::None, MatchPattern::Some(..)) => (first, second),
                        (MatchPattern::Some(..), MatchPattern::None) => (second, first),

                        (MatchPattern::False, MatchPattern::True) => (first, second),
                        (MatchPattern::True, MatchPattern::False) => (second, first),

                        (p1, p2) => {
                            emit.emit(
                                Error::IncompatibleMatchArms(p1.clone(), p2.clone())
                                    .with_span(e.span()),
                            );
                            (first, second)
                        }
                    };

                    Self {
                        scrutinee,
                        left,
                        right,
                        span: e.span(),
                    }
                }
                _ => {
                    let match_arm_fallback = MatchArm {
                        expression: Arc::new(Expression::empty(Span::new(0, 0))),
                        pattern: MatchPattern::False,
                    };

                    let (left, right) = (
                        arms.0.unwrap_or(match_arm_fallback.clone()),
                        arms.1.unwrap_or(match_arm_fallback.clone()),
                    );
                    Self {
                        scrutinee,
                        left,
                        right,
                        span: e.span(),
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

        let visibility = Visibility::arbitrary(u)?;
        let name = FunctionName::arbitrary(u)?;
        let len = u.int_in_range(0..=3)?;
        let params = (0..len)
            .map(|_| FunctionParam::arbitrary(u))
            .collect::<arbitrary::Result<Arc<[FunctionParam]>>>()?;
        let ret = Option::<AliasedType>::arbitrary(u)?;
        let body = Expression::arbitrary_rec(u, budget).map(Expression::into_block)?;
        Ok(Self {
            visibility,
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
                let id_l = Identifier::arbitrary(u)?;
                let ty_l = AliasedType::arbitrary(u)?;
                let pat_l = MatchPattern::Left(id_l, ty_l);
                let id_r = Identifier::arbitrary(u)?;
                let ty_r = AliasedType::arbitrary(u)?;
                let pat_r = MatchPattern::Right(id_r, ty_r);
                (pat_l, pat_r)
            }
            1 => {
                let id_r = Identifier::arbitrary(u)?;
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
