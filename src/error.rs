use std::fmt;
use std::num::NonZeroUsize;
use std::sync::Arc;

use simplicity::hashes::{sha256, Hash, HashEngine};
use simplicity::{elements, Cmr};

use crate::parse::{MatchPattern, Rule};
use crate::str::{AliasName, FunctionName, Identifier, JetName, ModuleName, WitnessName};
use crate::types::{ResolvedType, UIntType};

/// Position of an object inside a file.
///
/// [`pest::Position<'i>`] forces us to track lifetimes, so we introduce our own struct.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Position {
    /// Line where the object is located.
    ///
    /// Starts at 1.
    pub line: NonZeroUsize,
    /// Column where the object is located.
    ///
    /// Starts at 1.
    pub col: NonZeroUsize,
}

impl Position {
    /// A dummy position.
    #[cfg(feature = "arbitrary")]
    pub(crate) const DUMMY: Self = Self::new(1, 1);

    /// Create a new position.
    ///
    /// ## Panics
    ///
    /// Line or column are zero.
    pub const fn new(line: usize, col: usize) -> Self {
        // assert_ne not available in constfn
        assert!(line != 0, "line must not be zero",);
        // Safety: Checked above
        let line = unsafe { NonZeroUsize::new_unchecked(line) };
        assert!(col != 0, "column must not be zero",);
        // Safety: Checked above
        let col = unsafe { NonZeroUsize::new_unchecked(col) };
        Self { line, col }
    }
}

/// Area that an object spans inside a file.
///
/// The area cannot be empty.
///
/// [`pest::Span<'i>`] forces us to track lifetimes, so we introduce our own struct.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Span {
    /// Position where the object starts, inclusively.
    pub start: Position,
    /// Position where the object ends, inclusively.
    pub end: Position,
}

impl Span {
    /// A dummy span.
    #[cfg(feature = "arbitrary")]
    pub(crate) const DUMMY: Self = Self::new(Position::DUMMY, Position::DUMMY);

    /// Create a new span.
    ///
    /// ## Panics
    ///
    /// Start comes after end.
    pub const fn new(start: Position, end: Position) -> Self {
        // NonZeroUsize does not implement const comparisons (yet)
        // So we call NonZeroUsize:get() to compare usize in const
        assert!(
            start.line.get() <= end.line.get(),
            "Start cannot come after end"
        );
        assert!(
            start.line.get() < end.line.get() || start.col.get() <= end.col.get(),
            "Start cannot come after end"
        );
        Self { start, end }
    }

    /// Check if the span covers more than one line.
    pub const fn is_multiline(&self) -> bool {
        self.start.line.get() < self.end.line.get()
    }

    /// Return the CMR of the span.
    pub fn cmr(&self) -> Cmr {
        let mut hasher = sha256::HashEngine::default();
        hasher.input(&self.start.line.get().to_be_bytes());
        hasher.input(&self.start.col.get().to_be_bytes());
        hasher.input(&self.end.line.get().to_be_bytes());
        hasher.input(&self.end.col.get().to_be_bytes());
        let hash = sha256::Hash::from_engine(hasher);
        Cmr::from_byte_array(hash.to_byte_array())
    }

    /// Return a slice from the given `file` that corresponds to the span.
    ///
    /// Return `None` if the span runs out of bounds.
    pub fn to_slice<'a>(&self, file: &'a str) -> Option<&'a str> {
        let mut current_line = 1;
        let mut current_col = 1;
        let mut start_index = None;

        for (i, c) in file.char_indices() {
            if current_line == self.start.line.get() && current_col == self.start.col.get() {
                start_index = Some(i);
            }
            if current_line == self.end.line.get() && current_col == self.end.col.get() {
                let start_index = start_index.expect("start comes before end");
                let end_index = i;
                return Some(&file[start_index..end_index]);
            }
            if c == '\n' {
                current_line += 1;
                current_col = 1;
            } else {
                current_col += 1;
            }
        }

        None
    }
}

impl<'a> From<&'a pest::iterators::Pair<'_, Rule>> for Span {
    fn from(pair: &'a pest::iterators::Pair<Rule>) -> Self {
        let (line, col) = pair.line_col();
        let start = Position::new(line, col);
        // end_pos().line_col() is O(n) in file length
        // https://github.com/pest-parser/pest/issues/560
        // We should generate `Span`s only on error paths
        let (line, col) = pair.as_span().end_pos().line_col();
        let end = Position::new(line, col);
        Self::new(start, end)
    }
}

impl From<&str> for Span {
    fn from(s: &str) -> Self {
        let start = Position::new(1, 1);
        let end_line = std::cmp::max(1, s.lines().count());
        let end_col = std::cmp::max(1, s.lines().next_back().unwrap_or("").len());
        let end = Position::new(end_line, end_col);
        debug_assert!(start.line <= end.line);
        debug_assert!(start.line < end.line || start.col <= end.col);
        Span::new(start, end)
    }
}

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for Span {
    fn arbitrary(_: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(Self::DUMMY)
    }
}

/// Helper trait to convert `Result<T, E>` into `Result<T, RichError>`.
pub trait WithSpan<T> {
    /// Update the result with the affected span.
    fn with_span<S: Into<Span>>(self, span: S) -> Result<T, RichError>;
}

impl<T, E: Into<Error>> WithSpan<T> for Result<T, E> {
    fn with_span<S: Into<Span>>(self, span: S) -> Result<T, RichError> {
        self.map_err(|e| e.into().with_span(span.into()))
    }
}

/// Helper trait to update `Result<A, RichError>` with the affected source file.
pub trait WithFile<T> {
    /// Update the result with the affected source file.
    ///
    /// Enable pretty errors.
    fn with_file<F: Into<Arc<str>>>(self, file: F) -> Result<T, RichError>;
}

impl<T> WithFile<T> for Result<T, RichError> {
    fn with_file<F: Into<Arc<str>>>(self, file: F) -> Result<T, RichError> {
        self.map_err(|e| e.with_file(file.into()))
    }
}

/// An error enriched with context.
///
/// Records _what_ happened and _where_.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct RichError {
    /// The error that occurred.
    error: Error,
    /// Area that the error spans inside the file.
    span: Span,
    /// File in which the error occurred.
    ///
    /// Required to print pretty errors.
    file: Option<Arc<str>>,
}

impl RichError {
    /// Create a new error with context.
    pub fn new(error: Error, span: Span) -> RichError {
        RichError {
            error,
            span,
            file: None,
        }
    }

    /// Add the source file where the error occurred.
    ///
    /// Enable pretty errors.
    pub fn with_file(self, file: Arc<str>) -> Self {
        Self {
            error: self.error,
            span: self.span,
            file: Some(file),
        }
    }
}

impl fmt::Display for RichError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.file {
            Some(ref file) if !file.is_empty() => {
                let start_line_index = self.span.start.line.get() - 1;
                let n_spanned_lines = self.span.end.line.get() - start_line_index;
                let line_num_width = self.span.end.line.get().to_string().len();
                writeln!(f, "{:width$} |", " ", width = line_num_width)?;

                let mut lines = file.lines().skip(start_line_index).peekable();
                let start_line_len = lines.peek().map_or(0, |l| l.len());

                for (relative_line_index, line_str) in lines.take(n_spanned_lines).enumerate() {
                    let line_num = start_line_index + relative_line_index + 1;
                    writeln!(f, "{line_num:line_num_width$} | {line_str}")?;
                }

                let (underline_start, underline_length) = match self.span.is_multiline() {
                    true => (0, start_line_len),
                    false => (
                        self.span.start.col.get(),
                        self.span.end.col.get() - self.span.start.col.get(),
                    ),
                };
                write!(f, "{:width$} |", " ", width = line_num_width)?;
                write!(f, "{:width$}", " ", width = underline_start)?;
                write!(f, "{:^<width$} ", "", width = underline_length)?;
                write!(f, "{}", self.error)
            }
            _ => {
                write!(f, "{}", self.error)
            }
        }
    }
}

impl std::error::Error for RichError {}

impl From<RichError> for Error {
    fn from(error: RichError) -> Self {
        error.error
    }
}

impl From<RichError> for String {
    fn from(error: RichError) -> Self {
        error.to_string()
    }
}

impl From<pest::error::Error<Rule>> for RichError {
    fn from(error: pest::error::Error<Rule>) -> Self {
        let description = error.variant.message().to_string();
        let (start, end) = match error.line_col {
            pest::error::LineColLocation::Pos((line, col)) => {
                (Position::new(line, col), Position::new(line, col + 1))
            }
            pest::error::LineColLocation::Span((line, col), (line_end, col_end)) => {
                (Position::new(line, col), Position::new(line_end, col_end))
            }
        };
        let span = Span::new(start, end);
        Self::new(Error::Grammar(description), span)
    }
}

/// An individual error.
///
/// Records _what_ happened but not where.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Error {
    ListBoundPow2(usize),
    BitStringPow2(usize),
    HexStringLen(usize),
    ForWhileWidthPow2(usize),
    CannotParse(String),
    Grammar(String),
    IncompatibleMatchArms(MatchPattern, MatchPattern),
    /// Simplicity's type system rejected the compiled code.
    /// 
    /// This indicates a mismatch between SimplicityHL's type checking and
    /// Simplicity's more strict type system. This is expected during development
    /// as SimplicityHL's type system continues to improve.
    SimplicityTypeError(String),
    /// General compilation failure that doesn't fit other error categories.
    /// 
    /// This is a fallback for unexpected compilation issues.
    CannotCompile(String),
    JetDoesNotExist(JetName),
    InvalidCast(ResolvedType, ResolvedType),
    MainNoInputs,
    MainNoOutput,
    MainRequired,
    FunctionRedefined(FunctionName),
    FunctionUndefined(FunctionName),
    InvalidNumberOfArguments(usize, usize),
    FunctionNotFoldable(FunctionName),
    FunctionNotLoopable(FunctionName),
    ExpressionUnexpectedType(ResolvedType),
    ExpressionTypeMismatch(ResolvedType, ResolvedType),
    ExpressionNotConstant,
    IntegerOutOfBounds(UIntType),
    UndefinedVariable(Identifier),
    UndefinedAlias(AliasName),
    VariableReuseInPattern(Identifier),
    WitnessReused(WitnessName),
    WitnessTypeMismatch(WitnessName, ResolvedType, ResolvedType),
    WitnessReassigned(WitnessName),
    WitnessOutsideMain,
    ModuleRequired(ModuleName),
    ModuleRedefined(ModuleName),
    ArgumentMissing(WitnessName),
    ArgumentTypeMismatch(WitnessName, ResolvedType, ResolvedType),
}

#[rustfmt::skip]
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::ListBoundPow2(bound) => write!(
                f,
                "Expected a power of two greater than one (2, 4, 8, 16, 32, ...) as list bound, found {bound}"
            ),
            Error::BitStringPow2(len) => write!(
                f,
                "Expected a valid bit string length (1, 2, 4, 8, 16, 32, 64, 128, 256), found {len}"
            ),
            Error::HexStringLen(len) => write!(
                f,
                "Expected an even hex string length (0, 2, 4, 6, 8, ...), found {len}"
            ),
            Error::ForWhileWidthPow2(bit_width) => write!(
                f,
                "Expected a power of two (1, 2, 4, 8, 16, ...) as for-while bit width, found {bit_width}"
            ),
            Error::CannotParse(description) => write!(
                f,
                "Cannot parse: {description}"
            ),
            Error::Grammar(description) => write!(
                f,
                "Grammar error: {description}"
            ),
            Error::IncompatibleMatchArms(pattern1, pattern2) => write!(
                f,
                "Match arm `{pattern1}` is incompatible with arm `{pattern2}`"
            ),
            Error::SimplicityTypeError(description) => write!(
                f,
                "Simplicity type system rejected this code: {description}"
            ),
            Error::TypeUnificationError(expected, found) => write!(
                f,
                "Cannot unify types: expected `{expected}`, found `{found}`"
            ),
            Error::ContextTypeMismatch(expected, found) => write!(
                f,
                "Context type mismatch: expected `{expected}`, found `{found}`"
            ),
            Error::CannotCompile(description) => write!(
                f,
                "Failed to compile to Simplicity: {description}"
            ),
            Error::JetDoesNotExist(name) => write!(
                f,
                "Jet `{name}` does not exist"
            ),
            Error::InvalidCast(source, target) => write!(
                f,
                "Cannot cast values of type `{source}` as values of type `{target}`"
            ),
            Error::MainNoInputs => write!(
                f,
                "Main function takes no input parameters"
            ),
            Error::MainNoOutput => write!(
                f,
                "Main function produces no output"
            ),
            Error::MainRequired => write!(
                f,
                "Main function is required"
            ),
            Error::FunctionRedefined(name) => write!(
                f,
                "Function `{name}` was defined multiple times"
            ),
            Error::FunctionUndefined(name) => write!(
                f,
                "Function `{name}` was called but not defined"
            ),
            Error::InvalidNumberOfArguments(expected, found) => write!(
                f,
                "Expected {expected} arguments, found {found} arguments"
            ),
            Error::FunctionNotFoldable(name) => write!(
                f,
                "Expected a signature like `fn {name}(element: E, accumulator: A) -> A` for a fold"
            ),
            Error::FunctionNotLoopable(name) => write!(
                f,
                "Expected a signature like `fn {name}(accumulator: A, context: C, counter u{{1,2,4,8,16}}) -> Either<B, A>` for a for-while loop"
            ),
            Error::ExpressionUnexpectedType(ty) => write!(
                f,
                "Expected expression of type `{ty}`; found something else"
            ),
            Error::ExpressionTypeMismatch(expected, found) => write!(
                f,
                "Expected expression of type `{expected}`, found type `{found}`"
            ),
            Error::ExpressionNotConstant => write!(
                f,
                "Expression cannot be evaluated at compile time"
            ),
            Error::IntegerOutOfBounds(ty) => write!(
                f,
                "Value is out of bounds for type `{ty}`"
            ),
            Error::UndefinedVariable(identifier) => write!(
                f,
                "Variable `{identifier}` is not defined"
            ),
            Error::UndefinedAlias(identifier) => write!(
                f,
                "Type alias `{identifier}` is not defined"
            ),
            Error::VariableReuseInPattern(identifier) => write!(
                f,
                "Variable `{identifier}` is used twice in the pattern"
            ),
            Error::WitnessReused(name) => write!(
                f,
                "Witness `{name}` has been used before somewhere in the program"
            ),
            Error::WitnessTypeMismatch(name, declared, assigned) => write!(
                f,
                "Witness `{name}` was declared with type `{declared}` but its assigned value is of type `{assigned}`"
            ),
            Error::WitnessReassigned(name) => write!(
                f,
                "Witness `{name}` has already been assigned a value"
            ),
            Error::WitnessOutsideMain => write!(
                f,
                "Witness expressions are not allowed outside the `main` function"
            ),
            Error::ModuleRequired(name) => write!(
                f,
                "Required module `{name}` is missing"
            ),
            Error::ModuleRedefined(name) => write!(
                f,
                "Module `{name}` is defined twice"
            ),
            Error::ArgumentMissing(name) => write!(
                f,
                "Parameter `{name}` is missing an argument"
            ),
            Error::ArgumentTypeMismatch(name, declared, assigned) => write!(
                f,
                "Parameter `{name}` was declared with type `{declared}` but its assigned argument is of type `{assigned}`"
            ),
        }
    }
}

impl std::error::Error for Error {}

impl Error {
    /// Update the error with the affected span.
    pub fn with_span(self, span: Span) -> RichError {
        RichError::new(self, span)
    }
}

impl From<elements::hex::Error> for Error {
    fn from(error: elements::hex::Error) -> Self {
        Self::CannotParse(error.to_string())
    }
}

impl From<std::num::ParseIntError> for Error {
    fn from(error: std::num::ParseIntError) -> Self {
        Self::CannotParse(error.to_string())
    }
}

impl From<crate::num::ParseIntError> for Error {
    fn from(error: crate::num::ParseIntError) -> Self {
        Self::CannotParse(error.to_string())
    }
}

impl From<simplicity::types::Error> for Error {
    fn from(error: simplicity::types::Error) -> Self {
        Self::SimplicityTypeError(error.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const FILE: &str = r#"let a1: List<u32, 5> = None;
let x: u32 = Left(
    Right(0)
);"#;
    const EMPTY_FILE: &str = "";

    #[test]
    fn display_single_line() {
        let error = Error::ListBoundPow2(5)
            .with_span(Span::new(Position::new(1, 14), Position::new(1, 20)))
            .with_file(Arc::from(FILE));
        let expected = r#"
  |
1 | let a1: List<u32, 5> = None;
  |              ^^^^^^ Expected a power of two greater than one (2, 4, 8, 16, 32, ...) as list bound, found 5"#;
        assert_eq!(&expected[1..], &error.to_string());
    }

    #[test]
    fn display_multi_line() {
        let error = Error::CannotParse(
            "Expected value of type `u32`, got `Either<Either<_, u32>, _>`".to_string(),
        )
        .with_span(Span::new(Position::new(2, 21), Position::new(4, 2)))
        .with_file(Arc::from(FILE));
        let expected = r#"
  |
2 | let x: u32 = Left(
3 |     Right(0)
4 | );
  | ^^^^^^^^^^^^^^^^^^ Cannot parse: Expected value of type `u32`, got `Either<Either<_, u32>, _>`"#;
        assert_eq!(&expected[1..], &error.to_string());
    }

    #[test]
    fn display_entire_file() {
        let error = Error::CannotParse("This span covers the entire file".to_string())
            .with_span(Span::from(FILE))
            .with_file(Arc::from(FILE));
        let expected = r#"
  |
1 | let a1: List<u32, 5> = None;
2 | let x: u32 = Left(
3 |     Right(0)
4 | );
  | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ Cannot parse: This span covers the entire file"#;
        assert_eq!(&expected[1..], &error.to_string());
    }

    #[test]
    fn display_no_file() {
        let error = Error::CannotParse("This error has no file".to_string())
            .with_span(Span::from(EMPTY_FILE));
        let expected = "Cannot parse: This error has no file";
        assert_eq!(&expected, &error.to_string());

        let error = Error::CannotParse("This error has no file".to_string())
            .with_span(Span::new(Position::new(1, 1), Position::new(2, 2)));
        assert_eq!(&expected, &error.to_string());
    }

    #[test]
    fn display_empty_file() {
        let error = Error::CannotParse("This error has an empty file".to_string())
            .with_span(Span::from(EMPTY_FILE))
            .with_file(Arc::from(EMPTY_FILE));
        let expected = "Cannot parse: This error has an empty file";
        assert_eq!(&expected, &error.to_string());

        let error = Error::CannotParse("This error has an empty file".to_string())
            .with_span(Span::new(Position::new(1, 1), Position::new(2, 2)))
            .with_file(Arc::from(EMPTY_FILE));
        assert_eq!(&expected, &error.to_string());
    }
}
