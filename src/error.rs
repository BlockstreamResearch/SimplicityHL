use std::fmt;
use std::ops::Range;
use std::sync::Arc;

use chumsky::error::Error as ChumskyError;
use chumsky::input::ValueInput;
use chumsky::label::LabelError;
use chumsky::text::Char;
use chumsky::util::MaybeRef;
use chumsky::DefaultExpected;

use itertools::Itertools;
use simplicity::elements;

use crate::lexer::Token;
use crate::parse::MatchPattern;
use crate::str::{AliasName, FunctionName, Identifier, JetName, ModuleName, WitnessName};
use crate::types::{ResolvedType, UIntType};
use crate::warning::WarningName;

/// Area that an object spans inside a file.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Span {
    /// Position where the object starts, inclusively.
    pub start: usize,
    /// Position where the object ends, exclusively.
    pub end: usize,
}

impl Span {
    /// A dummy span.
    #[cfg(feature = "arbitrary")]
    pub(crate) const DUMMY: Self = Self::new(0, 0);

    /// Create a new span.
    ///
    /// ## Panics
    ///
    /// Start comes after end.
    pub const fn new(start: usize, end: usize) -> Self {
        assert!(start <= end, "Start cannot come after end");
        Self { start, end }
    }

    /// Return a slice from the given `file` that corresponds to the span.
    pub fn to_slice<'a>(&self, file: &'a str) -> Option<&'a str> {
        file.get(self.start..self.end)
    }
}

impl chumsky::span::Span for Span {
    type Context = ();

    type Offset = usize;

    fn new((): Self::Context, range: Range<Self::Offset>) -> Self {
        Self {
            start: range.start,
            end: range.end,
        }
    }

    fn context(&self) -> Self::Context {}

    fn start(&self) -> Self::Offset {
        self.start
    }

    fn end(&self) -> Self::Offset {
        self.end
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)?;
        Ok(())
    }
}

impl From<chumsky::span::SimpleSpan> for Span {
    fn from(span: chumsky::span::SimpleSpan) -> Self {
        Self {
            start: span.start,
            end: span.end,
        }
    }
}

impl From<Range<usize>> for Span {
    fn from(range: Range<usize>) -> Self {
        Self::new(range.start, range.end)
    }
}

impl From<&str> for Span {
    fn from(s: &str) -> Self {
        Span::new(0, s.len())
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

/// Helper trait to update `Result<A, RichError>` with the file path for display.
pub trait WithFilePath<T> {
    /// Attach the file path (e.g. `"src/main.simf"`) to the error for `–– >` display.
    fn with_file_path<P: Into<Arc<str>>>(self, path: P) -> Result<T, RichError>;
}

impl<T> WithFilePath<T> for Result<T, RichError> {
    fn with_file_path<P: Into<Arc<str>>>(self, path: P) -> Result<T, RichError> {
        self.map_err(|e| e.with_file_path(path.into()))
    }
}

/// An error enriched with context.
///
/// Records _what_ happened and _where_.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct RichError {
    /// The error that occurred.
    error: Box<Error>,
    /// Area that the error spans inside the file.
    span: Span,
    /// File contents in which the error occurred.
    ///
    /// Required to render the source-code excerpt.
    file: Option<Arc<str>>,
    /// File path (e.g. `"src/main.simf"`) shown on the ` --> ` line.
    file_path: Option<Arc<str>>,
}

impl RichError {
    /// Create a new error with context.
    pub fn new(error: Error, span: Span) -> RichError {
        RichError {
            error: Box::new(error),
            span,
            file: None,
            file_path: None,
        }
    }

    /// Add the source file where the error occurred.
    ///
    /// Enable pretty errors.
    pub fn with_file(self, file: Arc<str>) -> Self {
        Self {
            file: Some(file),
            ..self
        }
    }

    /// Add the file path shown on the ` --> ` line (e.g. `"src/main.simf"`).
    pub fn with_file_path(self, path: Arc<str>) -> Self {
        Self {
            file_path: Some(path),
            ..self
        }
    }

    /// Constructs an error that is very unlikely to be encountered, but indicates
    /// a problem on the parsing side.
    pub fn parsing_error(reason: &str) -> Self {
        Self {
            error: Box::new(Error::CannotParse(reason.to_string())),
            span: Span::new(0, 0),
            file: None,
            file_path: None,
        }
    }

    pub fn file(&self) -> &Option<Arc<str>> {
        &self.file
    }

    pub fn error(&self) -> &Error {
        &self.error
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

pub fn get_line_col(file: &str, offset: usize) -> (usize, usize) {
    let mut line = 1;
    let mut col = 0;

    let slice = file.get(0..offset).unwrap_or_default();

    for char in slice.chars() {
        if char.is_newline() {
            line += 1;
            col = 0;
        } else {
            col += char.len_utf16();
        }
    }

    (line, col + 1)
}

/// Pre-computed source-span metrics and rendered source lines.
///
/// Centralises the line-number arithmetic and source-line iteration so that both
/// [`RichError`] display and warning formatting produce consistent output without
/// duplicating the computation.
pub(crate) struct SpanDisplay {
    /// 1-based start line of the span.
    pub start_line: usize,
    /// 1-based start column of the span.
    pub start_col: usize,
    /// Width of the line-number column (digits in the last covered line number).
    pub line_num_width: usize,
    /// Number of spaces to indent before the underline carets.
    pub underline_start: usize,
    /// Number of underline caret characters (`^`).
    pub underline_len: usize,
    /// The blank-separator line and source lines, ready to write verbatim.
    ///
    /// Format: `"  |\n1 | source line\n"` etc.
    pub lines_block: String,
}

impl SpanDisplay {
    pub fn new(file: &str, span: Span) -> Self {
        use std::fmt::Write as _;

        let (start_line, start_col) = get_line_col(file, span.start);
        let (end_line, end_col) = get_line_col(file, span.end);
        let start_line_index = start_line - 1;
        let n_spanned_lines = end_line - start_line_index;
        let line_num_width = end_line.to_string().len();

        let mut lines = file.lines().skip(start_line_index).peekable();
        let start_line_len = lines.peek().map_or(0, |l| l.len());

        let mut lines_block = String::new();
        let _ = writeln!(lines_block, "{:width$} |", " ", width = line_num_width);
        for (i, line_str) in lines.take(n_spanned_lines).enumerate() {
            let line_num = start_line_index + i + 1;
            let _ = writeln!(lines_block, "{line_num:line_num_width$} | {line_str}");
        }

        let is_multiline = end_line > start_line;
        let (underline_start, underline_len) = if is_multiline {
            (0, start_line_len)
        } else {
            (start_col, end_col - start_col)
        };

        Self {
            start_line,
            start_col,
            line_num_width,
            underline_start,
            underline_len,
            lines_block,
        }
    }
}

impl fmt::Display for RichError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\x1b[1;31merror\x1b[0m: {}", self.error)?;
        match self.file {
            Some(ref file) if !file.is_empty() => {
                let sd = SpanDisplay::new(file, self.span);
                writeln!(f)?;
                if let Some(ref path) = self.file_path {
                    writeln!(f, " --> {}:{}:{}", path, sd.start_line, sd.start_col)?;
                }
                write!(f, "{}", sd.lines_block)?;
                write!(f, "{:width$} |", " ", width = sd.line_num_width)?;
                write!(f, "{:width$}", " ", width = sd.underline_start)?;
                write!(f, "{:^<width$} ", "", width = sd.underline_len)?;
                write!(f, "{}", self.error)
            }
            _ => Ok(()),
        }
    }
}

impl std::error::Error for RichError {}

impl From<RichError> for Error {
    fn from(error: RichError) -> Self {
        *error.error
    }
}

impl From<RichError> for String {
    fn from(error: RichError) -> Self {
        error.to_string()
    }
}

/// Implementation of traits for using inside `chumsky` parsers.
impl<'tokens, 'src: 'tokens, I> ChumskyError<'tokens, I> for RichError
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
{
    fn merge(self, other: Self) -> Self {
        match (self.error.as_ref(), other.error.as_ref()) {
            (Error::Grammar(_), Error::Grammar(_)) => other,
            (Error::Grammar(_), _) => other,
            (_, Error::Grammar(_)) => self,
            _ => other,
        }
    }
}

impl<'tokens, 'src: 'tokens, I> LabelError<'tokens, I, DefaultExpected<'tokens, Token<'src>>>
    for RichError
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
{
    fn expected_found<E>(
        expected: E,
        found: Option<MaybeRef<'tokens, Token<'src>>>,
        span: Span,
    ) -> Self
    where
        E: IntoIterator<Item = DefaultExpected<'tokens, Token<'src>>>,
    {
        let expected_tokens: Vec<String> = expected
            .into_iter()
            .map(|t| match t {
                DefaultExpected::Token(maybe) => maybe.to_string(),
                DefaultExpected::Any => "anything".to_string(),
                DefaultExpected::SomethingElse => "something else".to_string(),
                DefaultExpected::EndOfInput => "end of input".to_string(),
                _ => "UNEXPECTED_TOKEN".to_string(),
            })
            .collect();

        let found_string = found.map(|t| t.to_string());

        Self {
            error: Box::new(Error::Syntax {
                expected: expected_tokens,
                label: None,
                found: found_string,
            }),
            span,
            file: None,
            file_path: None,
        }
    }
}

impl<'tokens, 'src: 'tokens, I> LabelError<'tokens, I, &'tokens str> for RichError
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
{
    fn expected_found<E>(
        expected: E,
        found: Option<MaybeRef<'tokens, Token<'src>>>,
        span: Span,
    ) -> Self
    where
        E: IntoIterator<Item = &'tokens str>,
    {
        let expected_strings: Vec<String> = expected.into_iter().map(|s| s.to_string()).collect();
        let found_string = found.map(|t| t.to_string());

        Self {
            error: Box::new(Error::Syntax {
                expected: expected_strings,
                label: None,
                found: found_string,
            }),
            span,
            file: None,
            file_path: None,
        }
    }

    fn label_with(&mut self, label: &'tokens str) {
        if let Error::Syntax {
            label: ref mut l, ..
        } = self.error.as_mut()
        {
            *l = Some(label.to_string());
        }
    }
}

#[derive(Debug, Clone, Hash)]
pub struct ErrorCollector {
    /// File contents in which the error occurred.
    file: Arc<str>,
    /// File path shown on the ` --> ` line (e.g. `"src/main.simf"`).
    file_path: Option<Arc<str>>,

    /// Collected errors.
    errors: Vec<RichError>,
}

impl ErrorCollector {
    pub fn new(file: Arc<str>) -> Self {
        Self {
            file,
            file_path: None,
            errors: Vec::new(),
        }
    }

    /// Create a collector that also knows the file path for ` --> ` display.
    pub fn new_with_path(file: Arc<str>, file_path: Arc<str>) -> Self {
        Self {
            file,
            file_path: Some(file_path),
            errors: Vec::new(),
        }
    }

    /// Extend existing errors with slice of new errors.
    pub fn update(&mut self, errors: impl IntoIterator<Item = RichError>) {
        let new_errors = errors.into_iter().map(|err| {
            let err = err.with_file(Arc::clone(&self.file));
            match self.file_path {
                Some(ref p) => err.with_file_path(Arc::clone(p)),
                None => err,
            }
        });

        self.errors.extend(new_errors);
    }

    pub fn get(&self) -> &[RichError] {
        &self.errors
    }

    pub fn is_empty(&self) -> bool {
        self.get().is_empty()
    }
}

impl fmt::Display for ErrorCollector {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for err in self.get() {
            writeln!(f, "{err}\n")?;
        }
        Ok(())
    }
}

/// An individual error.
///
/// Records _what_ happened but not where.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Error {
    ArraySizeNonZero(usize),
    ListBoundPow2(usize),
    BitStringPow2(usize),
    CannotParse(String),
    Grammar(String),
    Syntax {
        expected: Vec<String>,
        label: Option<String>,
        found: Option<String>,
    },
    IncompatibleMatchArms(MatchPattern, MatchPattern),
    // TODO: Remove CompileError once SimplicityHL has a type system
    // The SimplicityHL compiler should never produce ill-typed Simplicity code
    // The compiler can only be this precise if it knows a type system at least as expressive as Simplicity's
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
    RedefinedAlias(AliasName),
    RedefinedAliasAsBuiltin(AliasName),
    UndefinedAlias(AliasName),
    VariableReuseInPattern(Identifier),
    WitnessReused(WitnessName),
    WitnessTypeMismatch(WitnessName, ResolvedType, ResolvedType),
    WitnessReassigned(WitnessName),
    WitnessOutsideMain,
    ModuleRedefined(ModuleName),
    ArgumentMissing(WitnessName),
    ArgumentTypeMismatch(WitnessName, ResolvedType, ResolvedType),
    DeniedWarning(WarningName),
}

#[rustfmt::skip]
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::ArraySizeNonZero(size) => write!(
                f,
                "Expected a non-negative integer as array size, found {size}"
            ),
            Error::ListBoundPow2(bound) => write!(
                f,
                "Expected a power of two greater than one (2, 4, 8, 16, 32, ...) as list bound, found {bound}"
            ),
            Error::BitStringPow2(len) => write!(
                f,
                "Expected a valid bit string length (1, 2, 4, 8, 16, 32, 64, 128, 256), found {len}"
            ),
            Error::CannotParse(description) => write!(
                f,
                "Cannot parse: {description}"
            ),
            Error::Grammar(description) => write!(
                f,
                "Grammar error: {description}"
            ),
            Error::Syntax { expected, label, found } => {
                let found_text = found.clone().unwrap_or("end of input".to_string());
                match (label, expected.len()) {
                    (Some(l), _) => write!(f, "Expected {}, found {}", l, found_text),
                    (None, 1) => {
                        let exp_text = expected.first().unwrap();
                        write!(f, "Expected '{}', found '{}'", exp_text, found_text)
                    }
                    (None, 0) => write!(f, "Unexpected {}", found_text),
                    (None, _) => {
                        let exp_text = expected.iter().map(|s| format!("'{}'", s)).join(", ");
                        write!(f, "Expected one of {}, found '{}'", exp_text, found_text)
                    }
                }
            }
            Error::IncompatibleMatchArms(pattern1, pattern2) => write!(
                f,
                "Match arm `{pattern1}` is incompatible with arm `{pattern2}`"
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
            Error::RedefinedAlias(identifier) => write!(
                f,
                "Type alias `{identifier}` was defined multiple times"
            ),
            Error::RedefinedAliasAsBuiltin(identifier) => write!(
                f,
                "Type alias `{identifier}` is already exists as built-in alias"
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
            Error::DeniedWarning(warning) => write!(
                f, "Warning treated as error: {warning}"
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
        Self::CannotCompile(error.to_string())
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

    const RED_BOLD: &str = "\x1b[1;31m";
    const RESET: &str = "\x1b[0m";

    #[test]
    fn display_single_line() {
        let error = Error::ListBoundPow2(5)
            .with_span(Span::new(13, 19))
            .with_file(Arc::from(FILE));
        let msg = "Expected a power of two greater than one (2, 4, 8, 16, 32, ...) as list bound, found 5";
        let expected = format!(
            "{RED_BOLD}error{RESET}: {msg}\n  |\n1 | let a1: List<u32, 5> = None;\n  |              ^^^^^^ {msg}"
        );
        assert_eq!(expected, error.to_string());
    }

    #[test]
    fn display_single_line_with_path() {
        let error = Error::ListBoundPow2(5)
            .with_span(Span::new(13, 19))
            .with_file(Arc::from(FILE))
            .with_file_path(Arc::from("src/main.simf"));
        let msg = "Expected a power of two greater than one (2, 4, 8, 16, 32, ...) as list bound, found 5";
        let expected = format!(
            "{RED_BOLD}error{RESET}: {msg}\n --> src/main.simf:1:14\n  |\n1 | let a1: List<u32, 5> = None;\n  |              ^^^^^^ {msg}"
        );
        assert_eq!(expected, error.to_string());
    }

    #[test]
    fn display_multi_line() {
        let error = Error::CannotParse(
            "Expected value of type `u32`, got `Either<Either<_, u32>, _>`".to_string(),
        )
        .with_span(Span::new(41, FILE.len()))
        .with_file(Arc::from(FILE));
        let msg = "Cannot parse: Expected value of type `u32`, got `Either<Either<_, u32>, _>`";
        let expected = format!(
            "{RED_BOLD}error{RESET}: {msg}\n  |\n2 | let x: u32 = Left(\n3 |     Right(0)\n4 | );\n  | ^^^^^^^^^^^^^^^^^^ {msg}"
        );
        assert_eq!(expected, error.to_string());
    }

    #[test]
    fn display_entire_file() {
        let error = Error::CannotParse("This span covers the entire file".to_string())
            .with_span(Span::from(FILE))
            .with_file(Arc::from(FILE));
        let msg = "Cannot parse: This span covers the entire file";
        let expected = format!(
            "{RED_BOLD}error{RESET}: {msg}\n  |\n1 | let a1: List<u32, 5> = None;\n2 | let x: u32 = Left(\n3 |     Right(0)\n4 | );\n  | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ {msg}"
        );
        assert_eq!(expected, error.to_string());
    }

    #[test]
    fn display_no_file() {
        let error = Error::CannotParse("This error has no file".to_string())
            .with_span(Span::from(EMPTY_FILE));
        let expected = format!("{RED_BOLD}error{RESET}: Cannot parse: This error has no file");
        assert_eq!(expected, error.to_string());

        let error =
            Error::CannotParse("This error has no file".to_string()).with_span(Span::new(5, 10));
        assert_eq!(expected, error.to_string());
    }

    #[test]
    fn display_empty_file() {
        let error = Error::CannotParse("This error has an empty file".to_string())
            .with_span(Span::from(EMPTY_FILE))
            .with_file(Arc::from(EMPTY_FILE));
        let expected =
            format!("{RED_BOLD}error{RESET}: Cannot parse: This error has an empty file");
        assert_eq!(expected, error.to_string());
    }

    #[test]
    fn display_with_utf16_chars() {
        let file = "/*😀*/ let a: u8 = 65536;";
        let error = Error::CannotParse("number too large to fit in target type".to_string())
            .with_span(Span::new(21, 26))
            .with_file(Arc::from(file));
        let msg = "Cannot parse: number too large to fit in target type";
        let expected = format!(
            "{RED_BOLD}error{RESET}: {msg}\n  |\n1 | /*😀*/ let a: u8 = 65536;\n  |                    ^^^^^ {msg}"
        );
        println!("{error}");
        assert_eq!(expected, error.to_string());
    }
}
