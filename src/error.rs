use std::fmt;
use std::ops::Range;
use std::sync::Arc;

use chumsky::error::Error as ChumskyError;
use chumsky::input::ValueInput;
use chumsky::label::LabelError;
use chumsky::text::Char;
use chumsky::util::MaybeRef;
use chumsky::DefaultExpected;

use crate::lexer::Token;
use crate::parse::SyntaxErrorInfo;
use crate::source::SourceFile;

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
pub trait WithContent<T> {
    /// Update the result with the affected source file.
    ///
    /// Enable pretty errors.
    fn with_content<C: Into<Arc<str>>>(self, content: C) -> Result<T, RichError>;
}

impl<T> WithContent<T> for Result<T, RichError> {
    fn with_content<C: Into<Arc<str>>>(self, content: C) -> Result<T, RichError> {
        self.map_err(|e| e.with_content(content.into()))
    }
}

/// Helper trait to update `Result<A, RichError>` with the affected source file.
pub trait WithSource<T> {
    /// Update the result with the affected source file.
    ///
    /// Enable pretty errors.
    fn with_source<S: Into<SourceFile>>(self, source: S) -> Result<T, RichError>;
}

impl<T> WithSource<T> for Result<T, RichError> {
    fn with_source<S: Into<SourceFile>>(self, source: S) -> Result<T, RichError> {
        self.map_err(|e| e.with_source(source.into()))
    }
}

/// An error enriched with context.
///
/// Records _what_ happened and _where_.
#[derive(Debug, Clone)]
pub struct RichError {
    /// The error that occurred.
    ///
    /// Wrapped in a `Box` to keep the `RichError` struct small on the stack,
    /// ensuring cheap moves when returning errors inside a `Result`.
    error: Box<Error>,

    /// Area that the error spans inside the file.
    span: Span,

    /// File context in which the error occurred.
    ///
    /// Required to print pretty errors.
    source: Option<SourceFile>,
}

impl RichError {
    /// Create a new error with context.
    pub fn new(error: Error, span: Span) -> RichError {
        RichError {
            error: Box::new(error),
            span,
            source: None,
        }
    }

    /// Adds raw source code content to the error context.
    ///
    /// Use this when the error occurs in an environment without a backing physical file
    /// (e.g., raw string input for single-file program) to enable basic error formatting.
    pub fn with_content(self, program_content: Arc<str>) -> Self {
        Self {
            error: self.error,
            span: self.span,
            source: Some(SourceFile::anonymous(program_content)),
        }
    }

    /// Add the source file where the error occurred.
    ///
    /// Enable pretty errors.
    pub fn with_source(self, source: impl Into<SourceFile>) -> Self {
        Self {
            error: self.error,
            span: self.span,
            source: Some(source.into()),
        }
    }

    /// Constructs an error that is very unlikely to be encountered, but indicates
    /// a problem on the parsing side.
    pub fn parsing_error(reason: &str) -> Self {
        Self {
            error: Box::new(Error::ParsingError(crate::parse::Error::CannotParse {
                msg: reason.to_string(),
            })),
            span: Span::new(0, 0),
            source: None,
        }
    }

    pub fn source(&self) -> &Option<SourceFile> {
        &self.source
    }

    pub fn error(&self) -> &Error {
        &self.error
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl fmt::Display for RichError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn get_line_col(file: &str, offset: usize) -> (usize, usize) {
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

        let Some(source) = &self.source else {
            return write!(f, "{}", self.error);
        };

        let content = source.content();

        if content.is_empty() {
            return write!(f, "{}", self.error);
        }

        let (start_line, start_col) = get_line_col(&content, self.span.start);
        let (end_line, end_col) = get_line_col(&content, self.span.end);

        let start_line_index = start_line - 1;

        let n_spanned_lines = end_line - start_line_index;
        let line_num_width = end_line.to_string().len();

        if let Some(name) = source.name() {
            writeln!(
                f,
                "{:>width$}--> {}:{}:{}",
                "",
                name.display(),
                start_line,
                start_col,
                width = line_num_width
            )?;
        }

        writeln!(f, "{:width$} |", " ", width = line_num_width)?;

        let mut lines = content
            .split(|c: char| c.is_newline())
            .skip(start_line_index)
            .peekable();
        let start_line_len = lines
            .peek()
            .map_or(0, |l| l.chars().map(char::len_utf16).sum());

        for (relative_line_index, line_str) in lines.take(n_spanned_lines).enumerate() {
            let line_num = start_line_index + relative_line_index + 1;
            writeln!(f, "{line_num:line_num_width$} | {line_str}")?;
        }

        let is_multiline = end_line > start_line;

        let (underline_start, underline_length) = match is_multiline {
            true => (0, start_line_len),
            false => (start_col, (end_col - start_col).max(1)),
        };
        write!(f, "{:width$} |", " ", width = line_num_width)?;
        write!(f, "{:width$}", " ", width = underline_start)?;
        write!(f, "{:^<width$} ", "", width = underline_length)?;
        write!(f, "{}", self.error)
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
            (Error::ParsingError(crate::parse::Error::Grammar { .. }), _) => other,
            (_, Error::ParsingError(crate::parse::Error::Grammar { .. })) => self,
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
            error: Box::new(Error::ParsingError(crate::parse::Error::SyntaxError(
                SyntaxErrorInfo {
                    expected: expected_tokens,
                    label: None,
                    found: found_string,
                },
            ))),
            span,
            source: None,
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
            error: Box::new(Error::ParsingError(crate::parse::Error::SyntaxError(
                SyntaxErrorInfo {
                    expected: expected_strings,
                    label: None,
                    found: found_string,
                },
            ))),
            span,
            source: None,
        }
    }

    fn label_with(&mut self, label: &'tokens str) {
        if let Error::ParsingError(crate::parse::Error::SyntaxError(SyntaxErrorInfo {
            label: ref mut l,
            ..
        })) = self.error.as_mut()
        {
            *l = Some(label.to_string());
        }
    }
}

#[derive(Debug, Clone)]
pub struct ErrorCollector {
    /// Collected errors.
    errors: Vec<RichError>,
}

impl Default for ErrorCollector {
    fn default() -> Self {
        Self::new()
    }
}

impl ErrorCollector {
    pub fn new() -> Self {
        Self { errors: Vec::new() }
    }

    /// Extend existing errors with specific `RichError`.
    /// We assume that `RichError` contains `SourceFile`.
    pub fn push(&mut self, error: RichError) {
        self.errors.push(error);
    }

    /// Appends new errors, tagging them with the provided source context.
    /// Automatically handles both single-file and multi-file environments.
    pub fn extend(
        &mut self,
        source: impl Into<SourceFile> + Clone,
        errors: impl IntoIterator<Item = RichError>,
    ) {
        let new_errors = errors
            .into_iter()
            .map(|err| err.with_source(source.clone()));

        self.errors.extend(new_errors);
    }

    /// The same idea applies to the `extend()` function.
    pub fn extend_with_handler(
        &mut self,
        source: impl Into<SourceFile> + Clone,
        handler: &ErrorCollector,
    ) {
        self.extend(source, handler.errors.iter().cloned());
    }

    pub fn get(&self) -> &[RichError] {
        &self.errors
    }

    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
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

// TODO: Add file context to `UnresolvedItem`, `PrivateItem`, and `DuplicateItem` errors.
/// An individual error.
///
/// Records _what_ happened but not where.
#[derive(Debug, Clone)]
pub enum Error {
    Internal { msg: String },
    LexerError { msg: String },
    ParsingError(crate::parse::Error),
    AnalyzingError(crate::ast::Error),
    DriverError(crate::driver::Error),
    CompileError(crate::compile::Error),
}

#[rustfmt::skip]
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Internal { msg } => write!(
                f,
                "{msg}"
            ),
            Error::ParsingError(err) => write!(
                f,
                "{err}"
            ),
            Error::AnalyzingError(err) => write!(
                f,
                "{err}"
            ),
            Error::DriverError(err) => write!(
                f,
                "{err}"
            ),
            Error::CompileError(err) => write!(
                f,
                "{err}"
            ),
            Error::LexerError { msg } => write!(
                f,
                "{msg}"
            ),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::ParsingError(err) => Some(err),
            Error::AnalyzingError(err) => Some(err),
            Error::DriverError(err) => Some(err),
            Error::CompileError(err) => Some(err),
            _ => None,
        }
    }
}

impl Error {
    /// Update the error with the affected span.
    pub fn with_span(self, span: Span) -> RichError {
        RichError::new(self, span)
    }
}

impl From<simplicity::types::Error> for Error {
    fn from(error: simplicity::types::Error) -> Self {
        Self::CompileError(crate::compile::Error::TypeError(error))
    }
}

impl From<crate::parse::Error> for Error {
    fn from(error: crate::parse::Error) -> Self {
        Self::ParsingError(error)
    }
}

impl From<crate::ast::Error> for Error {
    fn from(error: crate::ast::Error) -> Self {
        match error {
            crate::ast::Error::Internal { msg } => Self::Internal { msg },
            _ => Self::AnalyzingError(error),
        }
    }
}

impl From<crate::driver::Error> for Error {
    fn from(error: crate::driver::Error) -> Self {
        match error {
            crate::driver::Error::Internal { msg } => Self::Internal { msg },
            _ => Self::DriverError(error),
        }
    }
}

impl From<crate::compile::Error> for Error {
    fn from(error: crate::compile::Error) -> Self {
        Self::CompileError(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::Error;

    const CONTENT: &str = r#"let a1: List<u32, 5> = None;
let x: u32 = Left(
    Right(0)
);"#;
    const EMPTY_FILE: &str = "";

    #[test]
    fn display_single_line() {
        let error = Error::ListBoundPow2 { bound: 5 }
            .with_span(Span::new(13, 19))
            .with_content(Arc::from(CONTENT));
        let expected = r#"
  |
1 | let a1: List<u32, 5> = None;
  |              ^^^^^^ Expected a power of two greater than one (2, 4, 8, 16, 32, ...) as list bound, found 5"#;
        assert_eq!(&expected[1..], &error.to_string());
    }

    #[test]
    fn display_multi_line() {
        let error = Error::CannotParse {
            msg: "Expected value of type `u32`, got `Either<Either<_, u32>, _>`".to_string(),
        }
        .with_span(Span::new(41, CONTENT.len()))
        .with_content(Arc::from(CONTENT));
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
        let error = Error::CannotParse {
            msg: "This span covers the entire file".to_string(),
        }
        .with_span(Span::from(CONTENT))
        .with_content(Arc::from(CONTENT));
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
        let error = Error::CannotParse {
            msg: "This error has no file".to_string(),
        }
        .with_span(Span::from(EMPTY_FILE));
        let expected = "Cannot parse: This error has no file";
        assert_eq!(&expected, &error.to_string());

        let error = Error::CannotParse {
            msg: "This error has no file".to_string(),
        }
        .with_span(Span::new(5, 10));
        assert_eq!(&expected, &error.to_string());
    }

    #[test]
    fn display_empty_file() {
        let error = Error::CannotParse {
            msg: "This error has an empty file".to_string(),
        }
        .with_span(Span::from(EMPTY_FILE))
        .with_content(Arc::from(EMPTY_FILE));
        let expected = "Cannot parse: This error has an empty file";
        assert_eq!(&expected, &error.to_string());
    }

    #[test]
    fn display_with_utf16_chars() {
        let file = "/*😀*/ let a: u8 = 65536;";
        let error = Error::CannotParse {
            msg: "number too large to fit in target type".to_string(),
        }
        .with_span(Span::new(21, 26))
        .with_content(Arc::from(file));

        let expected = r#"
  |
1 | /*😀*/ let a: u8 = 65536;
  |                    ^^^^^ Cannot parse: number too large to fit in target type"#;

        assert_eq!(&expected[1..], &error.to_string());
    }

    #[test]
    fn multiline_display_with_utf16_chars() {
        let file = r#"/*😀 this symbol should not break the rendering*/
let a: u8 = 65536;
let x: u32 = Left(
    Right(0)
);"#;
        let error = Error::CannotParse {
            msg: "This span covers the entire file".to_string(),
        }
        .with_span(Span::from(file))
        .with_content(Arc::from(file));

        let expected = r#"
  |
1 | /*😀 this symbol should not break the rendering*/
2 | let a: u8 = 65536;
3 | let x: u32 = Left(
4 |     Right(0)
5 | );
  | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ Cannot parse: This span covers the entire file"#;

        assert_eq!(&expected[1..], &error.to_string());
    }

    #[test]
    fn display_with_unicode_separator() {
        let file = "let a: u8 = 65536;\u{2028}let b: u8 = 0;";
        let error = Error::CannotParse {
            msg: "number too large to fit in target type".to_string(),
        }
        .with_span(Span::new(12, 17))
        .with_content(Arc::from(file));

        let expected = r#"
  |
1 | let a: u8 = 65536;
  |             ^^^^^ Cannot parse: number too large to fit in target type"#;

        assert_eq!(&expected[1..], &error.to_string());
    }

    #[test]
    fn display_span_as_point() {
        let file = "fn main()";
        let error = Error::Grammar {
            msg: "Error span at (0,0)".to_string(),
        }
        .with_span(Span::new(0, 0))
        .with_content(Arc::from(file));

        let expected = r#"
  |
1 | fn main()
  | ^ Grammar error: Error span at (0,0)"#;
        assert_eq!(&expected[1..], &error.to_string());
    }

    #[test]
    fn display_span_as_point_on_trailing_empty_line() {
        let file = "fn main(){\n    let a:\n";
        let error = Error::CannotParse {
            msg: "eof".to_string(),
        }
        .with_span(Span::new(file.len(), file.len()))
        .with_content(Arc::from(file));

        let expected = r#"
  |
3 | 
  | ^ Cannot parse: eof"#;

        assert_eq!(&expected[1..], &error.to_string());
    }

    // --- Tests with filename ---
    #[test]
    fn display_single_line_with_file() {
        let source = SourceFile::new(std::path::Path::new("src/main.simf"), Arc::from(CONTENT));
        let error = Error::ListBoundPow2 { bound: 5 }
            .with_span(Span::new(13, 19))
            .with_source(source);

        let expected = r#"
 --> src/main.simf:1:14
  |
1 | let a1: List<u32, 5> = None;
  |              ^^^^^^ Expected a power of two greater than one (2, 4, 8, 16, 32, ...) as list bound, found 5"#;
        assert_eq!(&expected[1..], &error.to_string());
    }

    #[test]
    fn display_multi_line_with_file() {
        let source = SourceFile::new(std::path::Path::new("lib/parser.simf"), Arc::from(CONTENT));
        let error = Error::CannotParse {
            msg: "Expected value of type `u32`, got `Either<Either<_, u32>, _>`".to_string(),
        }
        .with_span(Span::new(41, CONTENT.len()))
        .with_source(source);

        let expected = r#"
 --> lib/parser.simf:2:13
  |
2 | let x: u32 = Left(
3 |     Right(0)
4 | );
  | ^^^^^^^^^^^^^^^^^^ Cannot parse: Expected value of type `u32`, got `Either<Either<_, u32>, _>`"#;
        assert_eq!(&expected[1..], &error.to_string());
    }

    #[test]
    fn display_entire_file_with_file() {
        let source = SourceFile::new(
            std::path::Path::new("tests/integration.simf"),
            Arc::from(CONTENT),
        );
        let error = Error::CannotParse {
            msg: "This span covers the entire file".to_string(),
        }
        .with_span(Span::from(CONTENT))
        .with_source(source);

        let expected = r#"
 --> tests/integration.simf:1:1
  |
1 | let a1: List<u32, 5> = None;
2 | let x: u32 = Left(
3 |     Right(0)
4 | );
  | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ Cannot parse: This span covers the entire file"#;
        assert_eq!(&expected[1..], &error.to_string());
    }
}
