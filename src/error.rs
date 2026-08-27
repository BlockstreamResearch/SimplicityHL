use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::ffi::OsStr;
use std::fmt;
use std::io::{self, IsTerminal, Write};
use std::ops::Range;
use std::path::PathBuf;
use std::sync::Arc;

use chumsky::error::Error as ChumskyError;
use chumsky::input::ValueInput;
use chumsky::label::LabelError;
use chumsky::span::SimpleSpan;
use chumsky::util::MaybeRef;
use chumsky::DefaultExpected;

use ariadne::{Cache, Color, Config, Label as AriadneLabel, Report, ReportKind, Source};

use itertools::Itertools;

use crate::driver::{SourceMap, CRATE_STR, MAIN_MODULE};
use crate::lexer::Token;
use crate::parse::MatchPattern;
use crate::str::{AliasName, FunctionName, Identifier, JetName, ModuleName, WitnessName};
use crate::types::{ResolvedType, UIntType};
use crate::unstable::UnstableFeature;

/// Area that an object spans inside a file.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Span {
    /// Identifier of the source file this span refers to.
    pub file_id: usize,
    /// Position where the object starts, inclusively.
    pub start: usize,
    /// Position where the object ends, exclusively.
    pub end: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
}

/// A span-anchored annotation attached to a diagnostic.
///
/// Used only for secondary highlights. The primary location is carried
/// by [`Diagnostic::location`].
#[derive(Debug, Clone)]
pub struct Label {
    pub span: Span,
    pub message: String,
}

/// Where the diagnostic points.
///
/// - `Code`: Inside a file, at a specific span. Normal case.
/// - `File`: The whole file. E.g. "main must be in the entry file".
/// - `Global`: The whole build. E.g. dependency cycle, missing crate root.
#[derive(Debug, Clone)]
pub enum Location {
    Code(Span),
    File(usize),
    Global,
}

impl Span {
    pub(crate) const DUMMY: Self = Self::new(MAIN_MODULE, 0..0);

    /// Create a new span.
    ///
    /// ## Panics
    ///
    /// Panics if `start > end`.
    pub const fn new(file_id: usize, range: Range<usize>) -> Self {
        assert!(range.start <= range.end, "Start cannot come after end");
        Self {
            file_id,
            start: range.start,
            end: range.end,
        }
    }

    /// EOF sentinel: zero-width position at the end of `file_id`'s contents
    pub const fn eof(file_id: usize, source_len: usize) -> Self {
        // start == end is intentional
        Self::new(file_id, source_len..source_len)
    }

    pub const fn from_chumsky(file_id: usize, span: SimpleSpan, start: usize) -> Self {
        Self::new(file_id, span.start + start..span.end + start)
    }

    /// Return a slice from the given `file` that corresponds to the span.
    pub fn to_slice<'a>(&self, file: &'a str) -> Option<&'a str> {
        file.get(self.start..self.end)
    }
}

impl chumsky::span::Span for Span {
    type Context = usize;
    type Offset = usize;

    fn new(file_id: Self::Context, range: Range<Self::Offset>) -> Self {
        // chumsky builds an empty `span_since` over mapped token input as
        // `next_token.start .. previous_token.end`, which is inverted
        // whenever skipped trivia separates the two tokens.
        //
        // Collapse such ranges to a zero-width span at the unconsumed token's start.
        if range.start > range.end {
            return Self::new(file_id, range.start..range.start);
        }

        Self::new(file_id, range)
    }

    fn context(&self) -> Self::Context {
        self.file_id
    }

    fn start(&self) -> Self::Offset {
        self.start
    }

    fn end(&self) -> Self::Offset {
        self.end
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl From<SimpleSpan<usize, usize>> for Span {
    fn from(span: SimpleSpan<usize, usize>) -> Self {
        Self::new(span.context, span.start..span.end)
    }
}

impl From<&str> for Span {
    fn from(s: &str) -> Self {
        Span::new(crate::driver::MAIN_MODULE, 0..s.len())
    }
}

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for Span {
    fn arbitrary(_: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        Ok(Self::DUMMY)
    }
}

/// Helper trait to convert `Result<T, E>` into `Result<T, Diagnostic>`.
pub trait WithSpan<T> {
    /// Update the result with the affected span.
    fn with_span<S: Into<Span>>(self, span: S) -> Result<T, Diagnostic>;
}

impl<T, E: Into<Error>> WithSpan<T> for Result<T, E> {
    fn with_span<S: Into<Span>>(self, span: S) -> Result<T, Diagnostic> {
        self.map_err(|e| e.into().with_span(span.into()))
    }
}

/// A single diagnostic ready to be rendered.
///
/// Records *what* went wrong, *where*, and any extra context that helps
/// the user act on it.
#[derive(Debug, Clone)]
pub struct Diagnostic {
    /// How the diagnostic is classified for display and exit code.
    severity: Severity,

    /// The error that occurred.
    ///
    /// Wrapped in a `Box` to keep the [`Error`] struct small on the stack,
    /// ensuring cheap moves when returning errors inside a `Result`.
    error: Box<Error>,

    location: Location,

    /// Additional highlights attached to secondary spans.
    /// Used for "X conflicts with Y" style errors. For example
    /// a "redefined function" error.
    secondary: Vec<Label>,

    /// Free-form notes shown below the code snippet.
    notes: Vec<Arc<str>>,

    /// A single actionable suggestion, if one applies.
    help: Option<Arc<str>>,
}

impl Diagnostic {
    /// Create a new error with context.
    pub fn new(error: Error, span: Span) -> Self {
        Self {
            severity: Severity::Error,
            error: Box::new(error),
            location: Location::Code(span),
            secondary: Vec::new(),
            notes: Vec::new(),
            help: None,
        }
    }

    /// Create a warning attached to a code span.
    pub fn warning(error: Error, span: Span) -> Self {
        Self {
            severity: Severity::Warning,
            ..Self::new(error, span)
        }
    }

    pub fn file(error: Error, file_id: usize) -> Self {
        Self {
            location: Location::File(file_id),
            ..Self::new(error, Span::DUMMY)
        }
    }

    pub fn global(error: Error) -> Self {
        Self {
            location: Location::Global,
            ..Self::new(error, Span::DUMMY)
        }
    }

    pub fn with_secondary(mut self, span: Span, message: impl Into<String>) -> Self {
        self.secondary.push(Label {
            span,
            message: message.into(),
        });
        self
    }

    pub fn with_note(mut self, note: impl Into<Arc<str>>) -> Self {
        self.notes.push(note.into());
        self
    }

    pub fn with_help(mut self, help: impl Into<Arc<str>>) -> Self {
        self.help = Some(help.into());
        self
    }

    pub fn severity(&self) -> &Severity {
        &self.severity
    }

    pub fn error(&self) -> &Error {
        &self.error
    }

    /// Returns where the diagnostic points: a code span, a whole file, or
    /// the whole build.
    pub fn location(&self) -> &Location {
        &self.location
    }

    /// Returns the secondary labels, additional highlights that give
    /// context for the primary error.
    pub fn secondary(&self) -> &[Label] {
        &self.secondary
    }

    /// Returns the free-form notes attached to this diagnostic.
    pub fn notes(&self) -> &[Arc<str>] {
        &self.notes
    }

    /// Returns the actionable suggestion, if one was set.
    pub fn help(&self) -> &Option<Arc<str>> {
        &self.help
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // A bare Diagnostic has no source text; that lives in the SourceMap.
        // Rich, span-highlighted output is produced by DiagnosticManager::render.
        write!(f, "{}", self.error)
    }
}

impl From<Diagnostic> for Error {
    fn from(diag: Diagnostic) -> Self {
        *diag.error
    }
}

impl From<Diagnostic> for String {
    fn from(diag: Diagnostic) -> Self {
        diag.to_string()
    }
}

impl std::error::Error for Diagnostic {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.error.source()
    }
}

/// Implementation of traits for using inside `chumsky` parsers.
impl<'tokens, 'src: 'tokens, I> ChumskyError<'tokens, I> for Diagnostic
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = Span>,
{
    fn merge(self, other: Self) -> Self {
        match (self.error.as_ref(), other.error.as_ref()) {
            (Error::Grammar { .. }, Error::Grammar { .. }) => other,
            (Error::Grammar { .. }, _) => other,
            (_, Error::Grammar { .. }) => self,
            _ => other,
        }
    }
}

impl<'tokens, 'src: 'tokens, I> LabelError<'tokens, I, DefaultExpected<'tokens, Token<'src>>>
    for Diagnostic
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

        Self::new(
            Error::Syntax {
                expected: expected_tokens,
                label: None,
                found: found_string,
            },
            span,
        )
    }
}

impl<'tokens, 'src: 'tokens, I> LabelError<'tokens, I, &'tokens str> for Diagnostic
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

        Self::new(
            Error::Syntax {
                expected: expected_strings,
                label: None,
                found: found_string,
            },
            span,
        )
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

/// Collects diagnostics emitted during a single compilation and renders
/// them against the source files they refer to.
#[derive(Debug, Clone, Default)]
pub struct DiagnosticManager {
    diags: Vec<Diagnostic>,
    error_count: usize,
    sources: Option<SourceMap>,
}

impl DiagnosticManager {
    pub fn new() -> Self {
        Self::default()
    }

    pub(crate) fn with_sources(&mut self, sources: SourceMap) {
        self.sources = Some(sources);
    }

    /// Extend existing errors with specific `Diagnostic`.
    pub fn push(&mut self, diag: Diagnostic) {
        if matches!(diag.severity, Severity::Error) {
            self.error_count += 1;
        }

        self.diags.push(diag);
    }

    /// Appends new errors, tagging them with the provided source context.
    /// Automatically handles both single-file and multi-file environments.
    pub fn extend(&mut self, iter: impl IntoIterator<Item = Diagnostic>) {
        for diag in iter {
            self.push(diag);
        }
    }

    pub fn has_errors(&self) -> bool {
        self.error_count > 0
    }

    pub fn error_count(&self) -> usize {
        self.error_count
    }

    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diags
    }

    pub fn sources(&self) -> Option<&SourceMap> {
        self.sources.as_ref()
    }

    // TODO(perf): rebuild-per-call cache + sources clone.
    // Revisit after diagnostic refactor lands.
    /// Render all diagnostics to `w` using `ariadne`.
    pub fn render(&self, with_color: bool, mut w: impl Write) -> std::io::Result<()> {
        // Empty-SourceMap fallback.
        //
        // The only caller that hits this branch is the legacy one-file program
        // flow, which bypasses the driver. All modern paths (LSP, `simc`,
        // Simplex, and the Web build via `TemplateProgram::flatten`) register
        // sources with the driver and hit the `RenderCache`-based render below.
        //
        // Legacy callers get message-only output — no source snippets, no
        // line/column info. Once the legacy flow migrates or is removed, this
        // branch can go.
        let Some(sources) = self.sources() else {
            return write!(w, "{self}");
        };

        let mut cache = RenderCache::new(sources);

        for diag in &self.diags {
            render_one(diag, &mut cache, with_color, &mut w)?;
        }

        Ok(())
    }

    pub fn render_to_string(&self) -> String {
        let mut buf = Vec::new();
        self.render(false, &mut buf)
            .expect("writing to Vec never fails");
        String::from_utf8(buf).expect("ariadne output is valid utf-8")
    }
}

impl fmt::Display for DiagnosticManager {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Message-only, no source snippets. Callers that want rich output
        // with span highlighting must call `render` or `render_to_string`
        // explicitly, because `fmt::Formatter` can't carry the color flag
        // or surface I/O errors.
        for diag in &self.diags {
            writeln!(f, "{diag}")?;
        }
        Ok(())
    }
}

impl std::error::Error for DiagnosticManager {}

/// Lazy ariadne cache that memoises `Source` construction across labels
/// within a single `render` call.
#[derive(Debug)]
pub(crate) struct RenderCache<'a> {
    pub(crate) sources: &'a SourceMap,
    built: HashMap<usize, Source<Arc<str>>>,
}

impl<'a> RenderCache<'a> {
    fn new(sources: &'a SourceMap) -> Self {
        Self {
            sources,
            built: HashMap::new(),
        }
    }
}

impl<'a> Cache<usize> for RenderCache<'a> {
    type Storage = Arc<str>;

    fn fetch(&mut self, id: &usize) -> Result<&ariadne::Source<Arc<str>>, Box<dyn fmt::Debug>> {
        match self.built.entry(*id) {
            Entry::Occupied(e) => Ok(e.into_mut()),

            Entry::Vacant(e) => {
                let Some(content) = self.sources.content(*id) else {
                    return Err(Box::new(format!("unknown file_id: {id}")));
                };

                Ok(e.insert(Source::from(content)))
            }
        }
    }

    fn display<'b>(&self, id: &'b usize) -> Option<Box<dyn std::fmt::Display + 'b>> {
        self.sources.path(*id).map(|path| {
            Box::new(path.as_path().display().to_string()) as Box<dyn fmt::Display + 'b>
        })
    }
}

/// Pure color-decision logic.
fn decide_color(clicolor_force: Option<&OsStr>, no_color: Option<&OsStr>, is_tty: bool) -> bool {
    let zero = OsStr::new("0");

    if let Some(v) = clicolor_force {
        if !v.is_empty() && v != zero {
            return true;
        }
    }
    if let Some(v) = no_color {
        if !v.is_empty() {
            return false;
        }
    }
    is_tty
}

/// Whether the given stream should be rendered with ANSI color.
///
/// Precedence: `CLICOLOR_FORCE` (non-empty, non-`"0"`) then force on;
/// `NO_COLOR` (non-empty, per <https://no-color.org>) then force off;
/// otherwise follow the stream's TTY status.
pub fn should_color<S: IsTerminal>(stream: &S) -> bool {
    decide_color(
        std::env::var_os("CLICOLOR_FORCE").as_deref(),
        std::env::var_os("NO_COLOR").as_deref(),
        stream.is_terminal(),
    )
}

fn render_one(
    diag: &Diagnostic,
    cache: &mut RenderCache,
    with_color: bool,
    w: &mut impl Write,
) -> std::io::Result<()> {
    match &diag.location {
        Location::Code(span) => render_code(diag, *span, cache, with_color, w),
        Location::File(file_id) => render_file(diag, *file_id, cache.sources, w),
        Location::Global => render_global(diag, w),
    }
}

fn render_code(
    diag: &Diagnostic,
    span: Span,
    cache: &mut RenderCache,
    with_color: bool,
    w: &mut impl Write,
) -> std::io::Result<()> {
    if cache.sources.content(span.file_id).is_none() {
        return render_missing_source(diag, span.file_id, w);
    };

    let span_range = span.start..span.end;

    let mut report = Report::build(kind(diag.severity), (span.file_id, span_range.clone()))
        .with_config(
            Config::default()
                .with_index_type(ariadne::IndexType::Byte)
                .with_char_set(if with_color {
                    ariadne::CharSet::Unicode
                } else {
                    ariadne::CharSet::Ascii
                })
                .with_color(with_color),
        )
        .with_message(diag.error.to_string())
        .with_label(
            // Consider polishing adding `with_message("")` string
            AriadneLabel::new((span.file_id, span_range)).with_color(Color::Red),
        );

    for label in &diag.secondary {
        if cache.sources.content(label.span.file_id).is_none() {
            debug_assert!(
                false,
                "secondary label references unregistered file_id {}",
                label.span.file_id
            );
            continue;
        };

        report = report.with_label(
            AriadneLabel::new((label.span.file_id, label.span.start..label.span.end))
                .with_message(&label.message)
                .with_color(Color::Blue),
        );
    }

    for note in &diag.notes {
        report = report.with_note(note.as_ref());
    }

    if let Some(help) = &diag.help {
        report = report.with_help(help);
    }

    report.finish().write(cache, &mut *w)
}

fn render_file(
    diag: &Diagnostic,
    file_id: usize,
    sources: &SourceMap,
    w: &mut impl Write,
) -> std::io::Result<()> {
    let Some(path) = sources.path(file_id) else {
        return render_missing_source(diag, file_id, w);
    };

    writeln!(
        w,
        "{}: {}\n --> {}",
        severity_prefix(diag.severity),
        diag.error,
        path.as_path().display()
    )?;
    write_notes_and_help(diag, w)
}

fn render_global(diag: &Diagnostic, w: &mut impl Write) -> std::io::Result<()> {
    writeln!(w, "{}: {}", severity_prefix(diag.severity), diag.error)?;
    write_notes_and_help(diag, w)
}

/// Fallback for diagnostics whose file isn't in the `SourceMap`.
///
/// Calling this function *is* the bug signal: if we got here, some pass
/// constructed a `Span` with a `file_id` that was never registered. The
/// `debug_assert!` fires in dev/test builds so the source-map bug is
/// caught early; in release we degrade the diagnostic to message-only
/// rather than panicking in the error-rendering path.
fn render_missing_source(diag: &Diagnostic, file_id: usize, w: &mut impl Write) -> io::Result<()> {
    debug_assert!(
        false,
        "diagnostic references unregistered file_id: {file_id}, check span construction"
    );

    writeln!(w, "{}: {}", severity_prefix(diag.severity), diag.error)?;
    writeln!(
        w,
        " = note: (internal) source for file_id: {file_id} not registered; snippet unavailable"
    )?;

    write_notes_and_help(diag, w)
}

fn write_notes_and_help(diag: &Diagnostic, w: &mut impl Write) -> io::Result<()> {
    for note in &diag.notes {
        writeln!(w, " = note: {note}")?;
    }

    if let Some(help) = &diag.help {
        writeln!(w, " = help: {help}")?;
    }

    Ok(())
}

fn kind(sev: Severity) -> ReportKind<'static> {
    match sev {
        Severity::Error => ReportKind::Error,
        Severity::Warning => ReportKind::Warning,
    }
}

fn severity_prefix(sev: Severity) -> &'static str {
    match sev {
        Severity::Error => "error",
        Severity::Warning => "warning",
    }
}

// TODO: Add file context to `UnresolvedItem`, `PrivateItem`, and `DuplicateItem` errors.
/// An individual error.
///
/// Records _what_ happened but not where.
#[derive(Debug, Clone)]
pub enum Error {
    UnstableFeature {
        feature: UnstableFeature,
    },
    InvalidSimcVersionSyntax {
        err: String,
    },
    SimcVersionMismatch {
        required: String,
        current: String,
    },
    MalformedSimcDirective,
    ReservedSimcKeyword,
    DependencyPathNotFound {
        path: PathBuf,
    },
    DependencyNotADirectory {
        path: PathBuf,
    },
    ReservedDependencyKeyword {
        keyword: String,
    },
    DuplicateDependencyAlias {
        alias: String,
        context: String,
    },
    LinearizationCycleDetected {
        deps: Vec<String>,
    },
    InvalidDependencyIdentifier {
        alias: String,
    },
    Internal {
        msg: String,
    },
    UnknownLibrary {
        name: String,
    },
    ArraySizeNonZero {
        size: usize,
    },
    ListBoundPow2 {
        bound: usize,
    },
    BitStringPow2 {
        len: usize,
    },
    CannotParse {
        msg: String,
    },
    Grammar {
        msg: String,
    },
    Syntax {
        expected: Vec<String>,
        label: Option<String>,
        found: Option<String>,
    },
    IncompatibleMatchArms {
        first: Box<MatchPattern>,
        second: Box<MatchPattern>,
    },
    // TODO: Remove CompileError once SimplicityHL has a type system
    // The SimplicityHL compiler should never produce ill-typed Simplicity code
    // The compiler can only be this precise if it knows a type system at least as expressive as Simplicity's
    CannotCompile {
        source: simplicity::types::Error,
    },
    ParseInt {
        source: std::num::ParseIntError,
    },
    ParseCrateInt {
        source: crate::num::ParseIntError,
    },
    JetDoesNotExist {
        name: JetName,
    },
    InvalidCast {
        source: ResolvedType,
        target: ResolvedType,
    },
    FileNotFound {
        filename: PathBuf,
    },
    ExternalFileNotFound {
        lib: String,
        filename: PathBuf,
    },
    LocalFileImportedAsExternal {
        path: PathBuf,
    },
    RedefinedItem {
        name: String,
    },
    UnresolvedItem {
        name: String,
    },
    PrivateItem {
        name: String,
    },
    MissingCrateKeyword,
    MainNoInputs,
    MainNoOutput,
    MainRequired,
    MainOutOfEntryFile,
    MainCannotBePublic,
    MainCannotBeAlias,
    FunctionRedefined {
        name: FunctionName,
    },
    FunctionUndefined {
        name: FunctionName,
    },
    InvalidNumberOfArguments {
        expected: usize,
        found: usize,
    },
    FunctionNotFoldable {
        name: FunctionName,
    },
    FunctionNotLoopable {
        name: FunctionName,
    },
    ExpressionUnexpectedType {
        ty: ResolvedType,
    },
    ExpressionTypeMismatch {
        expected: ResolvedType,
        found: ResolvedType,
    },
    ExpressionNotConstant,
    IntegerOutOfBounds {
        ty: UIntType,
    },
    UndefinedVariable {
        identifier: Identifier,
    },
    RedefinedAlias {
        name: AliasName,
    },
    RedefinedAliasAsBuiltin {
        name: AliasName,
    },
    UndefinedAlias {
        name: AliasName,
    },
    DuplicateAlias {
        name: String,
    },
    VariableReuseInPattern {
        identifier: Identifier,
    },
    WitnessReused {
        name: WitnessName,
    },
    WitnessMissing {
        name: WitnessName,
    },
    WitnessTypeMismatch {
        name: WitnessName,
        declared: ResolvedType,
        assigned: ResolvedType,
    },
    WitnessReassigned {
        name: WitnessName,
    },
    WitnessOutsideMain,
    ModuleRedefined {
        name: ModuleName,
    },
    ModuleNotFound {
        name: ModuleName,
    },
    ModuleIsPrivate {
        name: ModuleName,
    },
    ArgumentMissing {
        name: WitnessName,
    },
    ArgumentTypeMismatch {
        name: WitnessName,
        declared: ResolvedType,
        assigned: ResolvedType,
    },
    PaddingSizeZero,
    PaddingSizeTooLarge {
        size: usize,
        max: usize,
    },
}

#[rustfmt::skip]
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::UnstableFeature { feature } => write!(
                f,
                "The '{feature}' feature is not enabled.\nEnable it with: -Z {feature}"
            ),
            Error::InvalidSimcVersionSyntax { err } => {
                write!(f, "Invalid version requirement in `simc` directive: {err}")
            }
            Error::SimcVersionMismatch { required, current } => write!(
                f,
                "Incompatible compiler version: file requires `{required}`, but the compiler is `{current}`. Update the compiler or the `simc` directive."
            ),
            Error::MalformedSimcDirective => write!(
                f,
                "Malformed compiler version directive: expected `simc \"<version>\";`"
            ),
            Error::ReservedSimcKeyword => write!(
                f,
                "`simc` is reserved for the compiler version directive, which must be the first item in the file and may appear at most once"
            ),
            Error::DependencyPathNotFound { path } => write!(
                f,
                "Path not found: {}", path.display()
            ),
            Error::DependencyNotADirectory { path } => write!(
                f,
                "Path must be a directory: {}", path.display()
            ),
            Error::ReservedDependencyKeyword { keyword } => write!(
                f,
                "The '{keyword}' keyword is reserved and cannot be manually mapped. Use the builder's context definitions instead."
            ),
            Error::DuplicateDependencyAlias { alias, context } => write!(
                f,
                "Duplicate dependency mapping: alias '{alias}' is defined multiple times for context '{context}'"
            ),
            Error::LinearizationCycleDetected { deps } => write!(
                f,
                "Circular dependency detected: {:?}", deps.join(" -> ")
            ),
            Error::InvalidDependencyIdentifier { alias } => write!(
                f,
                "Invalid dependency alias '{alias}': must be a valid identifier and not a reserved keyword"
            ),
            Error::Internal { msg } => write!(
                f,
                "INTERNAL ERROR: {msg}"
            ),
            Error::UnknownLibrary { name } => write!(
                f,
                "Unknown module or library '{name}'"
            ),
            Error::ArraySizeNonZero { size } => write!(
                f,
                "Expected a non-negative integer as array size, found {size}"
            ),
            Error::ListBoundPow2 { bound } => write!(
                f,
                "Expected a power of two greater than one (2, 4, 8, 16, 32, ...) as list bound, found {bound}"
            ),
            Error::BitStringPow2 { len } => write!(
                f,
                "Expected a valid bit string length (1, 2, 4, 8, 16, 32, 64, 128, 256), found {len}"
            ),
            Error::CannotParse{ msg } => write!(
                f,
                "Cannot parse: {msg}"
            ),
            Error::Grammar{ msg } => write!(
                f,
                "Grammar error: {msg}"
            ),
            Error::FileNotFound { filename: path } => write!(
                f,
                "Local file `{}` not found", path.to_string_lossy()
            ),
            Error::ExternalFileNotFound { lib, filename: path } => write!(
                f,
                "File `{}` not found in external library `{}`", path.to_string_lossy(), lib
            ),
            Error::LocalFileImportedAsExternal { path } => write!(
                f,
                "File `{}` is part of the local project and must be imported using the `crate::` prefix", path.to_string_lossy()
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
            Error::IncompatibleMatchArms { first, second} => write!(
                f,
                "Match arm `{first}` is incompatible with arm `{second}`"
            ),
            Error::CannotCompile{ .. } => write!(
                f,
                "Failed to compile to Simplicity"
            ),
            Error::ParseInt { .. } | Error::ParseCrateInt { .. } => write!(f, "Integer parsing error"),
            Error::JetDoesNotExist { name } => write!(
                f,
                "Jet `{name}` does not exist"
            ),
            Error::InvalidCast { source, target } => write!(
                f,
                "Cannot cast values of type `{source}` as values of type `{target}`"
            ),
            Error::MissingCrateKeyword => write!(
                f,
                "Imports must begin with the `{CRATE_STR}` keyword in single-file programs",
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
            Error::MainOutOfEntryFile => write!(
                f,
                "The 'main' function must be defined in the entry point file"
            ),
            Error::MainCannotBePublic => write!(
                f,
                "Main function cannot be public"
            ),
            Error::MainCannotBeAlias => write!(
                f,
                "Main function cannot be alias",
            ),
            Error::FunctionRedefined { name } => write!(
                f,
                "Function `{name}` was defined multiple times"
            ),
            Error::FunctionUndefined { name } => write!(
                f,
                "Function `{name}` was called but not defined"
            ),
            Error::RedefinedItem { name } => write!(
                f,
                "Item `{name}` was defined multiple times"
            ),
            Error::UnresolvedItem { name } => write!(
                f,
                "Item `{name}` could not be found"
            ),
            Error::PrivateItem { name } => write!(
                f,
                "Item `{name}` is private"
            ),
            Error::InvalidNumberOfArguments { expected, found } => write!(
                f,
                "Expected {expected} arguments, found {found} arguments"
            ),
            Error::FunctionNotFoldable { name } => write!(
                f,
                "Expected a signature like `fn {name}(element: E, accumulator: A) -> A` for a fold"
            ),
            Error::FunctionNotLoopable { name } => write!(
                f,
                "Expected a signature like `fn {name}(accumulator: A, context: C, counter u{{1,2,4,8,16}}) -> Either<B, A>` for a for-while loop"
            ),
            Error::ExpressionUnexpectedType { ty } => write!(
                f,
                "Expected expression of type `{ty}`; found something else"
            ),
            Error::ExpressionTypeMismatch { expected, found } => write!(
                f,
                "Expected expression of type `{expected}`, found type `{found}`"
            ),
            Error::ExpressionNotConstant => write!(
                f,
                "Expression cannot be evaluated at compile time"
            ),
            Error::IntegerOutOfBounds { ty } => write!(
                f,
                "Value is out of bounds for type `{ty}`"
            ),
            Error::UndefinedVariable { identifier } => write!(
                f,
                "Variable `{identifier}` is not defined"
            ),
            Error::RedefinedAlias { name } => write!(
                f,
                "Type alias `{name}` was defined multiple times"
            ),
            Error::RedefinedAliasAsBuiltin { name } => write!(
                f,
                "Type alias `{name}` is already exists as built-in alias"
            ),
            Error::UndefinedAlias { name } => write!(
                f,
                "Type alias `{name}` is not defined"
            ),
            Error::DuplicateAlias { name } => write!(
                f,
                "The alias `{name}` was defined multiple times"
            ),
            Error::VariableReuseInPattern { identifier } => write!(
                f,
                "Variable `{identifier}` is used twice in the pattern"
            ),
            Error::WitnessReused { name } => write!(
                f,
                "Witness `{name}` has been used before somewhere in the program"
            ),
            Error::WitnessMissing { name } => write!(
                f,
                "Missing witness for `{name}`"
            ),
            Error::WitnessTypeMismatch { name, declared, assigned } => write!(
                f,
                "Witness `{name}` was declared with type `{declared}` but its assigned value is of type `{assigned}`"
            ),
            Error::WitnessReassigned { name } => write!(
                f,
                "Witness `{name}` has already been assigned a value"
            ),
            Error::WitnessOutsideMain => write!(
                f,
                "Witness expressions are not allowed outside the `main` function"
            ),
            Error::ModuleRedefined { name } => write!(
                f,
                "Module `{name}` was defined multiple times"
            ),
            Error::ModuleNotFound { name } => write!(
                f,
                "Module `{name}` not found"
            ),
            Error::ModuleIsPrivate { name } => write!(
                f,
                "Module `{name}` is private",
            ),
            Error::ArgumentMissing { name } => write!(
                f,
                "Parameter `{name}` is missing an argument"
            ),
            Error::ArgumentTypeMismatch { name, declared, assigned } => write!(
                f,
                "Parameter `{name}` was declared with type `{declared}` but its assigned argument is of type `{assigned}`"
            ),
            Error::PaddingSizeZero => write!(f, "Padding size cannot be zero"),
            Error::PaddingSizeTooLarge { size, max } => write!(
                f,
                "Expected a padding size of at most {max}, found {size}"
            ),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::ParseInt { source } => Some(source),
            Error::ParseCrateInt { source } => Some(source),
            Error::CannotCompile { source } => Some(source),
            _ => None,
        }
    }
}

impl Error {
    /// Update the error with the affected span.
    pub fn with_span(self, span: Span) -> Diagnostic {
        Diagnostic::new(self, span)
    }
}

impl From<std::num::ParseIntError> for Error {
    fn from(error: std::num::ParseIntError) -> Self {
        Self::ParseInt { source: error }
    }
}

impl From<crate::num::ParseIntError> for Error {
    fn from(error: crate::num::ParseIntError) -> Self {
        Self::ParseCrateInt { source: error }
    }
}

impl From<simplicity::types::Error> for Error {
    fn from(error: simplicity::types::Error) -> Self {
        Self::CannotCompile { source: error }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::driver::MAIN_MODULE;

    impl Span {
        pub const fn new_in_default_file(range: Range<usize>) -> Self {
            Self::new(MAIN_MODULE, range)
        }
    }

    #[test]
    fn has_errors_ignores_warnings() {
        let mut m = DiagnosticManager::new();

        let warning = Diagnostic::warning(Error::MainNoInputs, Span::DUMMY);
        m.push(warning);
        assert!(!m.has_errors());

        let error = Diagnostic::new(Error::MainNoInputs, Span::DUMMY);
        m.push(error);
        assert!(m.has_errors());
    }

    #[test]
    fn with_span_attaches_location() {
        let result: Result<(), Error> = Err(Error::MainRequired);
        let diag = result.with_span(Span::new(0, 5..10)).unwrap_err();
        assert!(matches!(diag.location(), Location::Code(s) if s.start == 5 && s.end == 10));
    }
}

#[cfg(test)]
mod render_tests {
    use super::*;

    use crate::driver::MAIN_MODULE;
    use crate::resolution::tests::canon;
    use crate::source::CanonSourceFile;
    use crate::test_utils::TempWorkspace;

    use std::ffi::OsStr;
    use std::sync::Arc;

    const CONTENT: &str = "let a1: List<u32, 5> = None;\nlet x: u32 = Left(\n    Right(0)\n);";

    /// A [`DiagnosticManager`] over one real file named `main.simf`.
    ///
    /// The file must exist on disk because [`CanonSourceFile`] canonicalizes.
    /// Rendering never reads it back (the content lives in the [`SourceMap`])
    /// so the workspace is kept alive only so a failing test can be inspected.
    struct Fixture {
        _ws: TempWorkspace,
        manager: DiagnosticManager,
        /// Absolute path of `main.simf`, stripped from rendered output.
        abs_path: String,
    }

    impl Fixture {
        fn new(content: &str) -> Self {
            let ws = TempWorkspace::new("render");
            let path = canon(&ws.create_file("main.simf", content));
            let abs_path = path.as_path().display().to_string();

            let sources = SourceMap::with_source(CanonSourceFile::new(path, Arc::from(content)));
            let mut manager = DiagnosticManager::default();
            manager.with_sources(sources);

            Self {
                _ws: ws,
                manager,
                abs_path,
            }
        }

        fn push(&mut self, diag: Diagnostic) {
            self.manager.push(diag);
        }

        /// Render with color off, the temp-dir path replaced by `main.simf`,
        /// and trailing whitespace stripped; ariadne pads gutter-only lines.
        fn render(&self) -> String {
            self.manager
                .render_to_string()
                .replace(&self.abs_path, "main.simf")
                .lines()
                .map(str::trim_end)
                .collect::<Vec<_>>()
                .join("\n")
        }
    }

    fn expect(actual: &str, expected: &str) {
        assert_eq!(actual, expected.trim_start_matches('\n').trim_end());
    }

    fn span(range: std::ops::Range<usize>) -> Span {
        Span::new(MAIN_MODULE, range)
    }

    #[test]
    fn clicolor_force_zero_does_not_force() {
        // Regression case: CLICOLOR_FORCE=0 with non-TTY stderr must not emit escapes.
        assert!(!decide_color(Some(OsStr::new("0")), None, false));
        assert!(decide_color(Some(OsStr::new("1")), None, false));
        assert!(!decide_color(None, Some(OsStr::new("1")), true));
        assert!(decide_color(None, None, true));
        assert!(!decide_color(None, None, false));
    }

    #[test]
    fn golden_full_diagnostic() {
        let mut fixture = Fixture::new(CONTENT);
        fixture.push(
            Diagnostic::new(Error::ListBoundPow2 { bound: 5 }, span(13..19))
                .with_secondary(span(0..2), "declared here")
                .with_note("first note")
                .with_note("second note")
                .with_help("use 4 or 8"),
        );

        expect(
            &fixture.render(),
            r#"
Error: Expected a power of two greater than one (2, 4, 8, 16, 32, ...) as list bound, found 5
   ,-[main.simf:1:14]
   |
 1 | let a1: List<u32, 5> = None;
   | ^|           ^^^^^^
   |  `------------------- declared here
   |
   | Help: use 4 or 8
   |
   | Note 1: first note
   |
   | Note 2: second note
---'"#,
        );
    }

    #[test]
    fn caret_lands_on_byte_offset_after_emoji() {
        // Pins the `IndexType::Byte` decision. Under `IndexType::Char`, ariadne
        // reads our byte offset as a char offset and underlines the wrong text.
        let mut fixture = Fixture::new("/*😀*/ let a: u8 = 65536;");
        fixture.push(Diagnostic::new(
            Error::CannotParse {
                msg: "too large".into(),
            },
            span(21..26),
        ));

        expect(
            &fixture.render(),
            r#"
Error: Cannot parse: too large
   ,-[main.simf:1:19]
   |
 1 | /*😀*/ let a: u8 = 65536;
---'"#,
        );
    }

    #[test]
    fn secondary_label_message_is_forwarded() {
        let mut fixture = Fixture::new(CONTENT);

        fixture.push(
            Diagnostic::new(Error::ListBoundPow2 { bound: 5 }, span(13..19))
                .with_secondary(span(0..2), "declared here"),
        );

        assert!(fixture.render().contains("declared here"));
    }

    #[test]
    fn warning_severity_reaches_report_kind() {
        let mut fixture = Fixture::new(CONTENT);
        fixture.push(Diagnostic::warning(Error::MainNoInputs, span(0..3)));
        let out = fixture.render();

        assert!(out.contains("Warning"), "{out}");
        assert!(!out.contains("Error"), "{out}");
    }

    #[test]
    fn empty_manager_renders_nothing() {
        assert_eq!(Fixture::new(CONTENT).render(), "");
    }
}
