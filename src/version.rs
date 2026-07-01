use std::borrow::Cow;

use semver::{Version, VersionReq};

use crate::error::{Error, ErrorCollector, RichError, Span};
use crate::source::SourceFile;

/// Defines the `simc "<version>";` directive syntax
pub const DIRECTIVE_PREFIX: &str = "simc \"";
pub const DIRECTIVE_SUFFIX: &str = "\";";

/// The running compiler's version (`CARGO_PKG_VERSION`).
pub fn current_version() -> &'static str {
    env!("CARGO_PKG_VERSION")
}

/// Render a `simc "<version>";` directive line
fn directive_for(version: &str) -> String {
    format!("{DIRECTIVE_PREFIX}{version}{DIRECTIVE_SUFFIX}")
}

/// Validate the leading `simc "...";` directive against the running compiler,
/// returning the diagnostic and its span on failure. Works on raw content,
/// independent of parsing the body, so directive errors surface clearly.
pub fn check(content: &str) -> Result<(), (Error, Span)> {
    let (req_str, span) = match scan_directive(content) {
        DirectiveScan::Found { req, span } => (req, span),
        // Absence is allowed — only a present directive is enforced (the CLI warns).
        DirectiveScan::Absent => return Ok(()),
        // Report a broken directive here, rather than let it confuse the lexer.
        DirectiveScan::Malformed(span) => {
            return Err((
                Error::InvalidSimcVersionSyntax {
                    err: malformed_directive_message(),
                },
                span,
            ));
        }
        DirectiveScan::Duplicate(span) => {
            return Err((
                Error::Syntax {
                    expected: vec!["Exactly one compiler version directive".to_string()],
                    label: None,
                    found: Some("Multiple directives".to_string()),
                },
                span,
            ));
        }
        DirectiveScan::Misplaced(span) => {
            return Err((
                Error::Syntax {
                    expected: vec![
                        "the `simc` directive to be the first item in the file".to_string()
                    ],
                    label: None,
                    found: Some("a compiler version directive after program code".to_string()),
                },
                span,
            ));
        }
    };

    let required = req_str.trim();
    let req = VersionRequirement::parse(required)
        .map_err(|e| (Error::InvalidSimcVersionSyntax { err: e }, span))?;

    let current = current_version();
    let current_ver = Version::parse(current).expect("CARGO_PKG_VERSION is valid semver");
    if !req.matches(&current_ver) {
        let err = Error::SimcVersionMismatch {
            required: required.to_string(),
            current: current.to_string(),
        };
        return Err((err, span));
    }

    Ok(())
}

/// Run [`check`] on a source file and record any diagnostic in `handler`. The
/// per-file entry point used by the driver and `TemplateProgram`.
pub fn check_source<S: Into<SourceFile> + Clone>(source: &S, handler: &mut ErrorCollector) {
    let source_file: SourceFile = source.clone().into();
    if let Err((err, span)) = check(&source_file.content()) {
        handler.push(RichError::new(err, span).with_source(source_file));
    }
}

/// The CLI advisory for a file that declares no directive, or `None` when one is
/// present (a malformed one is not "absent" — it surfaces as a hard error in
/// [`check`]).
pub fn missing_directive_warning(content: &str) -> Option<String> {
    matches!(requirement_of(content), Ok(None)).then(|| {
        format!(
            "no compiler version directive; consider adding `{}`",
            directive_for(current_version())
        )
    })
}

/// Why [`requirement_of`] could not hand back a clean requirement. Only a single,
/// well-formed leading directive yields one; every other shape a file's directive can
/// take is a distinct variant here, so tooling can react without lexing the program.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DirectiveError {
    /// More than one directive in the file (at most one is allowed).
    Duplicate,
    /// A directive that appears after program code (it must be the first item).
    Misplaced,
    /// A directive-looking line that is not a well-formed `simc "...";`, or a
    /// requirement string that is not valid semver. Carries the diagnostic message.
    InvalidSyntax(String),
}

/// Cheaply read a file's declared version requirement (leading directive only, no
/// lexing), for external tooling. `Ok(None)` when absent. A malformed directive is
/// reported as [`DirectiveError::InvalidSyntax`], the same as [`check`], so a typo is
/// never silently treated as "no directive".
pub fn requirement_of(content: &str) -> Result<Option<VersionRequirement>, DirectiveError> {
    match scan_directive(content) {
        DirectiveScan::Found { req, .. } => VersionRequirement::parse(req.trim())
            .map(Some)
            .map_err(DirectiveError::InvalidSyntax),
        DirectiveScan::Absent => Ok(None),
        DirectiveScan::Malformed(_) => {
            Err(DirectiveError::InvalidSyntax(malformed_directive_message()))
        }
        DirectiveScan::Duplicate(_) => Err(DirectiveError::Duplicate),
        DirectiveScan::Misplaced(_) => Err(DirectiveError::Misplaced),
    }
}

/// A parsed directive requirement: the semver range written inside the quotes. Wraps
/// [`semver::VersionReq`] so [`Self::matches`] can apply compiler-aware pre-release
/// handling — a plain release range still accepts a pre-release build of that version.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VersionRequirement {
    req: VersionReq,
}

impl VersionRequirement {
    /// Parse a requirement string such as `>=0.6.0` or `=0.6.0`.
    pub fn parse(s: &str) -> Result<Self, String> {
        VersionReq::parse(s)
            .map(|req| VersionRequirement { req })
            .map_err(|e| e.to_string())
    }

    /// The underlying requirement, for external tooling that
    /// intersects ranges across a project's files.
    pub fn req(&self) -> &VersionReq {
        &self.req
    }

    #[allow(rustdoc::private_intra_doc_links)]
    /// Whether `version` satisfies the requirement, after pre-release
    /// normalization (see [`Self::effective_version`]).
    pub fn matches(&self, version: &Version) -> bool {
        self.req.matches(&self.effective_version(version))
    }

    /// Strip the compiler's pre-release tag (`0.6.0-rc.0` → `0.6.0`) when the
    /// requirement names no pre-release, so a release range still accepts a matching
    /// pre-release compiler. Without this, semver would reject `0.6.0-rc.0` for a
    /// plain `>=0.6.0`.
    fn effective_version(&self, version: &Version) -> Version {
        let req_allows_pre = self.req.comparators.iter().any(|c| !c.pre.is_empty());
        if req_allows_pre || version.pre.is_empty() {
            version.clone()
        } else {
            Version {
                pre: semver::Prerelease::EMPTY,
                ..version.clone()
            }
        }
    }
}

/// Replace the directive with equal-length spaces so the parser never sees it
/// while later byte offsets (and thus error spans) stay correct.
pub(crate) fn blank_version_directive(content: &str) -> Cow<'_, str> {
    let directives: Vec<_> = leading_directives(content).collect();
    if directives.is_empty() {
        return Cow::Borrowed(content);
    }

    let mut buf = content.to_string();
    // Blank duplicates too; `check` reports them, not the parser.
    for (_, span) in &directives {
        buf.replace_range(span.start..span.end, &" ".repeat(span.end - span.start));
    }
    // A directive-only file blanks to whitespace, i.e. an empty program.
    Cow::Owned(if buf.trim().is_empty() {
        String::new()
    } else {
        buf
    })
}

/// The leading lines that carry code or directives, as `(full line, trimmed line,
/// byte offset of the line)`. Comments and blank lines are skipped; offsets keep
/// counting through them so spans stay correct.
fn meaningful_lines(content: &str) -> impl Iterator<Item = (&str, &str, usize)> {
    let mut in_block_comment = false;
    let mut offset = 0;
    content.split_inclusive('\n').filter_map(move |line| {
        let start = offset;
        offset += line.len();
        let trimmed = skip_block_comments(line.trim_start(), &mut in_block_comment);
        let skippable = in_block_comment || trimmed.is_empty() || trimmed.starts_with("//");
        (!skippable).then_some((line, trimmed, start))
    })
}

/// The leading `simc "...";` directives in order, stopping at the first line of
/// program code. More than one item means the file declared duplicates.
fn leading_directives(content: &str) -> impl Iterator<Item = (&str, Span)> {
    meaningful_lines(content)
        .map_while(|(line, trimmed, offset)| extract_directive_from_line(line, trimmed, offset))
}

/// The outcome of scanning a file for its compiler-version directive: the single
/// well-formed leading directive, its clean absence, or the specific way it is broken.
/// Centralizes the placement rules so [`check`] and [`requirement_of`] agree, and so a
/// misplaced or malformed directive yields a clear diagnostic instead of leaking to the
/// lexer as a confusing parse error.
enum DirectiveScan<'a> {
    /// A single well-formed directive, correctly placed before any program code.
    Found { req: &'a str, span: Span },
    /// No directive anywhere in the file.
    Absent,
    /// A directive-looking line that is not a well-formed `simc "...";`.
    Malformed(Span),
    /// More than one directive.
    Duplicate(Span),
    /// A well-formed directive that appears after program code.
    Misplaced(Span),
}

/// Scan `content` for its compiler-version directive. A directive must be the first
/// meaningful item and may appear at most once; the first deviation is reported with
/// the span of the offending line. Scans past the leading region so a directive
/// misplaced after code is caught rather than handed to the lexer.
fn scan_directive(content: &str) -> DirectiveScan<'_> {
    let mut found: Option<(&str, Span)> = None;
    let mut seen_code = false;
    for (line, trimmed, offset) in meaningful_lines(content) {
        if let Some((req, span)) = extract_directive_from_line(line, trimmed, offset) {
            if found.is_some() {
                return DirectiveScan::Duplicate(span);
            }
            if seen_code {
                return DirectiveScan::Misplaced(span);
            }
            found = Some((req, span));
        } else if !seen_code && directive_looking(trimmed) {
            // Before code, a `simc`-looking line that didn't parse is malformed. After
            // code we leave it be, so a `simc`-prefixed identifier isn't misreported.
            return DirectiveScan::Malformed(directive_looking_span(line, trimmed, offset));
        } else {
            seen_code = true;
        }
    }
    match found {
        Some((req, span)) => DirectiveScan::Found { req, span },
        None => DirectiveScan::Absent,
    }
}

/// Parse one line as a `simc "...";` directive, returning the requirement string
/// and the span covering `simc "...";`.
fn extract_directive_from_line<'a>(
    line: &str,
    trimmed: &'a str,
    current_offset: usize,
) -> Option<(&'a str, Span)> {
    if !trimmed.starts_with("simc") {
        return None;
    }
    let after_simc = &trimmed[4..];
    if !after_simc.is_empty() && !after_simc.starts_with(|c: char| c.is_whitespace() || c == '"') {
        return None;
    }

    let rest = after_simc.trim_start();
    let rest = rest.strip_prefix('"')?;
    let end_quote_idx = rest.find('"')?;
    let req_str = &rest[..end_quote_idx];

    let after_quote = rest[end_quote_idx + 1..].trim_start();
    if !after_quote.starts_with(';') {
        return None;
    }

    // Both are suffixes of `line`, so their lengths give the byte offsets directly.
    let span_start = current_offset + (line.len() - trimmed.len());
    let span_end = span_start + (trimmed.len() - after_quote.len()) + 1;

    Some((req_str, Span::new(span_start, span_end)))
}

/// Skip past `/* ... */` so a directive may follow a leading comment block.
fn skip_block_comments<'a>(mut trimmed: &'a str, in_block_comment: &mut bool) -> &'a str {
    loop {
        if *in_block_comment {
            if let Some(end_idx) = trimmed.find("*/") {
                trimmed = trimmed[end_idx + 2..].trim_start();
                *in_block_comment = false;
            } else {
                break;
            }
        } else if let Some(rest) = trimmed.strip_prefix("/*") {
            *in_block_comment = true;
            trimmed = rest;
        } else {
            break;
        }
    }
    trimmed
}

/// Whether a trimmed line begins a `simc "...";` directive attempt (well-formed or
/// not) — used to tell a malformed directive apart from ordinary program code.
fn directive_looking(trimmed: &str) -> bool {
    trimmed.strip_prefix("simc").is_some_and(|after| {
        after.is_empty() || after.starts_with(|c: char| c.is_whitespace() || c == '"')
    })
}

/// The span covering a directive-looking line, for reporting a malformed directive.
fn directive_looking_span(line: &str, trimmed: &str, offset: usize) -> Span {
    let start = offset + (line.len() - trimmed.len());
    Span::new(start, start + trimmed.trim_end().len())
}

/// The message shared by [`check`] and [`requirement_of`] for a leading line that
/// looks like a directive but is malformed, so the two agree on the wording.
fn malformed_directive_message() -> String {
    format!(
        "malformed compiler version directive; expected `{}`",
        directive_for("<version>")
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `matches` accepts or rejects requirements against the running compiler,
    /// exercising the pre-release normalization in `effective_version`: a release
    /// range still accepts the pre-release compiler, but semver pre-release gating
    /// (and reordered compound ranges) still bite. `0.6.0-rc.0` stands in for the
    /// compiler.
    #[test]
    fn matches_respects_operators_and_prerelease() {
        let cur = Version::parse("0.6.0-rc.0").unwrap();
        let accepted = [
            "*",
            "0.6.0",
            "^0.6.0",
            "~0.6.0",
            ">=0.6.0",
            ">0.1.0",
            "=0.6.0-rc.0",
            "^0.6.0-rc.0",
        ];
        let rejected = [
            "=0.5.0",
            ">99.0.0",
            "<0.0.1",
            "<0.6.0",          // -rc tag stripped, so 0.6.0 is not < 0.6.0
            ">=0.1.0-alpha.1", // pre-release gating: different base, so no match
            ">=0.7.0, =0.6.0", // the `=0.6.0` must not rescue the failing `>=0.7.0`
        ];
        for req in accepted {
            let req = VersionRequirement::parse(req).unwrap();
            assert!(req.matches(&cur), "`{req:?}` should match {cur}");
        }
        for req in rejected {
            let parsed = VersionRequirement::parse(req).unwrap();
            assert!(!parsed.matches(&cur), "`{req}` should not match {cur}");
        }
    }

    #[test]
    fn malformed_leading_directive_is_syntax_error_not_missing() {
        // A directive attempt with a missing semicolon or closing quote is a syntax
        // error, not an absent directive.
        for src in [
            "simc \"=0.5.0\"\nfn main() {}",
            "simc \"=0.5.0\nfn main() {}",
        ] {
            let (err, _span) = check(src).unwrap_err();
            assert!(
                matches!(err, Error::InvalidSimcVersionSyntax { .. }),
                "{src:?}"
            );
        }
    }

    #[test]
    fn misplaced_or_extra_directive_is_reported_not_leaked() {
        // A well-formed directive after program code is misplaced (it must be the first
        // item) — reported here, not handed to the parser as a stray `simc` token.
        let misplaced = "use foo;\nsimc \"*\";";
        assert!(matches!(
            check(misplaced).unwrap_err().0,
            Error::Syntax { .. }
        ));
        assert_eq!(requirement_of(misplaced), Err(DirectiveError::Misplaced));

        // A malformed *second* directive (before any code) is a syntax error, not a
        // silently ignored extra line that map_while used to stop short of.
        let bad_second = "simc \"*\";\nsimc \"bad\nfn main() {}";
        assert!(matches!(
            check(bad_second).unwrap_err().0,
            Error::InvalidSimcVersionSyntax { .. }
        ));
        assert!(matches!(
            requirement_of(bad_second),
            Err(DirectiveError::InvalidSyntax(_))
        ));
    }

    #[test]
    fn directive_scanned_through_leading_comments() {
        // The directive is the first *meaningful* line: leading `//` lines, blank
        // lines, and `/* */` blocks (multi-line or inline) are skipped, and the span
        // still lands exactly on `simc "...";` because offsets keep counting through
        // the skipped text. `*` matches any compiler, so this stays version-bump proof.
        for src in [
            "// header\n// notes\n\n/* a block\n   comment */\nsimc \"*\";\nfn main() {}",
            "/* lead */ simc \"*\";\nfn main() {}",
        ] {
            assert!(
                check(src).is_ok(),
                "should accept directive after comments: {src:?}"
            );
            let DirectiveScan::Found { req, span } = scan_directive(src) else {
                panic!("directive found past the comments: {src:?}");
            };
            assert_eq!(req, "*", "{src:?}");
            assert_eq!(
                &src[span.start..span.end],
                "simc \"*\";",
                "span must cover the directive in {src:?}"
            );
        }

        // A commented-out directive does not count; the real one after it does.
        let commented = "// simc \"=99.0.0\";\nsimc \"*\";\nfn main() {}";
        let DirectiveScan::Found { req, .. } = scan_directive(commented) else {
            panic!("real directive after the commented-out one");
        };
        assert_eq!(req, "*");
    }

    #[test]
    fn requirement_of_reads_or_rejects_directive() {
        // `req()` exposes the underlying semver requirement for range-intersecting tooling.
        let parsed = requirement_of("simc \">=0.1.0\";\nfn main() {}")
            .unwrap()
            .expect("directive present");
        assert_eq!(parsed.req(), &VersionReq::parse(">=0.1.0").unwrap());
        assert_eq!(requirement_of("fn main() {}"), Ok(None));
        assert!(matches!(
            requirement_of("simc \"not-a-version\";\nfn main() {}"),
            Err(DirectiveError::InvalidSyntax(_))
        ));
        // A malformed directive is a syntax error here too, not silently "absent",
        // so tooling and the compiler agree (the missing semicolon below).
        assert!(matches!(
            requirement_of("simc \"=0.1.0\"\nfn main() {}"),
            Err(DirectiveError::InvalidSyntax(_))
        ));
        // Duplicates are only reachable through this external entry point.
        assert_eq!(
            requirement_of("simc \"=0.1.0\";\nsimc \"=0.2.0\";\nfn main() {}"),
            Err(DirectiveError::Duplicate)
        );
    }
}
