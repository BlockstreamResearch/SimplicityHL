//! Compiler-version directives: `simc "<range>";`.
//!
//! A `.simf` file may declare, as its first non-comment item, the semver range of
//! compilers it is written for (see `doc/versioning.md`). The check runs once per
//! file, before lexing: `SimcDirective::prescan` scans the raw text, validates the
//! range against the running compiler, and returns the byte offset at which lexing
//! starts — right after the directive. Working on raw text keeps the check alive
//! for files whose bodies this compiler cannot even tokenize; an incompatible
//! compiler is reported as the only diagnostic.
//!
//! The language has no directive token: `simc` is a reserved keyword, so the lexer
//! rejects any `simc` it encounters past the prescan offset (a duplicate or
//! misplaced directive). The syntax recognized by `SimcDirective::scan` is frozen —
//! every past and future compiler must be able to read it. Keeping that code in
//! this module, away from the version-dependent parts of the compiler, is what
//! makes the guarantee enforceable.
//!
//! External tooling reads a file's declared range without compiling it via
//! [`SimcDirective::requirement_of`].

use std::ops::Range;
use std::sync::OnceLock;

use chumsky::Parser;
use semver::{Version, VersionReq};

use crate::error::{Error, Span};

/// The directive keyword, reserved by the lexer.
pub(crate) const SIMC_STR: &str = "simc";

/// Result of scanning a file's leading bytes for a `simc "<range>";` directive.
#[derive(Clone, Debug, Eq, PartialEq)]
enum DirectiveScan<'a> {
    /// A well-formed directive: the range between the quotes and its byte span.
    Found { range: &'a str, span: Range<usize> },
    /// A directive missing its closing quote or semicolon; `span` covers the broken text.
    Malformed { span: Range<usize> },
    /// No directive at the top of the file.
    Absent,
}

/// Operations on the `simc "<range>";` compiler-version directive.
pub struct SimcDirective;

impl SimcDirective {
    /// The running compiler's version (`CARGO_PKG_VERSION`), which directives are
    /// validated against.
    pub fn current_version() -> &'static str {
        env!("CARGO_PKG_VERSION")
    }

    /// Scan the raw text for a leading directive, validate it against the running
    /// compiler, and return the byte offset at which lexing should start — right
    /// after the directive.
    ///
    /// Skipping by offset keeps the pipeline directive-free — no token, no grammar
    /// special cases, `simc` stays plainly reserved — without copying or modifying
    /// the source. On error the caller should not lex: any further diagnostic is
    /// noise.
    pub(crate) fn prescan(content: &str, file_id: usize) -> Result<usize, (Error, Span)> {
        match Self::scan(content) {
            DirectiveScan::Absent => Ok(0),
            DirectiveScan::Malformed { span } => {
                Err((Error::MalformedSimcDirective, Span::new(file_id, span)))
            }
            DirectiveScan::Found { range, span } => {
                Self::validate(range, Span::new(file_id, span.clone()))?;
                Ok(span.end)
            }
        }
    }

    /// Read a file's declared version requirement without compiling it, for external
    /// tooling. Returns `Ok(None)` when the file declares no directive, and an error
    /// when the directive is malformed or its range is not valid semver.
    pub fn requirement_of(content: &str) -> Result<Option<VersionRequirement>, String> {
        match Self::scan(content) {
            DirectiveScan::Found { range, .. } => VersionRequirement::parse(range.trim()).map(Some),
            DirectiveScan::Malformed { .. } => Err(Error::MalformedSimcDirective.to_string()),
            DirectiveScan::Absent => Ok(None),
        }
    }

    /// The CLI advisory for a file with no `simc` directive, or `None` when one is
    /// present (a malformed directive counts as present). The suggestion names the
    /// compiler's base version — ranges cannot contain pre-release tags.
    pub fn missing_warning(content: &str) -> Option<String> {
        matches!(Self::scan(content), DirectiveScan::Absent).then(|| {
            let base_version = Self::current_version()
                .split('-')
                .next()
                .expect("split yields at least one part");
            format!(
                "no compiler version directive at the top of the file; consider adding `{SIMC_STR} \"{base_version}\";`",
            )
        })
    }

    /// Scan the start of `content` for a directive, skipping whitespace and comments.
    /// The single (frozen) definition of the directive syntax.
    fn scan(content: &str) -> DirectiveScan<'_> {
        // `rest` is always a suffix of `content`, so positions fall out of its length.
        let offset = |rest: &str| content.len() - rest.len();
        let start = Self::skip_trivia(content);

        let Some(rest) = content[start..].strip_prefix(SIMC_STR) else {
            return DirectiveScan::Absent;
        };
        // A bare `simc` is not a directive; the lexer rejects it as reserved.
        let Some(rest) = rest.trim_start_matches([' ', '\t']).strip_prefix('"') else {
            return DirectiveScan::Absent;
        };
        // The range runs to the closing quote on the same line.
        let Some(quote) = rest
            .find(['"', '\n'])
            .filter(|&i| rest[i..].starts_with('"'))
        else {
            let line_end = rest.find('\n').unwrap_or(rest.len());
            return DirectiveScan::Malformed {
                span: start..offset(rest) + line_end,
            };
        };
        let (range, rest) = (&rest[..quote], &rest[quote + 1..]);
        let rest = rest.trim_start_matches([' ', '\t']);
        let Some(rest) = rest.strip_prefix(';') else {
            return DirectiveScan::Malformed {
                span: start..offset(rest),
            };
        };
        DirectiveScan::Found {
            range,
            span: start..offset(rest),
        }
    }

    /// Validate a directive's version-requirement string against the running compiler.
    fn validate(required: &str, span: Span) -> Result<(), (Error, Span)> {
        let required = required.trim();
        let req = VersionRequirement::parse(required)
            .map_err(|e| (Error::InvalidSimcVersionSyntax { err: e }, span))?;

        if !req.matches(Self::current_semver()) {
            let err = Error::SimcVersionMismatch {
                required: required.to_string(),
                current: Self::current_version().to_string(),
            };
            return Err((err, span));
        }
        Ok(())
    }

    /// The running compiler's version, parsed once. `CARGO_PKG_VERSION` is a compile-time
    /// constant, so a multi-file build reuses this instead of re-parsing it per file.
    fn current_semver() -> &'static Version {
        static CURRENT: OnceLock<Version> = OnceLock::new();
        CURRENT.get_or_init(|| {
            Version::parse(Self::current_version()).expect("CARGO_PKG_VERSION is valid semver")
        })
    }

    /// Byte offset of the first content after leading whitespace and comments, using
    /// the lexer's shared [`trivia`](crate::lexer::trivia) recognizer so the scanner
    /// and the lexer agree on comment syntax.
    fn skip_trivia(content: &str) -> usize {
        crate::lexer::trivia()
            .to_slice()
            .lazy()
            .parse(content)
            .into_output()
            .map_or(0, str::len)
    }
}

/// A parsed directive requirement: the semver range written inside the quotes.
///
/// Wraps [`semver::VersionReq`], restricted to plain numeric versions: pre-release
/// identifiers are rejected at parse time, keeping matching inside the semver
/// crate's well-understood behavior. The running compiler's own pre-release tag is
/// instead normalized away in [`Self::matches`], so a release range still accepts a
/// pre-release build of that version.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VersionRequirement {
    req: VersionReq,
}

impl VersionRequirement {
    /// Parse a requirement string such as `>=0.6.0` or `=0.6.0`. Versions in the
    /// range must be plain `x.y.z` numbers — semver's pre-release matching has
    /// surprising corner cases, so pre-release identifiers are rejected outright.
    pub fn parse(s: &str) -> Result<Self, String> {
        let req = VersionReq::parse(s).map_err(|e| e.to_string())?;
        if req.comparators.iter().any(|c| !c.pre.is_empty()) {
            return Err(
                "pre-release identifiers are not allowed in version requirements".to_string(),
            );
        }
        Ok(VersionRequirement { req })
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
        self.req.matches(&Self::effective_version(version))
    }

    /// Strip the pre-release tag (`0.6.0-rc.0` → `0.6.0`), so a release range still
    /// accepts a matching pre-release compiler — without this, semver would reject
    /// `0.6.0-rc.0` for a plain `>=0.6.0`. Ranges themselves cannot name
    /// pre-releases (see [`Self::parse`]), so this is the only normalization needed.
    fn effective_version(version: &Version) -> Version {
        Version {
            pre: semver::Prerelease::EMPTY,
            ..version.clone()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::driver::MAIN_MODULE;

    /// `scan` distinguishes found, malformed, and absent directives, with exact spans.
    #[test]
    fn scan_directive_cases() {
        let found = |content: &str, range: &str, directive: &str| match SimcDirective::scan(content)
        {
            DirectiveScan::Found { range: r, span } => {
                assert_eq!(r, range, "wrong range in {content:?}");
                assert_eq!(&content[span], directive, "wrong span in {content:?}");
            }
            other => panic!("expected Found in {content:?}, got {other:?}"),
        };
        let malformed = |content: &str, broken: &str| match SimcDirective::scan(content) {
            DirectiveScan::Malformed { span } => {
                assert_eq!(&content[span], broken, "wrong span in {content:?}");
            }
            other => panic!("expected Malformed in {content:?}, got {other:?}"),
        };

        found(
            "simc \">=0.6.0\";\nfn main() {}",
            ">=0.6.0",
            "simc \">=0.6.0\";",
        );
        found("simc   \"*\" ;rest", "*", "simc   \"*\" ;");
        // Line comments, nested block comments, and blank lines are skipped.
        found(
            "// note\n/* outer /* inner */ outer */\n\nsimc \"1.0\";",
            "1.0",
            "simc \"1.0\";",
        );

        // Committed (`simc "`) but missing the closing quote or the semicolon.
        malformed("simc \"1.0\"\nfn f() {}", "simc \"1.0\"");
        malformed("simc \"1.0\nfn f() {}", "simc \"1.0");
        malformed("simc \"1.0\"", "simc \"1.0\"");

        // Not a directive at all: bare identifier, other code, or a directive that is
        // not the first item (the lexer rejects those as reserved `simc`).
        assert_eq!(SimcDirective::scan("simc"), DirectiveScan::Absent);
        assert_eq!(
            SimcDirective::scan("simcfoo \"1.0\";"),
            DirectiveScan::Absent
        );
        assert_eq!(SimcDirective::scan("fn main() {}"), DirectiveScan::Absent);
        assert_eq!(
            SimcDirective::scan("fn f() {}\nsimc \"1.0\";"),
            DirectiveScan::Absent
        );
        assert_eq!(
            SimcDirective::scan("/* unterminated\nsimc \"1.0\";"),
            DirectiveScan::Absent
        );
    }

    /// `prescan` validates a valid directive and returns the offset right after it;
    /// a directive-less source lexes from the top, and a broken directive aborts.
    #[test]
    fn prescan_validates_and_returns_offset() {
        let src = "// c\nsimc \"*\";\nfn main() {}";
        let DirectiveScan::Found { span, .. } = SimcDirective::scan(src) else {
            panic!("expected a directive in the test source");
        };
        let start = SimcDirective::prescan(src, MAIN_MODULE).unwrap();
        assert_eq!(
            start, span.end,
            "lexing must start right after the directive"
        );

        assert_eq!(
            SimcDirective::prescan("fn main() {}", MAIN_MODULE).unwrap(),
            0
        );

        assert!(matches!(
            SimcDirective::prescan("simc \"1.0\"\nfn main() {}", MAIN_MODULE)
                .unwrap_err()
                .0,
            Error::MalformedSimcDirective
        ));
        assert!(matches!(
            SimcDirective::prescan("simc \">99.0.0\";", MAIN_MODULE)
                .unwrap_err()
                .0,
            Error::SimcVersionMismatch { .. }
        ));
    }

    /// `matches` respects semver operators after pre-release normalization:
    /// `0.6.0-rc.0` stands in for the compiler and is matched as `0.6.0`.
    #[test]
    fn matches_respects_operators_and_prerelease() {
        let cur = Version::parse("0.6.0-rc.0").unwrap();
        let accepted = ["*", "0.6.0", "^0.6.0", "~0.6.0", ">=0.6.0", ">0.1.0"];
        let rejected = [
            "=0.5.0",
            ">99.0.0",
            "<0.0.1",
            "<0.6.0",          // -rc tag stripped, so 0.6.0 is not < 0.6.0
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

    /// Pre-release identifiers are rejected in ranges outright: semver's pre-release
    /// matching has surprising corner cases, so requirements stay in plain-version
    /// space (the compiler's own `-rc` tag is normalized in `matches` instead).
    #[test]
    fn prerelease_ranges_rejected() {
        for req in ["=0.6.0-rc.0", "^0.6.0-rc.0", ">=0.1.0-alpha.1"] {
            assert!(
                VersionRequirement::parse(req).is_err(),
                "`{req}` must be rejected"
            );
        }
        assert!(matches!(
            SimcDirective::validate("=0.6.0-rc.0", Span::new(MAIN_MODULE, 0..1))
                .unwrap_err()
                .0,
            Error::InvalidSimcVersionSyntax { .. }
        ));
    }

    /// `validate` rejects a bad semver range and an incompatible compiler, and
    /// accepts a satisfiable one.
    #[test]
    fn validate_reports_bad_and_incompatible() {
        let span = Span::new(MAIN_MODULE, 0..1);
        assert!(matches!(
            SimcDirective::validate("not-a-version", span)
                .unwrap_err()
                .0,
            Error::InvalidSimcVersionSyntax { .. }
        ));
        assert!(matches!(
            SimcDirective::validate(">=99.0.0", span).unwrap_err().0,
            Error::SimcVersionMismatch { .. }
        ));
        assert!(SimcDirective::validate("*", span).is_ok());
    }

    /// Only a directive-less source triggers the advisory; `requirement_of`
    /// distinguishes "no directive" from "broken directive".
    #[test]
    fn missing_warning_and_requirement_of() {
        assert!(SimcDirective::missing_warning("fn main() {}").is_some());
        assert!(SimcDirective::missing_warning("simc \"*\";\nfn main() {}").is_none());
        assert!(SimcDirective::missing_warning("// note\nsimc \"*\";\nfn main() {}").is_none());
        assert!(SimcDirective::missing_warning("simc \"*\"\nfn main() {}").is_none());

        assert_eq!(
            SimcDirective::requirement_of("simc \">=0.1.0\";\nfn main() {}")
                .unwrap()
                .map(|r| r.req().clone()),
            Some(VersionReq::parse(">=0.1.0").unwrap())
        );
        assert_eq!(SimcDirective::requirement_of("fn main() {}"), Ok(None));
        assert!(SimcDirective::requirement_of("simc \"*\"\nfn main() {}").is_err());
        assert!(SimcDirective::requirement_of("simc \"not-a-version\";").is_err());
    }
}
