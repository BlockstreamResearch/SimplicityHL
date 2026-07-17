//! Multi-file enforcement of `simc "...";` directives: the entry file and every
//! reachable dependency are checked. Semver matching itself is covered by
//! `crate::version`'s unit tests.

use crate::driver::tests::setup_graph_raw;

/// Builds the given files (with `{v}` replaced by the current compiler version)
/// through the dependency-graph build, returning success and collected diagnostics.
fn build(files: &[(&str, &str)]) -> (bool, String) {
    // Ranges cannot name pre-releases, so an `-rc` compiler substitutes its base version.
    let v = env!("CARGO_PKG_VERSION").split('-').next().unwrap();
    let owned: Vec<(&str, String)> = files
        .iter()
        .map(|(p, c)| (*p, c.replace("{v}", v)))
        .collect();

    let refs: Vec<(&str, &str)> = owned.iter().map(|(p, c)| (*p, c.as_str())).collect();
    let (graph_opt, _, _ws, diagnostics) = setup_graph_raw(refs);

    let ok = graph_opt.is_some() && !diagnostics.has_errors();
    (ok, diagnostics.to_string())
}

fn assert_builds(files: &[(&str, &str)]) {
    let (ok, errors) = build(files);
    assert!(ok, "build failed unexpectedly. Errors:\n{errors}");
}

/// Like [`assert_builds`], but the build must fail with a diagnostic containing
/// `expected_err`.
fn assert_build_fails(expected_err: &str, files: &[(&str, &str)]) {
    let (ok, errors) = build(files);
    assert!(!ok, "build succeeded when it should have failed");
    assert!(
        errors.contains(expected_err),
        "Expected error containing '{expected_err}' but got:\n{errors}"
    );
}

/// A multi-file program whose every file declares a compatible directive compiles:
/// each directive is checked and stripped, and the bodies still parse across `use`.
#[test]
fn mixed_valid_operators() {
    assert_builds(&[
        (
            "main.simf",
            r#"simc "^{v}";
use lib::A::foo;
fn main() {}"#,
        ),
        (
            "libs/lib/A.simf",
            r#"simc "={v}";
use crate::B::foo;
pub fn foo() {}"#,
        ),
        (
            "libs/lib/B.simf",
            r#"simc ">0.1.0";
use crate::C::foo;
pub fn foo() {}"#,
        ),
        (
            "libs/lib/C.simf",
            r#"simc "*";
pub fn foo() {}"#,
        ),
    ]);
}

/// The entry file's directive is checked.
#[test]
fn main_too_old_fails() {
    assert_build_fails(
        "Incompatible compiler version",
        &[
            (
                "main.simf",
                r#"simc ">99.0.0";
use lib::A::foo;
fn main() {}"#,
            ),
            (
                "libs/lib/A.simf",
                r#"simc "={v}";
pub fn foo() {}"#,
            ),
        ],
    );
}

/// Every reachable dependency's directive is checked, not just the entry file.
#[test]
fn lib_too_old_fails() {
    assert_build_fails(
        "Incompatible compiler version",
        &[
            (
                "main.simf",
                r#"simc "={v}";
use lib::A::foo;
fn main() {}"#,
            ),
            (
                "libs/lib/A.simf",
                r#"simc ">99.0.0";
pub fn foo() {}"#,
            ),
        ],
    );
}

/// A file that is never imported is not checked, even with an incompatible directive.
#[test]
fn unreferenced_file_with_invalid_version_ignored() {
    assert_builds(&[
        (
            "main.simf",
            r#"simc "={v}";
use lib::A::foo;
fn main() {}"#,
        ),
        (
            "libs/lib/A.simf",
            r#"simc "={v}";
pub fn foo() {}"#,
        ),
        (
            "libs/lib/B.simf",
            r#"simc ">99.0.0";
pub fn unused() {}"#,
        ),
    ]);
}

/// An omitted directive is allowed through the driver: only a present directive is
/// enforced, so a directive-less entry file builds successfully.
#[test]
fn directive_omitted() {
    assert_builds(&[("main.simf", "fn main() {}")]);
}

/// The compatibility check runs on the raw text, before lexing: an incompatible
/// compiler is reported even when the file's body cannot be tokenized (here a string
/// literal, which the language does not have), instead of a pile of lex errors.
#[test]
fn incompatible_reported_despite_unlexable_body() {
    assert_build_fails(
        "Incompatible compiler version",
        &[(
            "main.simf",
            r#"simc ">99.0.0";
fn main() { let s = "future syntax"; }"#,
        )],
    );
}

/// A stray directive is reported alone: its `"<range>";` remnant and the rest of
/// the parse must not add noise on top of the reserved-keyword error.
#[test]
fn stray_directive_reports_single_error() {
    let (ok, errors) = build(&[(
        "main.simf",
        r#"simc "={v}";
simc "={v}";
fn main() {}"#,
    )]);
    assert!(!ok, "duplicate directive must fail the build");
    assert!(
        errors.contains("reserved"),
        "expected the reserved-keyword error, got:\n{errors}"
    );
    assert!(
        !errors.contains("Cannot parse"),
        "remnant noise must be suppressed, got:\n{errors}"
    );
}

/// A file may declare at most one directive: a second one is misplaced and gets a
/// targeted diagnostic.
#[test]
fn multiple_directives_same_file_fails() {
    assert_build_fails(
        "must be the first item",
        &[(
            "main.simf",
            r#"simc "={v}";
simc "={v}";
fn main() {}"#,
        )],
    );
}

/// A directive after another item is misplaced and gets a targeted diagnostic,
/// with no noise from its `"<range>";` remnant.
#[test]
fn directive_after_item_fails() {
    let (ok, errors) = build(&[(
        "main.simf",
        r#"fn main() {}
simc "={v}";"#,
    )]);
    assert!(!ok, "misplaced directive must fail the build");
    assert!(
        errors.contains("must be the first item"),
        "expected the reserved-keyword error, got:\n{errors}"
    );
    assert!(
        !errors.contains("Cannot parse"),
        "remnant noise must be suppressed, got:\n{errors}"
    );
}

/// A malformed version requirement surfaces through the pipeline.
#[test]
fn invalid_syntax_main() {
    assert_build_fails(
        "Invalid version requirement",
        &[
            (
                "main.simf",
                r#"simc "foo";
use lib::A::foo;
fn main() {}"#,
            ),
            (
                "libs/lib/A.simf",
                r#"simc "={v}";
pub fn foo() {}"#,
            ),
        ],
    );
}

/// A directive may follow a leading line comment; a commented-out directive does not
/// count.
#[test]
fn version_in_comment_ignored() {
    assert_builds(&[(
        "main.simf",
        r#"// simc "=99.0.0";
simc "={v}";
fn main() {}"#,
    )]);
}

/// A directive may follow a leading block comment; one inside the comment does not
/// count.
#[test]
fn version_in_block_comment_ignored() {
    assert_builds(&[(
        "main.simf",
        r#"/*
simc "=99.0.0";
*/
simc "={v}";
fn main() {}"#,
    )]);
}
