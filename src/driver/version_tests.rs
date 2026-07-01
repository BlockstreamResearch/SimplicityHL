//! Integration tests for the *multi-file* enforcement of `simc "...";` directives:
//! the entry file and every reachable dependency are checked, unreachable files
//! are not, and our directive scanner (duplicates, comments) behaves end to end.
//!
//! Semver matching and mismatch-message classification are tested directly and far
//! more cheaply in `crate::version`'s unit tests; they are deliberately not
//! re-asserted through the dependency graph here.

use crate::driver::tests::setup_graph_raw;

/// Builds the given files (replacing `{v}` with the current compiler version), runs
/// the dependency-graph build, and asserts the expected outcome. When `expect_success`
/// is false and `expected_err` is `Some`, the collected diagnostics must contain it.
fn check_versions(expect_success: bool, expected_err: Option<&str>, files: &[(&str, &str)]) {
    let v = env!("CARGO_PKG_VERSION");
    let owned: Vec<(&str, String)> = files
        .iter()
        .map(|(p, c)| (*p, c.replace("{v}", v)))
        .collect();
    let refs: Vec<(&str, &str)> = owned.iter().map(|(p, c)| (*p, c.as_str())).collect();
    let (graph_opt, _, _ws, handler) = setup_graph_raw(refs);

    if expect_success {
        assert!(
            graph_opt.is_some() && !handler.has_errors(),
            "Scenario failed unexpectedly. Errors:\n{handler}"
        );
        return;
    }

    assert!(
        graph_opt.is_none() || handler.has_errors(),
        "Scenario succeeded when it should have failed."
    );
    if let Some(err) = expected_err {
        assert!(
            handler.to_string().contains(err),
            "Expected error containing '{err}' but got:\n{handler}"
        );
    }
}

/// A multi-file program whose every file declares a compatible directive compiles:
/// each directive is checked and stripped, and the bodies still parse across `use`.
#[test]
fn mixed_valid_operators() {
    check_versions(
        true,
        None,
        &[
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
        ],
    );
}

/// The entry file's directive is checked.
#[test]
fn main_too_old_fails() {
    check_versions(
        false,
        Some("Incompatible compiler version"),
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
    check_versions(
        false,
        Some("Incompatible compiler version"),
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
    check_versions(
        true,
        None,
        &[
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
        ],
    );
}

/// An omitted directive is allowed through the driver: only a present directive is
/// enforced, so a directive-less entry file builds successfully.
#[test]
fn directive_omitted() {
    check_versions(true, None, &[("main.simf", "fn main() {}")]);
}

/// A file may declare at most one directive.
#[test]
fn multiple_directives_same_file_fails() {
    check_versions(
        false,
        Some("Exactly one compiler version directive"),
        &[(
            "main.simf",
            r#"simc "={v}";
simc "={v}";
fn main() {}"#,
        )],
    );
}

/// A malformed version requirement surfaces through the pipeline.
#[test]
fn invalid_syntax_main() {
    check_versions(
        false,
        Some("Invalid version syntax"),
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
    check_versions(
        true,
        None,
        &[(
            "main.simf",
            r#"// simc "=99.0.0";
simc "={v}";
fn main() {}"#,
        )],
    );
}

/// A directive may follow a leading block comment; one inside the comment does not
/// count.
#[test]
fn version_in_block_comment_ignored() {
    check_versions(
        true,
        None,
        &[(
            "main.simf",
            r#"/*
simc "=99.0.0";
*/
simc "={v}";
fn main() {}"#,
        )],
    );
}
