use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn repo_path(path: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(path)
}

/// Write `content` to a uniquely named `.simf` file in the test temp dir and run
/// `simc` on it, returning the process output. Used by the version-directive tests
/// to exercise the real binary on standalone files.
fn run_simc_on_source(name: &str, content: &str) -> Output {
    let file = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("{name}.simf"));
    std::fs::write(&file, content).expect("failed to write source file");
    Command::new(env!("CARGO_BIN_EXE_simc"))
        .arg(file)
        .output()
        .expect("failed to run simc")
}

/// Write each `(relative path, content)` under a unique temp project root (creating
/// parent directories) and return the root. Used to drive multi-file `--dep` builds.
fn setup_project(name: &str, files: &[(&str, &str)]) -> PathBuf {
    let root = Path::new(env!("CARGO_TARGET_TMPDIR")).join(name);
    for (rel, content) in files {
        let path = root.join(rel);
        std::fs::create_dir_all(path.parent().unwrap()).expect("failed to create project dirs");
        std::fs::write(&path, content).expect("failed to write project file");
    }
    root
}

#[test]
fn cli_dependency_can_use_crate_root() {
    let root = repo_path("functional-tests/valid-test-cases/external-library-uses-crate");
    let main = root.join("main.simf");
    let ext_lib = root.join("ext_lib");
    let dep_arg = format!("{}:ext_lib={}", root.display(), ext_lib.display());

    let output = Command::new(env!("CARGO_BIN_EXE_simc"))
        .arg(main)
        .arg("-Z")
        .arg("imports")
        .arg("--dep")
        .arg(dep_arg)
        .output()
        .expect("failed to run simc");

    assert!(
        output.status.success(),
        "simc failed\nstatus: {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
fn cli_import_program_rejected_without_unstable_flag() {
    let root = repo_path("functional-tests/valid-test-cases/external-library-uses-crate");
    let main = root.join("main.simf");
    let ext_lib = root.join("ext_lib");
    let dep_arg = format!("{}:ext_lib={}", root.display(), ext_lib.display());

    // Same invocation as `cli_dependency_can_use_crate_root`, but without `-Z imports`:
    // the import syntax must be gated, so the binary exits non-zero and points at
    // the missing feature flag.
    let output = Command::new(env!("CARGO_BIN_EXE_simc"))
        .arg(main)
        .arg("--dep")
        .arg(dep_arg)
        .output()
        .expect("failed to run simc");

    assert!(
        !output.status.success(),
        "simc must reject an import program without -Z imports"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("imports") && stderr.contains("-Z"),
        "error should name the feature and the flag, got:\n{stderr}"
    );
}

#[test]
fn cli_reserved_crate_mapping_fails() {
    let root = repo_path("functional-tests/valid-test-cases/external-library-uses-crate");
    let main = root.join("main.simf");
    let ext_lib = root.join("ext_lib");

    // Attempt to maliciously override the `crate` keyword
    let dep_arg = format!("crate={}", ext_lib.display());

    let output = Command::new(env!("CARGO_BIN_EXE_simc"))
        .arg(main)
        .arg("--dep")
        .arg(dep_arg)
        .output()
        .expect("failed to run simc");

    assert!(
        !output.status.success(),
        "simc unexpectedly succeeded when overriding the 'crate' dependency"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("keyword is reserved"),
        "Expected 'keyword is reserved' error, got:\n{}",
        stderr
    );
}

/// A compatible version directive compiles from the command line, with no
/// missing-directive warning. `*` matches any compiler, so this stays valid across
/// version bumps and acts as the positive control for the rejection tests below.
#[test]
fn cli_version_compatible_accepted() {
    let output = run_simc_on_source("version_ok", "simc \"*\";\nfn main() {}\n");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "simc should accept a compatible directive\nstderr:\n{stderr}",
    );
    assert!(
        !stderr.contains("no compiler version directive"),
        "a present directive must not trigger the missing-directive warning, got:\n{stderr}"
    );
}

/// A directive the running compiler cannot satisfy is rejected. `>99.0.0` is
/// permanently too new, so the build aborts with a non-zero exit and a clear message.
#[test]
fn cli_version_incompatible_rejected() {
    let output = run_simc_on_source("version_incompatible", "simc \">99.0.0\";\nfn main() {}\n");
    assert!(
        !output.status.success(),
        "simc must reject an incompatible directive"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Incompatible compiler version"),
        "Expected 'Incompatible compiler version', got:\n{stderr}"
    );
}

/// A directive is optional: a file with none still compiles, but the CLI prints a
/// warning suggesting one be added.
#[test]
fn cli_version_missing_warns_but_compiles() {
    let output = run_simc_on_source("version_missing", "fn main() {}\n");
    assert!(
        output.status.success(),
        "simc must accept a file with no version directive"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("no compiler version directive"),
        "Expected a missing-directive warning, got:\n{stderr}"
    );
}

/// A directive whose requirement is not valid semver is a syntax error, not a
/// version mismatch.
#[test]
fn cli_version_invalid_syntax_rejected() {
    let output = run_simc_on_source(
        "version_bad_syntax",
        "simc \"not-a-version\";\nfn main() {}\n",
    );
    assert!(
        !output.status.success(),
        "simc must reject a malformed version requirement"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Invalid version syntax"),
        "Expected 'Invalid version syntax', got:\n{stderr}"
    );
}

/// A directive that is structurally broken (here a missing semicolon) is rejected
/// before the requirement is even parsed — a different path than an invalid semver
/// string above.
#[test]
fn cli_version_malformed_directive_rejected() {
    let output = run_simc_on_source("version_malformed", "simc \"1.0\"\nfn main() {}\n");
    assert!(
        !output.status.success(),
        "simc must reject a directive with a missing semicolon"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("malformed compiler version directive"),
        "Expected 'malformed compiler version directive', got:\n{stderr}"
    );
}

/// An incompatible directive in a *dependency* (reached via `--dep`), not the entry
/// file, also aborts the build and the diagnostic points at the dependency.
#[test]
fn cli_dependency_version_mismatch_rejected() {
    let root = setup_project(
        "version_dep_mismatch",
        &[
            (
                "main.simf",
                "simc \"*\";\nuse lib::module::add;\nfn main() {}\n",
            ),
            ("lib/module.simf", "simc \">99.0.0\";\npub fn add() {}\n"),
        ],
    );
    let dep_arg = format!("{}:lib={}", root.display(), root.join("lib").display());

    let output = Command::new(env!("CARGO_BIN_EXE_simc"))
        .arg(root.join("main.simf"))
        .arg("-Z")
        .arg("imports")
        .arg("--dep")
        .arg(dep_arg)
        .output()
        .expect("failed to run simc");

    assert!(
        !output.status.success(),
        "simc must reject an incompatible directive in a dependency"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Incompatible compiler version") && stderr.contains("module.simf"),
        "expected an incompatible-version error pointing at the dependency, got:\n{stderr}"
    );
}
