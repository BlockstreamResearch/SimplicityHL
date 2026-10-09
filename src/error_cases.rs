//! Programs that must be rejected, one file per case.
//!
//! Each `.simf` file in [`CASES_DIR`] starts with a header naming the [`Error`]
//! variant it must produce, and optionally the unstable features to enable:
//!
//! ```text
//! // error: ExpressionTypeMismatch
//! // flags: enums imports
//! ```
//!
//! A case may have `<name>.args` and `<name>.wit` files next to it. A missing
//! file means no arguments or no witness values.
//!
//! The [`coverage!`] table lists every [`Error`] variant. Its `match` has no
//! wildcard arm, so adding a variant does not compile until it is listed here,
//! either with a case file or with the reason it has none.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::str::FromStr;

use crate::ast::ElementsJetHinter;
use crate::error::{DiagnosticManager, Error};
use crate::{
    Arguments, TemplateAst, UnresolvedValues, UnstableFeature, UnstableFeatures, WitnessValues,
};

const CASES_DIR: &str = "./functional-tests/error-test-cases/single-file";

/// How a variant is covered.
#[derive(Debug)]
enum Coverage {
    /// At least one case file in [`CASES_DIR`] produces this variant.
    Tested,
    /// Covered by the named test outside [`CASES_DIR`].
    Elsewhere(&'static str),
    /// Cannot be produced from source; the reason says why.
    Untestable(&'static str),
}

use Coverage::{Elsewhere, Tested, Untestable};

macro_rules! coverage {
    ($($variant:ident => $coverage:expr,)*) => {
        fn variant_name(error: &Error) -> &'static str {
            match error {
                $(Error::$variant { .. } => stringify!($variant),)*
            }
        }

        const COVERAGE: &[(&str, Coverage)] = &[$((stringify!($variant), $coverage),)*];
    };
}

coverage! {
    UnstableFeature => Tested,
    InvalidSimcVersionSyntax => Tested,
    SimcVersionMismatch => Tested,
    MalformedSimcDirective => Tested,
    ReservedSimcKeyword => Tested,
    DependencyPathNotFound => Elsewhere("lib.rs: file_not_found_error, lib_not_found_error"),
    DependencyNotADirectory => Elsewhere("resolution.rs: test_builder_rejects_file_as_directory"),
    ReservedDependencyKeyword => Elsewhere("resolution.rs: test_builder_rejects_reserved_keywords"),
    DuplicateDependencyAlias => Elsewhere("resolution.rs: test_builder_rejects_duplicates"),
    LinearizationCycleDetected => Elsewhere("driver/linearization.rs: test_linearize_detects_cycle"),
    InvalidDependencyIdentifier => Elsewhere("resolution.rs: test_builder_rejects_invalid_identifiers"),
    Internal => Untestable("reports a compiler bug"),
    UnknownLibrary => Elsewhere("resolution.rs: test_context_isolation"),
    ArraySizeNonZero => Tested,
    ListBoundPow2 => Tested,
    BitStringPow2 => Tested,
    CannotParse => Tested,
    Grammar => Tested,
    Syntax => Tested,
    IncompatibleMatchArms => Tested,
    CannotCompile => Untestable("the compiler should never produce ill-typed Simplicity"),
    ParseInt => Tested,
    ParseCrateInt => Tested,
    JetDoesNotExist => Tested,
    InvalidCast => Tested,
    FileNotFound => Elsewhere(
        "resolution.rs: test_crate_file_not_found; driver: test_unreadable_import_is_file_not_found",
    ),
    ExternalFileNotFound => Elsewhere("resolution.rs: test_external_file_not_found"),
    LocalFileImportedAsExternal => Elsewhere("resolution.rs: test_local_file_imported_as_external"),
    RedefinedItem => Tested,
    UnresolvedItem => Tested,
    PrivateItem => Tested,
    MissingCrateKeyword => Tested,
    MainNoInputs => Tested,
    MainNoOutput => Tested,
    MainRequired => Tested,
    MainOutOfEntryFile => Untestable("only its message is used, inside a CannotParse error"),
    MainCannotBePublic => Tested,
    MainCannotBeAlias => Tested,
    FunctionRedefined => Tested,
    FunctionUndefined => Tested,
    InvalidNumberOfArguments => Tested,
    FunctionNotFoldable => Tested,
    FunctionNotLoopable => Tested,
    ExpressionUnexpectedType => Tested,
    ExpressionTypeMismatch => Tested,
    ExpressionNotConstant => Untestable("never constructed"),
    IntegerOutOfBounds => Tested,
    UndefinedVariable => Tested,
    RedefinedAlias => Tested,
    RedefinedAliasAsBuiltin => Tested,
    UndefinedAlias => Tested,
    DuplicateAlias => Untestable("never constructed"),
    VariableReuseInPattern => Tested,
    WitnessReused => Tested,
    WitnessMissing => Tested,
    WitnessTypeMismatch => Tested,
    WitnessReassigned => Untestable("never constructed"),
    WitnessOutsideMain => Tested,
    ModuleRedefined => Tested,
    ModuleNotFound => Tested,
    ModuleIsPrivate => Tested,
    ArgumentMissing => Tested,
    ArgumentTypeMismatch => Tested,
    RawHashUnsupportedType => Tested,
    RawHashJetsUnavailable => Elsewhere("lib.rs: raw_hash_without_sha_jets"),
}

struct Case {
    path: PathBuf,
    expected: String,
    features: UnstableFeatures,
}

impl Case {
    fn load(path: PathBuf) -> Result<Self, String> {
        let text = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
        let mut expected = None;
        let mut features = Vec::new();
        for line in text.lines() {
            let Some(comment) = line.strip_prefix("//") else {
                break;
            };
            let comment = comment.trim();
            if let Some(name) = comment.strip_prefix("error:") {
                expected = Some(name.trim().to_string());
            } else if let Some(names) = comment.strip_prefix("flags:") {
                for name in names.split_whitespace() {
                    features.push(UnstableFeature::from_str(name)?);
                }
            }
        }
        Ok(Self {
            path,
            expected: expected.ok_or("missing `// error:` header")?,
            features: UnstableFeatures::new(features),
        })
    }

    fn sidecar(&self, extension: &str) -> Option<UnresolvedValues> {
        let path = self.path.with_extension(extension);
        let text = std::fs::read_to_string(path).ok()?;
        Some(serde_json::from_str(&text).expect("sidecar file should be valid JSON"))
    }

    /// Compile the case, then check its arguments and witness values, stopping
    /// at the first stage that reports errors. Returns the variant names of
    /// those errors, or `None` if every stage passed.
    fn errors(&self) -> Option<Vec<&'static str>> {
        let text = std::fs::read_to_string(&self.path).unwrap();
        let program = match TemplateAst::new_with_unstable(
            text,
            &self.features,
            Box::new(ElementsJetHinter::new()),
        ) {
            Ok(program) => program,
            Err(diagnostics) => return Some(names(&diagnostics)),
        };

        let mut diagnostics = DiagnosticManager::new();
        let arguments: Arguments = match self.sidecar("args") {
            Some(values) => values.resolve(program.parameters()).unwrap(),
            None => Arguments::default(),
        };
        arguments.is_consistent(program.parameters(), &mut diagnostics);
        if diagnostics.has_errors() {
            return Some(names(&diagnostics));
        }

        let witness: WitnessValues = match self.sidecar("wit") {
            Some(values) => values.resolve(program.witness_types()).unwrap(),
            None => WitnessValues::default(),
        };
        witness.is_consistent(program.witness_types(), &mut diagnostics);
        if diagnostics.has_errors() {
            return Some(names(&diagnostics));
        }

        None
    }
}

fn names(diagnostics: &DiagnosticManager) -> Vec<&'static str> {
    diagnostics
        .diagnostics()
        .iter()
        .map(|diagnostic| variant_name(diagnostic.error()))
        .collect()
}

fn case_paths() -> Vec<PathBuf> {
    let mut paths: Vec<_> = std::fs::read_dir(Path::new(CASES_DIR))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "simf"))
        .collect();
    paths.sort();
    paths
}

#[test]
fn every_case_is_rejected_with_its_error() {
    let mut failures = String::new();
    for path in case_paths() {
        let case = match Case::load(path.clone()) {
            Ok(case) => case,
            Err(error) => {
                writeln!(failures, "{}: {error}", path.display()).unwrap();
                continue;
            }
        };
        match case.errors() {
            None => writeln!(failures, "{}: was accepted", path.display()).unwrap(),
            Some(found) if !found.contains(&case.expected.as_str()) => writeln!(
                failures,
                "{}: expected {}, found {found:?}",
                path.display(),
                case.expected,
            )
            .unwrap(),
            Some(_) => {}
        }
    }
    assert!(failures.is_empty(), "\n{failures}");
}

#[test]
fn every_variant_is_accounted_for() {
    let cases: Vec<Case> = case_paths()
        .into_iter()
        .filter_map(|path| Case::load(path).ok())
        .collect();

    let mut failures = String::new();
    for case in &cases {
        if !COVERAGE.iter().any(|(name, _)| *name == case.expected) {
            writeln!(
                failures,
                "{}: `{}` is not an Error variant",
                case.path.display(),
                case.expected,
            )
            .unwrap();
        }
    }
    for (name, coverage) in COVERAGE {
        if let Elsewhere(reason) | Untestable(reason) = coverage {
            if reason.trim().is_empty() {
                writeln!(failures, "{name}: give a reason ({coverage:?})").unwrap();
            }
        }
        let has_case = cases.iter().any(|case| case.expected == *name);
        match coverage {
            Tested if !has_case => {
                writeln!(failures, "{name}: marked Tested but has no case file").unwrap()
            }
            Elsewhere(_) | Untestable(_) if has_case => writeln!(
                failures,
                "{name}: has a case file, so mark it Tested ({coverage:?})"
            )
            .unwrap(),
            _ => {}
        }
    }
    assert!(failures.is_empty(), "\n{failures}");
}
