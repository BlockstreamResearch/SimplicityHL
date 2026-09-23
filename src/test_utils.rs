use std::fs;
use std::path::PathBuf;
use std::time;

use std::sync::atomic::{AtomicUsize, Ordering};

use crate::ast::ElementsJetHinter;
use crate::{TemplateAst, UnstableFeatures};

/// Compile `src` up to and including analysis, with all unstable features enabled.
/// Return the message of every reported error, in the order they are presented to the user.
pub fn analysis_errors(src: &str) -> Vec<String> {
    match TemplateAst::new_with_unstable(
        src,
        &UnstableFeatures::all(),
        Box::new(ElementsJetHinter::new()),
    ) {
        Ok(_) => Vec::new(),
        Err(diagnostics) => diagnostics
            .presentation_order()
            .into_iter()
            .map(ToString::to_string)
            .collect(),
    }
}

/// Assert that compiling `src` reports exactly the `expected` errors, in order.
#[track_caller]
pub fn assert_errors(src: &str, expected: &[&str]) {
    assert_eq!(
        analysis_errors(src),
        expected,
        "unexpected errors for program:\n{src}"
    );
}

/// A global counter used to guarantee unique directory names for temporary workspaces.
///
/// Because `cargo test` runs tests in parallel, relying solely on system timestamps
/// for directory names can lead to race conditions. If two tests execute at the exact
/// same nanosecond, they will share the same temporary directory. This causes flaky
/// test failures (e.g., one test deleting the directory while the other is still using it).
/// Incrementing this atomic counter ensures every test workspace is strictly unique.
static WORKSPACE_COUNTER: AtomicUsize = AtomicUsize::new(0);

/// A self-cleaning temporary workspace for unit tests.
/// Completely replaces the need for the external `tempfile` crate.
pub struct TempWorkspace {
    root: PathBuf,
}

impl TempWorkspace {
    /// Generates a mathematically unique temporary directory on the OS
    /// and physically creates it.
    pub fn new(test_name: &str) -> Self {
        let unique = time::SystemTime::now()
            .duration_since(time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let count = WORKSPACE_COUNTER.fetch_add(1, Ordering::SeqCst);
        let cwd = std::env::current_dir().unwrap();
        let root = cwd.join("target").join(format!(
            "test-{}-{}-{}-{}",
            test_name,
            std::process::id(),
            unique,
            count
        ));
        fs::create_dir_all(&root).unwrap();
        Self { root }
    }

    /// Helper to physically create a nested directory inside the workspace.
    pub fn create_dir(&self, rel_path: &str) -> PathBuf {
        let path = self.root.join(rel_path);
        fs::create_dir_all(&path).unwrap();
        path
    }

    /// Helper to physically create a file (and any necessary parent directories)
    /// with string contents.
    pub fn create_file(&self, rel_path: &str, contents: &str) -> PathBuf {
        let path = self.root.join(rel_path);

        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }

        fs::write(&path, contents).unwrap();
        path
    }
}

impl Drop for TempWorkspace {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}
