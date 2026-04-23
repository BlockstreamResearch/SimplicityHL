use std::fs;
use std::path::PathBuf;
use std::time;

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
        let cwd = std::env::current_dir().unwrap();
        let root = cwd.join("target").join(format!(
            "test-{}-{}-{}",
            test_name,
            std::process::id(),
            unique
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
