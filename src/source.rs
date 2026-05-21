use std::path::Path;
use std::sync::Arc;

/// Powers error reporting by mapping compiler diagnostics to the specific file.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct SourceFile {
    /// The path of the source file (e.g., "./src/main.simf").
    name: Option<Arc<Path>>,
    /// The actual text content of the source file.
    content: Arc<str>,
}

impl From<(&Path, &str)> for SourceFile {
    fn from((name, content): (&Path, &str)) -> Self {
        Self::new(name, Arc::from(content))
    }
}

impl From<CanonSourceFile> for SourceFile {
    fn from(canon_source: CanonSourceFile) -> Self {
        Self::new(canon_source.name().as_path(), canon_source.content())
    }
}

impl SourceFile {
    /// Creates a standard `SourceFile` from a file path and its content.
    pub fn new(name: &Path, content: Arc<str>) -> Self {
        Self {
            name: Some(Arc::from(name)),
            content,
        }
    }

    /// Creates an anonymous `SourceFile` without a file path (e.g., for a single-file programs)
    pub fn anonymous(content: Arc<str>) -> Self {
        Self {
            name: None,
            content,
        }
    }

    pub fn name(&self) -> &Option<Arc<Path>> {
        &self.name
    }

    pub fn content(&self) -> Arc<str> {
        self.content.clone()
    }
}

/// Caches the canonicalized path of a source file to prevent redundant,
/// expensive, and potentially failing filesystem operations.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct CanonSourceFile {
    /// The path of the source file (e.g., "./src/main.simf").
    name: CanonPath,
    /// The actual text content of the source file.
    content: Arc<str>,
}

impl TryFrom<SourceFile> for CanonSourceFile {
    type Error = String;

    fn try_from(source: SourceFile) -> Result<Self, Self::Error> {
        let name = if let Some(root_name) = source.name() {
            CanonPath::canonicalize(root_name)?
        } else {
            return Err(
                "Cannot canonicalize the SourceFile because it is missing a file name.".to_string(),
            );
        };

        Ok(CanonSourceFile {
            name,
            content: source.content(),
        })
    }
}

impl CanonSourceFile {
    pub fn new(name: CanonPath, content: Arc<str>) -> Self {
        Self { name, content }
    }

    pub fn name(&self) -> &CanonPath {
        &self.name
    }

    pub fn str_name(&self) -> String {
        self.name.as_path().display().to_string()
    }

    pub fn content(&self) -> Arc<str> {
        self.content.clone()
    }
}

/// A guaranteed, fully coanonicalized absolute path.
#[derive(Debug, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct CanonPath(Arc<Path>);

impl CanonPath {
    /// Safely resolves an absolute path via the OS and wraps it in a `CanonPath`.
    ///
    /// # Errors
    ///
    /// Returns a `String` containing the OS error if the path does not exist or
    /// cannot be accessed. The caller is expected to map this into a more specific
    /// compiler diagnostic (e.g., `RichError`).
    pub fn canonicalize(path: &Path) -> Result<Self, String> {
        // We use `map_err` here to intercept the generic OS error and enrich
        // it with the specific path that failed
        let canon_path = std::fs::canonicalize(path).map_err(|err| {
            format!(
                "Failed to find library target path '{}' :{}",
                path.display(),
                err
            )
        })?;

        Ok(Self(Arc::from(canon_path.as_path())))
    }

    /// Appends a logical module path to this physical root directory and verifies it.
    /// It automatically appends the `.simf` extension to the final path *before* asking
    /// the OS to verify its existence.
    pub fn join(&self, parts: &[&str]) -> Result<Self, String> {
        let mut new_path = self.0.to_path_buf();

        for part in parts {
            new_path.push(part);
        }

        Self::canonicalize(&new_path.with_extension("simf"))
    }

    /// Check if the current file is executing inside the context's directory tree.
    /// This prevents a file in `/project_a/` from using a dependency meant for `/project_b/`
    pub fn starts_with(&self, path: &CanonPath) -> bool {
        self.as_path().starts_with(path.as_path())
    }

    pub fn as_path(&self) -> &Path {
        &self.0
    }

    #[cfg(test)]
    pub fn dummy_for_test(path: &Path) -> Self {
        Self(Arc::from(path))
    }
}
