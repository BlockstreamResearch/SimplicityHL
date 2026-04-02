use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::error::{Error, RichError, WithSpan as _};
use crate::parse::UseDecl;

/// Powers error reporting by mapping compiler diagnostics to the specific file.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct SourceFile {
    /// The name or path of the source file (e.g., "./simf/main.simf").
    name: Option<Arc<Path>>,
    /// The actual text content of the source file.
    content: Arc<str>,
}

impl From<(&Path, &str)> for SourceFile {
    fn from((name, content): (&Path, &str)) -> Self {
        Self {
            name: Some(Arc::from(name)),
            content: Arc::from(content),
        }
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

/// This defines how a specific dependency root path (e.g. "math")
/// should be resolved to a physical path on the disk, restricted to
/// files executing within the `context_prefix`.
#[derive(Debug, Clone)]
pub struct Remapping {
    /// The base directory that owns this dependency mapping.
    pub context_prefix: PathBuf,
    /// The name used in the `use` statement (e.g., "math").
    pub dependency_root_path: String,
    /// The physical path this dependency root path points to.
    pub target: PathBuf,
}

/// A router for resolving dependencies across multi-file workspaces.
///
/// Mappings are strictly sorted by the longest `context_prefix` match.
/// This mathematical guarantee ensures that if multiple nested directories
/// define the same dependency root path, the most specific (deepest) context wins.
#[derive(Debug, Default)]
pub struct DependencyMap {
    inner: Vec<Remapping>,
}

impl DependencyMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Re-sort the vector in descending order so the longest context paths are always at the front.
    /// This mathematically guarantees that the first match we find is the most specific.
    fn sort_mappings(&mut self) {
        self.inner.sort_by(|a, b| {
            let len_a = a.context_prefix.as_os_str().len();
            let len_b = b.context_prefix.as_os_str().len();
            len_b.cmp(&len_a)
        });
    }

    /// Inserts a dependency remapping without interacting with the physical file system.
    ///
    /// **Warning:** This method completely bypasses OS path canonicalization (`std::fs::canonicalize`).
    /// It is designed strictly for unit testing and virtual file environments where the
    /// provided paths might not actually exist on the hard drive.
    #[cfg(test)]
    pub fn test_insert_without_canonicalize(
        &mut self,
        context: &Path,
        dependency_root_path: String,
        path: &Path,
    ) {
        self.inner.push(Remapping {
            context_prefix: context.to_path_buf(),
            dependency_root_path,
            target: path.to_path_buf(),
        });
        self.sort_mappings();
    }

    /// Add a dependency mapped to a specific calling file's path prefix.
    /// Re-sorts the vector internally to guarantee the Longest Prefix Match.
    pub fn insert(
        &mut self,
        context: &Path,
        dependency_root_path: String,
        path: &Path,
    ) -> io::Result<()> {
        let canon_context = std::fs::canonicalize(context).map_err(|err| {
            io::Error::new(
                err.kind(),
                format!(
                    "Failed to find context directory '{}': {}",
                    context.display(),
                    err
                ),
            )
        })?;

        let canon_path = std::fs::canonicalize(path).map_err(|err| {
            io::Error::new(
                err.kind(),
                format!(
                    "Failed to find library target path '{}': {}",
                    path.display(),
                    err
                ),
            )
        })?;

        self.inner.push(Remapping {
            context_prefix: canon_context,
            dependency_root_path,
            target: canon_path,
        });

        self.sort_mappings();

        Ok(())
    }

    /// Resolve `use dependency_root_path::...` into a physical file path by finding the
    /// most specific library context that owns the current file.
    pub fn resolve_path(
        &self,
        current_file: &Path,
        use_decl: &UseDecl,
    ) -> Result<PathBuf, RichError> {
        // Safely extract the first segment (the dependency root path)
        let parts: Vec<&str> = use_decl.path().iter().map(|s| s.as_inner()).collect();
        let first_segment = parts.first().copied().ok_or_else(|| {
            Error::CannotParse("Empty use path".to_string()).with_span(*use_decl.span())
        })?;

        // Because the vector is sorted by longest prefix,
        // the VERY FIRST match we find is guaranteed to be the correct one.
        for remapping in &self.inner {
            // Check if the current file is executing inside the context's directory tree.
            // This prevents a file in `/project_a/` from using a dependency meant for `/project_b/`
            if !current_file.starts_with(&remapping.context_prefix) {
                continue;
            }

            // Check if the alias matches what the user typed
            if remapping.dependency_root_path == first_segment {
                let mut resolved_path = remapping.target.clone();
                resolved_path.extend(&parts[1..]);
                return Ok(resolved_path);
            }
        }

        // No matches found
        Err(Error::UnknownLibrary(first_segment.to_string())).with_span(*use_decl.span())
    }
}
