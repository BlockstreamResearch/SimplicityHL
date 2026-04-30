use std::io;
use std::path::Path;
use std::sync::Arc;

use crate::driver::{CanonSourceFile, CRATE_STR};
use crate::error::{Error, RichError, WithSpan as _};
use crate::parse::UseDecl;

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

/// A guaranteed, fully coanonicalized absolute path.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
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
}

/// This defines how a specific dependency root path (e.g. "math")
/// should be resolved to a physical path on the disk, restricted to
/// files executing within the `context_prefix`.
#[derive(Debug, Clone)]
pub struct Remapping {
    /// The base directory that owns this dependency mapping.
    pub context_prefix: CanonPath,
    /// The dependency root path name used in the `use` statement (e.g., "math").
    pub drp_name: String,
    /// The physical path this dependency root path points to.
    pub target: CanonPath,
}

/// A router for resolving dependencies across multi-file workspaces.
///
/// Mappings are strictly sorted by the longest `context_prefix` match.
/// This mathematical guarantee ensures that if multiple nested directories
/// define the same dependency root path, the most specific (deepest) context wins.
#[derive(Debug, Clone, Default)]
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
            let len_a = a.context_prefix.as_path().as_os_str().len();
            let len_b = b.context_prefix.as_path().as_os_str().len();
            len_b.cmp(&len_a)
        });
    }

    /// Add a dependency mapped to a specific calling file's path prefix.
    /// Re-sorts the vector internally to guarantee the Longest Prefix Match.
    ///
    /// # Arguments
    ///
    /// * `context` - The physical root directory where this dependency rule applies
    ///   (e.g., `/workspace/frontend`).
    /// * `drp_name` - The Dependency Root Path Name. This is the logical alias the
    ///   programmer types in their source code (e.g., the `"math"` in `use math::vector;`).
    /// * `target` - The physical directory where the compiler should actually
    ///   look for the code (e.g., `/libs/frontend_math`).
    pub fn insert(
        &mut self,
        context: CanonPath,
        drp_name: String,
        target: CanonPath,
    ) -> io::Result<()> {
        self.inner.push(Remapping {
            context_prefix: context,
            drp_name,
            target,
        });

        self.sort_mappings();

        Ok(())
    }

    /// Resolve `use dependency_root_path_name::...` into a physical file path by finding the
    /// most specific library context that owns the current file.
    pub fn resolve_path(
        &self,
        current_file: &CanonPath,
        use_decl: &UseDecl,
    ) -> Result<CanonPath, RichError> {
        let parts = use_decl.path();
        let drp_name = use_decl.drp_name()?;

        // Because the vector is sorted by longest prefix,
        // the VERY FIRST match we find is guaranteed to be the correct one.
        for remapping in &self.inner {
            if !current_file.starts_with(&remapping.context_prefix) {
                continue;
            }

            // Check if the alias matches what the user typed
            if remapping.drp_name == drp_name {
                let resolved = Self::build_and_verify_path(&remapping.target, &parts[1..])
                    .map_err(|failed_path| {
                        let err = if drp_name == CRATE_STR {
                            Error::FileNotFound(failed_path)
                        } else {
                            Error::ExternalFileNotFound(drp_name.to_string(), failed_path)
                        };
                        RichError::new(err, *use_decl.span())
                    })?;

                self.check_local_file_imported_as_external(
                    drp_name,
                    current_file,
                    &resolved,
                    use_decl,
                )?;

                return Ok(resolved);
            }
        }

        // If the unmapped root path is "crate", it means the compiler driver failed to configure the workspace root.
        // "crate" explicitly signals local code and should never be treated as an unknown external library.
        if drp_name == CRATE_STR {
            return Err(Error::Internal(
                "The 'crate' root path was not configured by the compiler.".to_string(),
            ))
            .with_span(*use_decl.span());
        }

        Err(Error::UnknownLibrary(drp_name.to_string())).with_span(*use_decl.span())
    }

    /// Enforces that a local file is imported via `crate::` and not via an external alias.
    fn check_local_file_imported_as_external(
        &self,
        drp_name: &str,
        current_file: &CanonPath,
        resolved: &CanonPath,
        use_decl: &UseDecl,
    ) -> Result<(), RichError> {
        if drp_name == CRATE_STR {
            return Ok(());
        }

        let current_crate = self
            .inner
            .iter()
            .find(|r| current_file.starts_with(&r.context_prefix) && r.drp_name == CRATE_STR);

        let resolved_crate = self
            .inner
            .iter()
            .find(|r| resolved.starts_with(&r.context_prefix) && r.drp_name == CRATE_STR);

        if let (Some(curr), Some(res)) = (current_crate, resolved_crate) {
            if curr.target == res.target {
                return Err(Error::LocalFileImportedAsExternal(
                    resolved.as_path().to_path_buf(),
                ))
                .with_span(*use_decl.span());
            }
        }

        Ok(())
    }

    /// Replace `.join` method to better error handling
    fn build_and_verify_path(
        base_target: &CanonPath,
        module_parts: &[impl ToString],
    ) -> Result<CanonPath, std::path::PathBuf> {
        let mut theoretical_path = base_target.as_path().to_path_buf();
        for part in module_parts {
            theoretical_path.push(part.to_string());
        }
        theoretical_path.set_extension("simf");

        match CanonPath::canonicalize(&theoretical_path) {
            Ok(valid_canon_path) => Ok(valid_canon_path),
            Err(_) => Err(theoretical_path),
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use crate::str::Identifier;
    use crate::test_utils::TempWorkspace;

    use super::*;

    pub fn canon(p: &Path) -> CanonPath {
        CanonPath::canonicalize(p).unwrap_or_else(|_| CanonPath::dummy_for_test(p))
    }

    impl CanonPath {
        pub fn dummy_for_test(path: &Path) -> Self {
            Self(Arc::from(path))
        }
    }

    /// Helper to easily construct a `UseDecl` for path resolution tests.
    fn create_dummy_use_decl(path_segments: &[&str]) -> UseDecl {
        let path: Vec<Identifier> = path_segments
            .iter()
            .map(|&s| Identifier::dummy(s))
            .collect();

        UseDecl::dummy_path(path)
    }

    /// When a user registers the same library dependency root path multiple times
    /// for different folders, the compiler must always check the longest folder path first.
    #[test]
    fn test_sorting_longest_prefix() {
        let ws = TempWorkspace::new("sorting");

        let workspace_dir = canon(&ws.create_dir("workspace"));
        let nested_dir = canon(&ws.create_dir("workspace/project_a/nested"));
        let project_a_dir = canon(&ws.create_dir("workspace/project_a"));

        let target_v1 = canon(&ws.create_dir("lib/math_v1"));
        let target_v3 = canon(&ws.create_dir("lib/math_v3"));
        let target_v2 = canon(&ws.create_dir("lib/math_v2"));

        let mut map = DependencyMap::new();
        map.insert(workspace_dir.clone(), "math".to_string(), target_v1)
            .unwrap();
        map.insert(nested_dir.clone(), "math".to_string(), target_v3)
            .unwrap();
        map.insert(project_a_dir.clone(), "math".to_string(), target_v2)
            .unwrap();

        // The longest prefixes should bubble to the top
        assert_eq!(map.inner[0].context_prefix, nested_dir);
        assert_eq!(map.inner[1].context_prefix, project_a_dir);
        assert_eq!(map.inner[2].context_prefix, workspace_dir);
    }

    /// Projects should not be able to "steal" or accidentally access dependencies
    /// that do not belong to them.
    #[test]
    fn test_context_isolation() {
        let ws = TempWorkspace::new("isolation");

        let project_a = canon(&ws.create_dir("project_a"));
        let target_utils = canon(&ws.create_dir("libs/utils_a"));
        let current_file = canon(&ws.create_file("project_b/main.simf", ""));

        let mut map = DependencyMap::new();
        map.insert(project_a, "utils".to_string(), target_utils)
            .unwrap();

        let use_decl = create_dummy_use_decl(&["utils"]);
        let result = map.resolve_path(&current_file, &use_decl);

        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err().error(),
            Error::UnknownLibrary(..)
        ));
    }

    /// It proves that a highly specific path definition will "override" or "shadow"
    /// a broader path definition.
    #[test]
    fn test_resolve_longest_prefix_match() {
        let ws = TempWorkspace::new("resolve_prefix");

        // 1. Setup Global Context
        let global_context = canon(&ws.create_dir("workspace"));
        let global_target = canon(&ws.create_dir("libs/global_math"));
        let global_expected = canon(&ws.create_file("libs/global_math/vector.simf", ""));

        // 2. Setup Frontend Context
        let frontend_context = canon(&ws.create_dir("workspace/frontend"));
        let frontend_target = canon(&ws.create_dir("libs/frontend_math"));
        let frontend_expected = canon(&ws.create_file("libs/frontend_math/vector.simf", ""));

        let mut map = DependencyMap::new();
        map.insert(global_context, "math".to_string(), global_target)
            .unwrap();
        map.insert(frontend_context, "math".to_string(), frontend_target)
            .unwrap();

        let use_decl = create_dummy_use_decl(&["math", "vector"]);

        // 3. Test Frontend Override
        let frontend_file = canon(&ws.create_file("workspace/frontend/src/main.simf", ""));
        let resolved_frontend = map.resolve_path(&frontend_file, &use_decl).unwrap();
        assert_eq!(resolved_frontend, frontend_expected);

        // 4. Test Global Fallback
        let backend_file = canon(&ws.create_file("workspace/backend/src/main.simf", ""));
        let resolved_backend = map.resolve_path(&backend_file, &use_decl).unwrap();
        assert_eq!(resolved_backend, global_expected);
    }

    /// It proves that a file inside the local project cannot be imported via an external dependency alias.
    #[test]
    fn test_local_file_imported_as_external() {
        let ws = TempWorkspace::new("local_as_ext");

        let project_dir = canon(&ws.create_dir("workspace"));
        ws.create_file("workspace/utils.simf", "");
        let current_file = canon(&ws.create_file("workspace/main.simf", ""));

        let mut map = DependencyMap::new();
        // The driver sets up the crate root
        map.insert(
            project_dir.clone(),
            CRATE_STR.to_string(),
            project_dir.clone(),
        )
        .unwrap();
        // The user tries to alias a folder inside their own project as an external dependency
        map.insert(
            project_dir.clone(),
            "utils_lib".to_string(),
            project_dir.clone(),
        )
        .unwrap();

        let use_decl = create_dummy_use_decl(&["utils_lib", "utils"]);
        let result = map.resolve_path(&current_file, &use_decl);

        assert!(matches!(
            result.unwrap_err().error(),
            Error::LocalFileImportedAsExternal(..)
        ));
    }

    /// It verifies that the "crate" dependency root path successfully resolves
    /// to the local workspace root directory.
    #[test]
    fn test_crate_resolution() {
        let ws = TempWorkspace::new("crate_res");

        let project_dir = canon(&ws.create_dir("workspace"));
        let expected = canon(&ws.create_file("workspace/utils.simf", ""));
        let current_file = canon(&ws.create_file("workspace/main.simf", ""));

        let mut map = DependencyMap::new();
        map.insert(
            project_dir.clone(),
            CRATE_STR.to_string(),
            project_dir.clone(),
        )
        .unwrap();

        let use_decl = create_dummy_use_decl(&[CRATE_STR, "utils"]);
        let result = map.resolve_path(&current_file, &use_decl).unwrap();

        assert_eq!(result, expected);
    }

    /// It proves that the compiler throws an Internal error if the driver forgets
    /// to map the "crate" dependency, rather than an `UnknownLibrary` error.
    #[test]
    fn test_crate_unconfigured_error() {
        let ws = TempWorkspace::new("crate_unconf");
        let current_file = canon(&ws.create_file("workspace/main.simf", ""));

        let map = DependencyMap::new();

        let use_decl = create_dummy_use_decl(&[CRATE_STR, "utils"]);
        let result = map.resolve_path(&current_file, &use_decl);

        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err().error(),
            Error::Internal(msg) if msg.contains("The 'crate' root path was not configured")
        ));
    }

    /// it proves that `start_with()` and `resolve_path()` logic correctly handles files
    /// that are buried deep inside a project's subdirectories.
    #[test]
    fn test_resolve_relative_current_file_against_canonical_context() {
        let ws = TempWorkspace::new("relative_current");

        let context = canon(&ws.create_dir("workspace/frontend"));
        let target = canon(&ws.create_dir("libs/frontend_math"));
        let expected = canon(&ws.create_file("libs/frontend_math/vector.simf", ""));

        let current_file = canon(&ws.create_file("workspace/frontend/src/main.simf", ""));

        let mut map = DependencyMap::new();
        map.insert(context, "math".to_string(), target).unwrap();

        let use_decl = create_dummy_use_decl(&["math", "vector"]);
        let result = map.resolve_path(&current_file, &use_decl).unwrap();

        assert_eq!(result, expected);
    }
}
