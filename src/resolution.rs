use std::sync::Arc;

use crate::driver::CRATE_STR;
use crate::error::{Error, RichError, WithSpan as _};
use crate::parse::UseDecl;
use crate::source::CanonPath;
use crate::str::Identifier;

/// This defines how a specific dependency root path (e.g. "math")
/// should be resolved to a physical path on the disk, restricted to
/// files executing within the `context_prefix`.
#[derive(Debug, Clone)]
pub(crate) struct Remapping {
    /// The base directory that owns this dependency mapping.
    pub(crate) context_prefix: CanonPath,
    /// The dependency root path name used in the `use` statement (e.g., "math").
    pub(crate) drp_name: String,
    /// The physical path this dependency root path points to.
    pub(crate) target: CanonPath,
}

fn is_valid_dependency_identifier(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }
    let mut chars = s.chars();
    let first = chars.next().unwrap();
    if !(first.is_ascii_alphabetic() || first == '_') {
        return false;
    }
    if !chars.all(|c| c.is_ascii_alphanumeric() || c == '_') {
        return false;
    }
    !crate::lexer::is_keyword(s)
}

/// A router for resolving dependencies across multi-file workspaces.
///
/// Mappings are strictly sorted by the longest `context_prefix` match.
/// This mathematical guarantee ensures that if multiple nested directories
/// define the same dependency root path, the most specific (deepest) context wins.
/// This struct must always be constructed via [`DependencyMapBuilder`].
/// Builder guarantees that the vector is never empty and contains no duplicates, so we can safely sort without worrying about edge cases.
#[derive(Debug, Clone)]
pub struct DependencyMap {
    /// External dependency remappings (e.g., `use math::...`)
    remappings: Arc<Vec<Remapping>>,
    /// Package roots for resolving local workspace paths (`crate::...`).
    ///
    /// In a multi-file workspace with nested dependencies,
    /// a file might be part of an external dependency package rather than the top-level
    /// project. These paths are sorted by descending length, allowing the compiler to
    /// match a file to its closest (most deeply nested) owning package root.
    /// This prevents symlink escapes and ensures `crate::` correctly resolves relative
    /// to the dependency's own root directory, rather than the parent workspace root.
    package_roots: Vec<CanonPath>,
}

/// Pre-validated, frozen dependency graph without an entry root.
///
/// Built once from [`DependencyMapBuilder::validate_deps`] — all filesystem checks,
/// identifier validation, and sorting are done at this stage.
#[derive(Debug, Clone)]
pub struct ValidatedDeps {
    /// Already validated and sorted by longest context prefix.
    ///
    /// Wrapped in `Arc` so multiple [`DependencyMap`]'s produced by `with_root`
    /// share the same `Vec` instead of deep-cloning every `Remapping` per call.
    remappings: Arc<Vec<Remapping>>,
    /// Package roots contributed by deps only; entry root is excluded here
    /// because it changes per call. Already deduped and sorted.
    dep_roots: Arc<[CanonPath]>,
}

impl ValidatedDeps {
    /// Attaches a new entry root and produces a [`DependencyMap`].
    ///
    /// Only validates the root directory — all dependency checks were done once
    /// in [`DependencyMapBuilder::validate_deps`] and are not repeated here.
    /// Cost: one `validate_dir` call + one sort of `package_roots`.
    pub fn with_root(&self, entry_root: CanonPath) -> Result<DependencyMap, Error> {
        DependencyMapBuilder::validate_dir(&entry_root)?;

        // Build the full set of package roots: entry root + pre-validated dep roots.
        // No `HashSet` here because for the small `N` we expect (~200 max), allocating a `HashSet`
        // and re-collecting into a `Vec` costs more than sorting then deduplicating in place.
        let mut package_roots: Vec<CanonPath> = std::iter::once(entry_root)
            .chain(self.dep_roots.iter().cloned())
            .collect();

        package_roots.sort_by(Self::cmp_by_path_len_desc);
        package_roots.dedup();

        Ok(DependencyMap {
            // Remappings are already sorted
            remappings: self.remappings.clone(),
            package_roots,
        })
    }

    /// Comparator for sorting paths by descending length, then alphabetically.
    /// Ensures longest-prefix-match works correctly on the resulting vector.
    fn cmp_by_path_len_desc(a: &CanonPath, b: &CanonPath) -> std::cmp::Ordering {
        b.as_path()
            .as_os_str()
            .len()
            .cmp(&a.as_path().as_os_str().len())
            .then_with(|| a.cmp(b))
    }
}

/// Builder for [`DependencyMap`].
///
/// Supports two usage patterns:
///
/// - **Single entry root**: call [`build`](Self::build) directly.
/// - **Multiple entry roots with shared deps**: call [`validate_deps`](Self::validate_deps)
///   once, then call [`with_root`](ValidatedDeps::with_root) for each entry point.
#[derive(Debug, Clone, Default)]
pub struct DependencyMapBuilder {
    deps: Vec<Remapping>,
}

impl DependencyMapBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    /// Convenience method for single-root use cases
    pub fn build(self, entry_root: CanonPath) -> Result<DependencyMap, Error> {
        self.validate_deps()?.with_root(entry_root)
    }

    /// validates and freezes all dependencies into a reusable [`ValidatedDeps`].
    ///
    /// Performs all filesystem checks and sorting exactly once — O(n log n).
    /// The result can then be combined with any number of entry roots via
    /// [`ValidatedDeps::with_root`] without repeating this work.
    pub fn validate_deps(self) -> Result<ValidatedDeps, Error> {
        let mut seen =
            std::collections::HashSet::<(CanonPath, String)>::with_capacity(self.deps.len());
        let mut dep_roots = Vec::<CanonPath>::with_capacity(self.deps.len());
        let mut remappings = Vec::<Remapping>::with_capacity(self.deps.len());

        for dep in self.deps {
            Self::validate_dir(&dep.context_prefix)?;
            Self::validate_dir(&dep.target)?;
            Self::validate_dependency_identifier(&dep.drp_name)?;

            if !seen.insert((dep.context_prefix.clone(), dep.drp_name.clone())) {
                return Err(Error::DuplicateDependencyAlias {
                    alias: dep.drp_name,
                    context: dep.context_prefix.as_path().display().to_string(),
                });
            }

            dep_roots.push(dep.target.clone());
            remappings.push(dep);
        }

        // Re-sort the vector in descending order so the longest context paths are always at the front.
        // This mathematically guarantees that the first match we find is the most specific.
        remappings.sort_by(|a, b| {
            ValidatedDeps::cmp_by_path_len_desc(&a.context_prefix, &b.context_prefix)
                .then_with(|| a.drp_name.cmp(&b.drp_name))
        });

        dep_roots.sort_by(ValidatedDeps::cmp_by_path_len_desc);
        dep_roots.dedup();

        Ok(ValidatedDeps {
            remappings: Arc::new(remappings),
            dep_roots: dep_roots.into(),
        })
    }

    pub fn add_dependency(
        &mut self,
        context: CanonPath,
        alias: String,
        target: CanonPath,
    ) -> &mut Self {
        self.deps.push(Remapping {
            context_prefix: context,
            drp_name: alias,
            target,
        });
        self
    }

    fn validate_dir(path: &CanonPath) -> Result<(), Error> {
        if !path.as_path().exists() {
            return Err(Error::DependencyPathNotFound {
                path: path.as_path().into(),
            });
        }
        if !path.as_path().is_dir() {
            return Err(Error::DependencyNotADirectory {
                path: path.as_path().into(),
            });
        }
        Ok(())
    }

    fn validate_dependency_identifier(alias: &str) -> Result<(), Error> {
        if is_valid_dependency_identifier(alias) {
            return Ok(());
        }
        if alias == CRATE_STR {
            Err(Error::ReservedDependencyKeyword {
                keyword: alias.to_string(),
            })
        } else {
            Err(Error::InvalidDependencyIdentifier {
                alias: alias.to_string(),
            })
        }
    }
}

/// Represents a fully resolved `use` declaration, split into two parts:
/// the physical file on disk and the remaining inline path within it.
///
/// # Example
///
/// ``` md
/// use drp_name::dir1::dir2::simf_file::first_mod::item;
/// //  |______________________________| |______________|
/// //              path                     mod_path
/// ```
#[derive(Debug, Clone)]
pub(crate) struct ResolvedUse {
    /// The resolved `.simf` file this `use` points to.
    /// Represents the root `crate` directory if this is the root file.
    pub(crate) path: CanonPath,

    /// Path segments after the file boundary — inline `mod` names and the final item.
    /// Empty if the `use` points directly to a file-level item.
    #[allow(dead_code)]
    pub(crate) mod_path: Vec<Identifier>,
}

impl DependencyMap {
    /// Returns the package root for the given file, which corresponds to the
    /// target directory of the most specific dependency or the entry root.
    pub fn get_package_root(&self, current_file: &CanonPath) -> Option<&CanonPath> {
        self.package_roots
            .iter()
            .find(|root| current_file.starts_with(root))
    }

    /// Resolve `use dependency_root_path_name::...` into a physical file path by finding the
    /// most specific library context that owns the current file.
    pub fn resolve_path(
        &self,
        current_file: &CanonPath,
        use_decl: &UseDecl,
    ) -> Result<CanonPath, RichError> {
        Ok(self.resolve_path_internal(current_file, use_decl)?.path)
    }

    pub(crate) fn resolve_path_internal(
        &self,
        current_file: &CanonPath,
        use_decl: &UseDecl,
    ) -> Result<ResolvedUse, RichError> {
        let drp_name = use_decl.drp_name()?;
        let span = *use_decl.span();

        if drp_name == CRATE_STR {
            return self.resolve_crate_path(current_file, use_decl);
        }

        // Because the vector is sorted by longest prefix,
        // the VERY FIRST match we find is guaranteed to be the correct one.
        self.remappings
            .iter()
            .find(|r| current_file.starts_with(&r.context_prefix) && r.drp_name == drp_name)
            .ok_or_else(|| {
                RichError::new(
                    Error::UnknownLibrary {
                        name: drp_name.to_string(),
                    },
                    span,
                )
            })
            .and_then(|remapping| self.resolve_external_path(remapping, current_file, use_decl))
    }

    fn resolve_external_path(
        &self,
        remapping: &Remapping,
        current_file: &CanonPath,
        use_decl: &UseDecl,
    ) -> Result<ResolvedUse, RichError> {
        let drp_name = use_decl.drp_name()?;
        let parts_without_drp_name = &use_decl.path()[1..];

        let resolved = Self::build_and_verify_path(&remapping.target, parts_without_drp_name)
            .map_err(|failed_path| {
                RichError::new(
                    Error::ExternalFileNotFound {
                        lib: drp_name.to_string(),
                        filename: failed_path,
                    },
                    *use_decl.span(),
                )
            })?;

        self.check_local_file_imported_as_external(current_file, &resolved.path, use_decl.span())?;
        Ok(resolved)
    }

    /// Resolves `crate::...` imports into a physical file path.
    ///
    /// Attempts physical file resolution first. If that fails and the current file
    /// is at the package root, it falls back to resolving inline items from the main scope.
    fn resolve_crate_path(
        &self,
        current_file: &CanonPath,
        use_decl: &UseDecl,
    ) -> Result<ResolvedUse, RichError> {
        let root = self
            .get_package_root(current_file)
            .ok_or_else(|| Error::Internal {
                msg: "The 'crate' root path was not configured by the compiler.".to_string(),
            })
            .map_err(|e| RichError::new(e, *use_decl.span()))?;

        let parts_without_drp_name = &use_decl.path()[1..];
        let failed_path = match Self::build_and_verify_path(root, parts_without_drp_name) {
            Ok(resolved) => return Ok(resolved),
            Err(path) => path,
        };

        // Fallback: Check if the current file sits directly inside the root directory.
        let is_in_root_dir = current_file.as_path().parent() == Some(root.as_path());
        if is_in_root_dir {
            return Ok(ResolvedUse {
                path: current_file.clone(),
                mod_path: parts_without_drp_name.to_vec(),
            });
        }

        Err(RichError::new(
            Error::FileNotFound {
                filename: failed_path,
            },
            *use_decl.span(),
        ))
    }

    /// Enforces that a local file is imported via `crate::` and not via an external alias.
    fn check_local_file_imported_as_external(
        &self,
        current_file: &CanonPath,
        resolved: &CanonPath,
        use_decl_span: &crate::error::Span,
    ) -> Result<(), RichError> {
        if let (Some(curr), Some(res)) = (
            self.get_package_root(current_file),
            self.get_package_root(resolved),
        ) {
            if curr == res {
                return Err(Error::LocalFileImportedAsExternal {
                    path: resolved.as_path().to_path_buf(),
                })
                .with_span(*use_decl_span);
            }
        }
        Ok(())
    }

    /// Walks `module_parts` greedily. Directories first, then the first matching `.simf` file.
    /// Remaining segments after the file boundary are collected as inline `mod_path`.
    ///
    /// # Errors
    ///
    /// Returns the failed candidate path as a raw `PathBuf`, without any additional context.
    /// The caller is responsible for enriching this into a [`RichError`] with the appropriate
    /// span, library name, and any other diagnostic information.
    fn build_and_verify_path(
        base_target: &CanonPath,
        module_parts: &[Identifier],
    ) -> Result<ResolvedUse, std::path::PathBuf> {
        let mut path = base_target.as_path().to_path_buf();

        let mut iter = module_parts.iter();

        while let Some(part) = iter.next() {
            let joined = path.join(part.as_inner());
            if joined.is_dir() {
                path = joined;
                continue;
            }

            let mut file_candidate = joined;
            file_candidate.set_extension("simf");

            // Error context is intentionally dropped here. Callers enrich it with span, lib name, etc.
            let resolved =
                CanonPath::canonicalize(&file_candidate).map_err(|_| file_candidate.clone())?;

            if !resolved.starts_with(base_target) {
                return Err(file_candidate);
            }

            return Ok(ResolvedUse {
                path: resolved,
                mod_path: iter.cloned().collect(), // Add only remaining elements
            });
        }

        Err(path)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use crate::str::Identifier;
    use crate::test_utils::TempWorkspace;
    use std::path::Path;

    use super::*;

    pub fn canon(p: &Path) -> CanonPath {
        CanonPath::canonicalize(p).unwrap_or_else(|_| CanonPath::dummy_for_test(p))
    }

    /// Helper to easily construct a `UseDecl` for path resolution tests.
    fn create_dummy_use_decl(path_segments: &[&str]) -> UseDecl {
        let path: Vec<Identifier> = path_segments
            .iter()
            .map(|&s| Identifier::dummy(s))
            .collect();

        UseDecl::dummy_path(path)
    }

    /// Creates directories under `ws` and returns their canonical paths.
    fn dirs<const N: usize>(ws: &TempWorkspace, paths: [&str; N]) -> [CanonPath; N] {
        paths.map(|p| canon(&ws.create_dir(p)))
    }

    /// Creates empty files under `ws` and returns their canonical paths.
    fn files<const N: usize>(ws: &TempWorkspace, paths: [&str; N]) -> [CanonPath; N] {
        paths.map(|p| canon(&ws.create_file(p, "")))
    }

    /// Builds a `DependencyMap`, hiding the `.clone()` and `.to_string()` noise of `add_dependency`.
    pub(crate) fn build_map(
        root: &CanonPath,
        deps: &[(&CanonPath, &str, &CanonPath)],
    ) -> Result<DependencyMap, Error> {
        let mut builder = DependencyMapBuilder::new();
        for (ctx, alias, target) in deps {
            builder.add_dependency((*ctx).clone(), alias.to_string(), (*target).clone());
        }
        builder.build(root.clone())
    }

    /// Attempting to manually map the `crate` keyword using `insert()` must result in an error.
    #[test]
    fn test_insert_crate_fails() {
        let ws = TempWorkspace::new("insert_crate_fail");
        let [project_dir] = dirs(&ws, ["workspace"]);

        let result = build_map(&project_dir, &[(&project_dir, CRATE_STR, &project_dir)]);

        assert!(matches!(
            result.unwrap_err(),
            Error::ReservedDependencyKeyword { .. }
        ));
    }

    /// When a user registers the same library dependency root path multiple times
    /// for different folders, the compiler must always check the longest folder path first.
    #[test]
    fn test_sorting_longest_prefix() {
        let ws = TempWorkspace::new("sorting");

        let [workspace_dir, project_a_dir, nested_dir, target_v1, target_v2, target_v3] = dirs(
            &ws,
            [
                "workspace",
                "workspace/project_a",
                "workspace/project_a/nested",
                "lib/math_v1",
                "lib/math_v2",
                "lib/math_v3",
            ],
        );

        let map = build_map(
            &workspace_dir,
            &[
                (&workspace_dir, "math", &target_v1),
                (&nested_dir, "math", &target_v3),
                (&project_a_dir, "math", &target_v2),
            ],
        )
        .unwrap();

        // The longest prefixes should bubble to the top
        assert_eq!(map.remappings[0].context_prefix, nested_dir);
        assert_eq!(map.remappings[1].context_prefix, project_a_dir);
        assert_eq!(map.remappings[2].context_prefix, workspace_dir);
    }

    /// Projects should not be able to "steal" or accidentally access dependencies
    /// that do not belong to them.
    #[test]
    fn test_context_isolation() {
        let ws = TempWorkspace::new("isolation");

        let [project_a, target_utils] = dirs(&ws, ["project_a", "libs/utils_a"]);
        let [current_file] = files(&ws, ["project_b/main.simf"]);

        let map = build_map(&project_a, &[(&project_a, "utils", &target_utils)]).unwrap();

        let use_decl = create_dummy_use_decl(&["utils"]);
        let result = map.resolve_path(&current_file, &use_decl);

        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err().error(),
            Error::UnknownLibrary { .. }
        ));
    }

    /// It proves that a highly specific path definition will "override" or "shadow"
    /// a broader path definition.
    #[test]
    fn test_resolve_longest_prefix_match() {
        let ws = TempWorkspace::new("resolve_prefix");

        let [global_context, global_target, frontend_context, frontend_target] = dirs(
            &ws,
            [
                "workspace",
                "libs/global_math",
                "workspace/frontend",
                "libs/frontend_math",
            ],
        );

        let [global_expected, frontend_expected, frontend_file, backend_file] = files(
            &ws,
            [
                "libs/global_math/vector.simf",
                "libs/frontend_math/vector.simf",
                "workspace/frontend/src/main.simf",
                "workspace/backend/src/main.simf",
            ],
        );

        let map = build_map(
            &global_context,
            &[
                (&global_context, "math", &global_target),
                (&frontend_context, "math", &frontend_target),
            ],
        )
        .unwrap();

        let use_decl = create_dummy_use_decl(&["math", "vector"]);

        assert_eq!(
            map.resolve_path(&frontend_file, &use_decl).unwrap(),
            frontend_expected
        );
        assert_eq!(
            map.resolve_path(&backend_file, &use_decl).unwrap(),
            global_expected
        );
    }

    /// It proves that a file inside the local project cannot be imported via an external dependency alias.
    #[test]
    fn test_local_file_imported_as_external() {
        let ws = TempWorkspace::new("local_as_ext");

        let [project_dir] = dirs(&ws, ["workspace"]);
        let [_utils_file, current_file] =
            files(&ws, ["workspace/utils.simf", "workspace/main.simf"]);

        let map = build_map(&project_dir, &[(&project_dir, "utils_lib", &project_dir)]).unwrap();

        let use_decl = create_dummy_use_decl(&["utils_lib", "utils"]);
        let result = map.resolve_path(&current_file, &use_decl);

        assert!(matches!(
            result.unwrap_err().error(),
            Error::LocalFileImportedAsExternal { .. }
        ));
    }

    /// It verifies that the "crate" dependency root path successfully resolves
    /// to the local workspace root directory.
    #[test]
    fn test_crate_resolution() {
        let ws = TempWorkspace::new("crate_res");

        let [project_dir] = dirs(&ws, ["workspace"]);
        let [expected, current_file] = files(&ws, ["workspace/utils.simf", "workspace/main.simf"]);

        let map = build_map(&project_dir, &[]).unwrap();

        let use_decl = create_dummy_use_decl(&[CRATE_STR, "utils"]);
        let result = map.resolve_path(&current_file, &use_decl).unwrap();

        assert_eq!(result, expected);
    }

    /// It proves that the compiler throws an Internal error if a file attempting
    /// to resolve `crate::` is mysteriously located completely outside any known
    /// package root.
    #[test]
    fn test_crate_unconfigured_error() {
        let ws = TempWorkspace::new("crate_unconf");

        let [other_dir] = dirs(&ws, ["other_dir"]);
        let [current_file] = files(&ws, ["workspace/main.simf"]);

        let map = build_map(&other_dir, &[]).unwrap();

        let use_decl = create_dummy_use_decl(&[CRATE_STR, "utils"]);
        let result = map.resolve_path(&current_file, &use_decl);

        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err().error(),
            Error::Internal{msg} if msg.contains("The 'crate' root path was not configured")
        ));
    }

    /// it proves that `start_with()` and `resolve_path()` logic correctly handles files
    /// that are buried deep inside a project's subdirectories.
    #[test]
    fn test_resolve_relative_current_file_against_canonical_context() {
        let ws = TempWorkspace::new("relative_current");

        let [context, target] = dirs(&ws, ["workspace/frontend", "libs/frontend_math"]);
        let [expected, current_file] = files(
            &ws,
            [
                "libs/frontend_math/vector.simf",
                "workspace/frontend/src/main.simf",
            ],
        );

        let map = build_map(&context, &[(&context, "math", &target)]).unwrap();

        let use_decl = create_dummy_use_decl(&["math", "vector"]);
        let result = map.resolve_path(&current_file, &use_decl).unwrap();

        assert_eq!(result, expected);
    }

    #[test]
    fn test_builder_rejects_file_as_directory() {
        let ws = TempWorkspace::new("file_as_dir");

        let [valid_dir] = dirs(&ws, ["workspace/valid_dir"]);
        let [file_path] = files(&ws, ["workspace/not_a_dir.simf"]);

        let res1 = build_map(&file_path, &[]);
        assert!(matches!(
            res1.unwrap_err(),
            Error::DependencyNotADirectory { .. }
        ));

        let res2 = build_map(&valid_dir, &[(&file_path, "alias", &valid_dir)]);
        assert!(matches!(
            res2.unwrap_err(),
            Error::DependencyNotADirectory { .. }
        ));

        let res3 = build_map(&valid_dir, &[(&valid_dir, "alias", &file_path)]);
        assert!(matches!(
            res3.unwrap_err(),
            Error::DependencyNotADirectory { .. }
        ));
    }

    #[test]
    fn test_builder_rejects_non_existent_paths() {
        let ws = TempWorkspace::new("non_existent");

        let [valid_dir] = dirs(&ws, ["workspace/valid_dir"]);
        let fake_path = CanonPath::dummy_for_test(Path::new("/does/not/exist/in/this/universe"));

        let res = build_map(&valid_dir, &[(&valid_dir, "alias", &fake_path)]);
        assert!(matches!(
            res.unwrap_err(),
            Error::DependencyPathNotFound { .. }
        ));
    }

    #[test]
    fn test_builder_rejects_invalid_identifiers() {
        let ws = TempWorkspace::new("invalid_idents");
        let [valid_dir] = dirs(&ws, ["workspace/valid_dir"]);

        let bad_aliases = vec!["", "123lib", "my-lib", "lib!", " space "];

        for bad_alias in bad_aliases {
            let res = build_map(&valid_dir, &[(&valid_dir, bad_alias, &valid_dir)]);
            assert!(
                matches!(res.unwrap_err(), Error::InvalidDependencyIdentifier { .. }),
                "Builder should reject alias: '{}'",
                bad_alias
            );
        }
    }

    #[test]
    fn test_builder_rejects_reserved_keywords() {
        let ws = TempWorkspace::new("reserved_keywords");
        let [valid_dir] = dirs(&ws, ["workspace/valid_dir"]);

        for kw in crate::lexer::KEYWORDS.to_vec() {
            let res = build_map(&valid_dir, &[(&valid_dir, kw, &valid_dir)]);
            let err = res.unwrap_err();

            if kw == CRATE_STR {
                assert!(matches!(err, Error::ReservedDependencyKeyword { .. }));
            } else {
                assert!(matches!(err, Error::InvalidDependencyIdentifier { .. }));
            }
        }
    }

    #[test]
    fn test_builder_rejects_duplicates() {
        let ws = TempWorkspace::new("duplicates");

        let [valid_dir, target1, target2] = dirs(
            &ws,
            [
                "workspace/valid_dir",
                "workspace/target1",
                "workspace/target2",
            ],
        );

        let res = build_map(
            &valid_dir,
            &[
                (&valid_dir, "alias", &target1),
                (&valid_dir, "alias", &target2),
            ],
        );

        assert!(matches!(
            res.unwrap_err(),
            Error::DuplicateDependencyAlias { .. }
        ));
    }

    #[test]
    fn test_resolve_rejects_escaping_package_root() {
        let ws = TempWorkspace::new("escaping_root");

        let [context, target] = dirs(&ws, ["workspace", "libs/target"]);
        let [current_file, _outside_file] =
            files(&ws, ["workspace/main.simf", "libs/escaped.simf"]);

        let map = build_map(&context, &[(&context, "alias", &target)]).unwrap();

        let use_decl = create_dummy_use_decl(&["alias", "..", "escaped"]);
        let result = map.resolve_path(&current_file, &use_decl);

        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("not found"));
    }

    /// A dependency package should not be able to expose a symlinked source file
    /// whose canonical path escapes the dependency root.
    #[cfg(unix)]
    #[test]
    fn test_dependency_symlink_escape_rejected() {
        let ws = TempWorkspace::new("dependency_symlink_escape");

        let [workspace_dir] = dirs(&ws, ["workspace"]);

        let dependency_dir_path = ws.create_dir("deps/package");
        let escaped_file = ws.create_file("outside/foo.simf", "");
        std::os::unix::fs::symlink(&escaped_file, dependency_dir_path.join("foo.simf")).unwrap();

        let dependency_dir = canon(&dependency_dir_path);
        let [current_file] = files(&ws, ["workspace/main.simf"]);

        let map = build_map(&workspace_dir, &[(&workspace_dir, "dep", &dependency_dir)]).unwrap();

        let use_decl = create_dummy_use_decl(&["dep", "foo"]);
        map.resolve_path(&current_file, &use_decl)
            .expect_err("dependency symlink escape was accepted");
    }

    /// It proves that the builder correctly deduplicates `package_roots`
    /// even if multiple roots have the exact same string length.
    #[test]
    fn test_package_roots_deduplication() {
        let ws = TempWorkspace::new("dedup_roots");

        let [workspace_dir, lib_a, lib_b] =
            dirs(&ws, ["workspace", "workspace/libs/A", "workspace/libs/B"]);

        let map = build_map(
            &workspace_dir,
            &[
                (&workspace_dir, "lib_a", &lib_a),
                (&workspace_dir, "lib_b", &lib_b),
                (&lib_b, "lib_a", &lib_a),
            ],
        )
        .unwrap();

        // The package roots should only contain workspace_dir, lib_a, and lib_b (exactly 3 unique roots).
        assert_eq!(
            map.package_roots.len(),
            3,
            "Package roots were not correctly deduplicated"
        );
    }

    /// It proves that if a dependency is nested physically inside the entry root,
    /// files inside the dependency correctly resolve `crate::` to their own sandbox boundary,
    /// and NOT the parent workspace boundary.
    #[test]
    fn test_crate_resolves_to_closest_package_root() {
        let ws = TempWorkspace::new("closest_root");

        let [workspace_dir, lib_dir] = dirs(&ws, ["workspace", "workspace/libs/math"]);
        let [lib_file] = files(&ws, ["workspace/libs/math/vector.simf"]);

        let map = build_map(&workspace_dir, &[(&workspace_dir, "math", &lib_dir)]).unwrap();

        let lib_crate = map.get_package_root(&lib_file).unwrap();
        assert_eq!(
            lib_crate, &lib_dir,
            "Nested dependency did not securely shadow the parent workspace root"
        );
    }
}
