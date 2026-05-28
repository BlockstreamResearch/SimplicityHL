use crate::driver::CRATE_STR;
use crate::error::{Error, RichError, WithSpan as _};
use crate::parse::UseDecl;
use crate::source::CanonPath;

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
    remappings: Vec<Remapping>,
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

#[derive(Debug, Clone)]
pub struct DependencyMapBuilder {
    entry_root: CanonPath,
    deps: Vec<Remapping>,
}

impl DependencyMapBuilder {
    pub fn new(entry_root: CanonPath) -> Self {
        Self {
            entry_root,
            deps: Vec::new(),
        }
    }

    pub fn add_dependency(mut self, context: CanonPath, alias: String, target: CanonPath) -> Self {
        self.deps.push(Remapping {
            context_prefix: context,
            drp_name: alias,
            target,
        });
        self
    }

    pub fn build(self) -> Result<DependencyMap, Error> {
        let mut remappings = Vec::new();
        let mut crate_roots = Vec::new();

        // This guarantees that `crate_roots` is never empty, so `get_package_root()`
        // will always return `Some()` for files under the entry root.
        let root = self.entry_root;
        if !root.as_path().exists() {
            return Err(Error::DependencyPathNotFound {
                path: root.as_path().into(),
            });
        }
        if !root.as_path().is_dir() {
            return Err(Error::DependencyNotADirectory {
                path: root.as_path().into(),
            });
        }
        crate_roots.push(root);

        for dep in self.deps {
            if !dep.context_prefix.as_path().exists() {
                return Err(Error::DependencyPathNotFound {
                    path: dep.context_prefix.as_path().into(),
                });
            }
            if !dep.context_prefix.as_path().is_dir() {
                return Err(Error::DependencyNotADirectory {
                    path: dep.context_prefix.as_path().into(),
                });
            }
            if !dep.target.as_path().exists() {
                return Err(Error::DependencyPathNotFound {
                    path: dep.target.as_path().into(),
                });
            }
            if !dep.target.as_path().is_dir() {
                return Err(Error::DependencyNotADirectory {
                    path: dep.target.as_path().into(),
                });
            }

            if !is_valid_dependency_identifier(&dep.drp_name) {
                if dep.drp_name == CRATE_STR {
                    return Err(Error::ReservedDependencyKeyword {
                        keyword: dep.drp_name,
                    });
                }
                return Err(Error::InvalidDependencyIdentifier {
                    alias: dep.drp_name,
                });
            }

            // Reject duplicates: same context and same alias
            if remappings.iter().any(|r: &Remapping| {
                r.context_prefix == dep.context_prefix && r.drp_name == dep.drp_name
            }) {
                return Err(Error::DuplicateDependencyAlias {
                    alias: dep.drp_name.clone(),
                    context: dep.context_prefix.as_path().display().to_string(),
                });
            }

            crate_roots.push(dep.target.clone());
            remappings.push(dep);
        }

        // Sort package roots by length descending (for longest prefix match),
        // and then alphabetically to group duplicates together for deduplication.
        crate_roots.sort_by(|a, b| {
            let len_a = a.as_path().as_os_str().len();
            let len_b = b.as_path().as_os_str().len();
            len_b.cmp(&len_a).then_with(|| a.cmp(b))
        });
        crate_roots.dedup();

        let mut map = DependencyMap {
            remappings,
            package_roots: crate_roots,
        };
        map.sort_mappings();
        Ok(map)
    }
}

impl DependencyMap {
    /// Re-sort the vector in descending order so the longest context paths are always at the front.
    /// This mathematically guarantees that the first match we find is the most specific.
    fn sort_mappings(&mut self) {
        self.remappings.sort_by(|a, b| {
            let len_a = a.context_prefix.as_path().as_os_str().len();
            let len_b = b.context_prefix.as_path().as_os_str().len();
            len_b
                .cmp(&len_a)
                .then_with(|| a.context_prefix.cmp(&b.context_prefix))
                .then_with(|| a.drp_name.cmp(&b.drp_name))
        });
    }

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
        let parts = use_decl.path();
        let drp_name = use_decl.drp_name()?;

        if drp_name == CRATE_STR {
            return self.resolve_crate_path(current_file, use_decl, &parts);
        }

        // Because the vector is sorted by longest prefix,
        // the VERY FIRST match we find is guaranteed to be the correct one.
        for remapping in &self.remappings {
            if !current_file.starts_with(&remapping.context_prefix) {
                continue;
            }

            // Check if the alias matches what the user typed
            if remapping.drp_name == drp_name {
                return self.resolve_external_path(remapping, current_file, use_decl, &parts);
            }
        }

        Err(Error::UnknownLibrary {
            name: drp_name.to_string(),
        })
        .with_span(*use_decl.span())
    }

    fn resolve_external_path(
        &self,
        remapping: &Remapping,
        current_file: &CanonPath,
        use_decl: &UseDecl,
        parts: &[&str],
    ) -> Result<CanonPath, RichError> {
        let drp_name = use_decl.drp_name()?;

        let resolved = Self::build_and_verify_path(&remapping.target, &parts[1..])
            .map_err(|failed_path| Error::ExternalFileNotFound {
                lib: drp_name.to_string(),
                filename: failed_path,
            })
            .with_span(*use_decl.span())?;

        if !resolved.starts_with(&remapping.target) {
            return Err(Error::ExternalFileNotFound {
                lib: drp_name.to_string(),
                filename: resolved.as_path().to_path_buf(),
            })
            .with_span(*use_decl.span());
        }

        self.check_local_file_imported_as_external(current_file, &resolved, use_decl)?;

        Ok(resolved)
    }

    /// Resolves `crate::...` imports into a physical file path.
    fn resolve_crate_path(
        &self,
        current_file: &CanonPath,
        use_decl: &UseDecl,
        parts: &[&str],
    ) -> Result<CanonPath, RichError> {
        let root = self
            .get_package_root(current_file)
            .ok_or_else(|| Error::Internal {
                msg: "The 'crate' root path was not configured by the compiler.".to_string(),
            })
            .with_span(*use_decl.span())?;

        let resolved = Self::build_and_verify_path(root, &parts[1..])
            .map_err(|failed_path| Error::FileNotFound {
                filename: failed_path,
            })
            .with_span(*use_decl.span())?;

        if !resolved.starts_with(root) {
            return Err(Error::FileNotFound {
                filename: resolved.as_path().to_path_buf(),
            })
            .with_span(*use_decl.span());
        }

        Ok(resolved)
    }

    /// Enforces that a local file is imported via `crate::` and not via an external alias.
    fn check_local_file_imported_as_external(
        &self,
        current_file: &CanonPath,
        resolved: &CanonPath,
        use_decl: &UseDecl,
    ) -> Result<(), RichError> {
        let current_crate = self.get_package_root(current_file);
        let resolved_crate = self.get_package_root(resolved);

        if let (Some(curr), Some(res)) = (current_crate, resolved_crate) {
            if curr == res {
                return Err(Error::LocalFileImportedAsExternal {
                    path: resolved.as_path().to_path_buf(),
                })
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

    /// Attempting to manually map the `crate` keyword using `insert()` must result in an error.
    #[test]
    fn test_insert_crate_fails() {
        let ws = TempWorkspace::new("insert_crate_fail");
        let project_dir = canon(&ws.create_dir("workspace"));

        let result = DependencyMapBuilder::new(project_dir.clone())
            .add_dependency(
                project_dir.clone(),
                CRATE_STR.to_string(),
                project_dir.clone(),
            )
            .build();

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

        let workspace_dir = canon(&ws.create_dir("workspace"));
        let nested_dir = canon(&ws.create_dir("workspace/project_a/nested"));
        let project_a_dir = canon(&ws.create_dir("workspace/project_a"));

        let target_v1 = canon(&ws.create_dir("lib/math_v1"));
        let target_v3 = canon(&ws.create_dir("lib/math_v3"));
        let target_v2 = canon(&ws.create_dir("lib/math_v2"));

        let map = DependencyMapBuilder::new(workspace_dir.clone())
            .add_dependency(workspace_dir.clone(), "math".to_string(), target_v1)
            .add_dependency(nested_dir.clone(), "math".to_string(), target_v3)
            .add_dependency(project_a_dir.clone(), "math".to_string(), target_v2)
            .build()
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

        let project_a = canon(&ws.create_dir("project_a"));
        let target_utils = canon(&ws.create_dir("libs/utils_a"));
        let current_file = canon(&ws.create_file("project_b/main.simf", ""));

        let map = DependencyMapBuilder::new(project_a.clone())
            .add_dependency(project_a, "utils".to_string(), target_utils)
            .build()
            .unwrap();

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

        let global_context = canon(&ws.create_dir("workspace"));
        let global_target = canon(&ws.create_dir("libs/global_math"));
        let global_expected = canon(&ws.create_file("libs/global_math/vector.simf", ""));

        let frontend_context = canon(&ws.create_dir("workspace/frontend"));
        let frontend_target = canon(&ws.create_dir("libs/frontend_math"));
        let frontend_expected = canon(&ws.create_file("libs/frontend_math/vector.simf", ""));

        let map = DependencyMapBuilder::new(global_context.clone())
            .add_dependency(global_context, "math".to_string(), global_target)
            .add_dependency(frontend_context, "math".to_string(), frontend_target)
            .build()
            .unwrap();

        let use_decl = create_dummy_use_decl(&["math", "vector"]);

        let frontend_file = canon(&ws.create_file("workspace/frontend/src/main.simf", ""));
        let resolved_frontend = map.resolve_path(&frontend_file, &use_decl).unwrap();
        assert_eq!(resolved_frontend, frontend_expected);

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

        let map = DependencyMapBuilder::new(project_dir.clone())
            .add_dependency(
                project_dir.clone(),
                "utils_lib".to_string(),
                project_dir.clone(),
            )
            .build()
            .unwrap();

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

        let project_dir = canon(&ws.create_dir("workspace"));
        let expected = canon(&ws.create_file("workspace/utils.simf", ""));
        let current_file = canon(&ws.create_file("workspace/main.simf", ""));

        let map = DependencyMapBuilder::new(project_dir.clone())
            .build()
            .unwrap();

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
        let current_file = canon(&ws.create_file("workspace/main.simf", ""));

        let other_dir = canon(&ws.create_dir("other_dir"));
        let map = DependencyMapBuilder::new(other_dir).build().unwrap();

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

        let context = canon(&ws.create_dir("workspace/frontend"));
        let target = canon(&ws.create_dir("libs/frontend_math"));
        let expected = canon(&ws.create_file("libs/frontend_math/vector.simf", ""));

        let current_file = canon(&ws.create_file("workspace/frontend/src/main.simf", ""));

        let map = DependencyMapBuilder::new(context.clone())
            .add_dependency(context, "math".to_string(), target)
            .build()
            .unwrap();

        let use_decl = create_dummy_use_decl(&["math", "vector"]);
        let result = map.resolve_path(&current_file, &use_decl).unwrap();

        assert_eq!(result, expected);
    }

    #[test]
    fn test_builder_rejects_file_as_directory() {
        let ws = TempWorkspace::new("file_as_dir");
        let file_path = canon(&ws.create_file("workspace/not_a_dir.simf", ""));
        let valid_dir = canon(&ws.create_dir("workspace/valid_dir"));

        let res1 = DependencyMapBuilder::new(file_path.clone()).build();
        assert!(matches!(
            res1.unwrap_err(),
            Error::DependencyNotADirectory { .. }
        ));

        let res2 = DependencyMapBuilder::new(valid_dir.clone())
            .add_dependency(file_path.clone(), "alias".to_string(), valid_dir.clone())
            .build();
        assert!(matches!(
            res2.unwrap_err(),
            Error::DependencyNotADirectory { .. }
        ));

        let res3 = DependencyMapBuilder::new(valid_dir.clone())
            .add_dependency(valid_dir.clone(), "alias".to_string(), file_path)
            .build();
        assert!(matches!(
            res3.unwrap_err(),
            Error::DependencyNotADirectory { .. }
        ));
    }

    #[test]
    fn test_builder_rejects_non_existent_paths() {
        let ws = TempWorkspace::new("non_existent");
        let valid_dir = canon(&ws.create_dir("workspace/valid_dir"));
        let fake_path = CanonPath::dummy_for_test(Path::new("/does/not/exist/in/this/universe"));

        let res = DependencyMapBuilder::new(valid_dir.clone())
            .add_dependency(valid_dir.clone(), "alias".to_string(), fake_path)
            .build();
        assert!(matches!(
            res.unwrap_err(),
            Error::DependencyPathNotFound { .. }
        ));
    }

    #[test]
    fn test_builder_rejects_invalid_identifiers() {
        let ws = TempWorkspace::new("invalid_idents");
        let valid_dir = canon(&ws.create_dir("workspace/valid_dir"));

        let bad_aliases = vec!["", "123lib", "my-lib", "lib!", " space "];

        for bad_alias in bad_aliases {
            let res = DependencyMapBuilder::new(valid_dir.clone())
                .add_dependency(valid_dir.clone(), bad_alias.to_string(), valid_dir.clone())
                .build();
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
        let valid_dir = canon(&ws.create_dir("workspace/valid_dir"));

        let keywords = crate::lexer::KEYWORDS.to_vec();

        for kw in keywords {
            let res = DependencyMapBuilder::new(valid_dir.clone())
                .add_dependency(valid_dir.clone(), kw.to_string(), valid_dir.clone())
                .build();
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
        let valid_dir = canon(&ws.create_dir("workspace/valid_dir"));
        let target1 = canon(&ws.create_dir("workspace/target1"));
        let target2 = canon(&ws.create_dir("workspace/target2"));

        let res = DependencyMapBuilder::new(valid_dir.clone())
            .add_dependency(valid_dir.clone(), "alias".to_string(), target1)
            .add_dependency(valid_dir.clone(), "alias".to_string(), target2)
            .build();

        assert!(matches!(
            res.unwrap_err(),
            Error::DuplicateDependencyAlias { .. }
        ));
    }

    #[test]
    fn test_resolve_rejects_escaping_package_root() {
        let ws = TempWorkspace::new("escaping_root");
        let context = canon(&ws.create_dir("workspace"));
        let target = canon(&ws.create_dir("libs/target"));
        let current_file = canon(&ws.create_file("workspace/main.simf", ""));

        let _outside_file = canon(&ws.create_file("libs/escaped.simf", ""));

        let map = DependencyMapBuilder::new(context.clone())
            .add_dependency(context, "alias".to_string(), target.clone())
            .build()
            .unwrap();

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

        let workspace_dir = canon(&ws.create_dir("workspace"));
        let dependency_dir_path = ws.create_dir("deps/package");
        let escaped_file = ws.create_file("outside/foo.simf", "");
        std::os::unix::fs::symlink(&escaped_file, dependency_dir_path.join("foo.simf")).unwrap();

        let dependency_dir = canon(&dependency_dir_path);
        let current_file = canon(&ws.create_file("workspace/main.simf", ""));

        let map = DependencyMapBuilder::new(workspace_dir.clone())
            .add_dependency(workspace_dir, "dep".to_string(), dependency_dir)
            .build()
            .unwrap();

        let use_decl = create_dummy_use_decl(&["dep", "foo"]);
        map.resolve_path(&current_file, &use_decl)
            .expect_err("dependency symlink escape was accepted");
    }

    /// It proves that the builder correctly deduplicates `package_roots`
    /// even if multiple roots have the exact same string length.
    #[test]
    fn test_package_roots_deduplication() {
        let ws = TempWorkspace::new("dedup_roots");

        let workspace_dir = canon(&ws.create_dir("workspace"));
        let lib_a = canon(&ws.create_dir("workspace/libs/A"));
        let lib_b = canon(&ws.create_dir("workspace/libs/B"));

        let map = DependencyMapBuilder::new(workspace_dir.clone())
            .add_dependency(workspace_dir.clone(), "lib_a".to_string(), lib_a.clone())
            .add_dependency(workspace_dir.clone(), "lib_b".to_string(), lib_b.clone())
            .add_dependency(lib_b.clone(), "lib_a".to_string(), lib_a.clone())
            .build()
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
        let workspace_dir = canon(&ws.create_dir("workspace"));
        let lib_dir = canon(&ws.create_dir("workspace/libs/math"));

        let map = DependencyMapBuilder::new(workspace_dir.clone())
            .add_dependency(workspace_dir.clone(), "math".to_string(), lib_dir.clone())
            .build()
            .unwrap();

        let lib_file = canon(&ws.create_file("workspace/libs/math/vector.simf", ""));
        let lib_crate = map.get_package_root(&lib_file).unwrap();
        assert_eq!(
            lib_crate, &lib_dir,
            "Nested dependency did not securely shadow the parent workspace root"
        );
    }
}
