use std::path::PathBuf;

use crate::str::{AliasName, FunctionName};

#[derive(Debug, thiserror::Error, Clone, Eq, PartialEq, Hash)]
pub enum Error {
    #[error("Item `{name}` could not be found")]
    UnresolvedItem { name: String },

    #[error("Item `{name}` is private")]
    PrivateItem { name: String },

    #[error("The alias `{name}` was defined multiple times")]
    DuplicateAlias { name: String },

    #[error("Item `{name}` was defined multiple times")]
    RedefinedItem { name: String },

    #[error("Main function cannot be public")]
    MainCannotBePublic,

    #[error("Function `{name}` was defined multiple times")]
    FunctionRedefined { name: FunctionName },

    #[error("Unknown module or library '{name}'")]
    UnknownLibrary { name: String },

    #[error("Main function cannot be alias")]
    MainCannotBeAlias,

    #[error("Type alias `{name}` was defined multiple times")]
    RedefinedAlias { name: AliasName },

    #[error("Local file `{}` not found", filename.display())]
    FileNotFound { filename: PathBuf },

    #[error(
    "File `{}` is part of the local project and must be imported using the `crate::` prefix", path.to_string_lossy()

    )]
    LocalFileImportedAsExternal { path: PathBuf },

    #[error("File `{}` not found in external library `{}`", lib, filename.display())]
    ExternalFileNotFound { lib: String, filename: PathBuf },

    #[error("INTERNAL ERROR: {msg}")]
    Internal { msg: String },

    #[error("Path not found: {}", path.display())]
    DependencyPathNotFound { path: PathBuf },

    #[error("Path must be a directory: {}", path.display())]
    DependencyNotADirectory { path: PathBuf },

    #[error("The '{keyword}' keyword is reserved and cannot be manually mapped. Use the builder's context definitions instead.")]
    ReservedDependencyKeyword { keyword: String },

    #[error("Duplicate dependency mapping: alias '{alias}' is defined multiple times for context '{context}'")]
    DuplicateDependencyAlias { alias: String, context: String },

    #[error(
        "Invalid dependency alias '{alias}': must be a valid identifier and not a reserved keyword"
    )]
    InvalidDependencyIdentifier { alias: String },
}
