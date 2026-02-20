use std::collections::HashMap;
use std::path::PathBuf;

use crate::parse::UseDecl;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum SourceName {
    Real(PathBuf),
    Virtual(String),
}

impl SourceName {
    pub fn without_extension(&self) -> SourceName {
        match self {
            SourceName::Real(path) => SourceName::Real(path.with_extension("")),
            SourceName::Virtual(name) => SourceName::Virtual(name.clone()),
        }
    }
}

impl Default for SourceName {
    fn default() -> Self {
        SourceName::Virtual("<unnkown>".to_string())
    }
}

pub type LibTable = HashMap<String, PathBuf>;

pub fn get_full_path(libraries: &LibTable, use_decl: &UseDecl) -> Result<PathBuf, String> {
    let parts: Vec<&str> = use_decl.path().iter().map(|s| s.as_ref()).collect();
    let first_segment = parts[0];

    if let Some(lib_root) = libraries.get(first_segment) {
        let mut full_path = lib_root.clone();
        full_path.extend(&parts[1..]);

        return Ok(full_path);
    }

    Err(format!(
        "Unknown dependency '{}'. Did you forget to pass --dep {}=...?",
        first_segment, first_segment,
    ))
}
