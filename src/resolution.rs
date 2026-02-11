use std::collections::HashMap;
use std::path::{Path, PathBuf};

use crate::parse::UseDecl;

#[derive(Debug, Clone)]
pub struct LibConfig {
    pub libraries: HashMap<String, PathBuf>,
    pub root_path: PathBuf,
}

impl LibConfig {
    pub fn new(libraries: HashMap<String, PathBuf>, raw_root_path: &Path) -> Self {
        let root_path = raw_root_path.with_extension("");

        Self {
            libraries,
            root_path,
        }
    }

    pub fn get_full_path(&self, use_decl: &UseDecl) -> Result<PathBuf, String> {
        let parts: Vec<&str> = use_decl.path().iter().map(|s| s.as_ref()).collect();
        let first_segment = parts[0];

        if let Some(lib_root) = self.libraries.get(first_segment) {
            let mut full_path = lib_root.clone();
            full_path.extend(&parts[1..]);

            return Ok(full_path);
        }

        Err(format!(
            "Unknown dependency '{}'. Did you forget to pass --dep {}=...?",
            first_segment, first_segment,
        ))
    }
}
