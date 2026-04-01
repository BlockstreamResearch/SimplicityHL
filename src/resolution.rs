use std::path::Path;
use std::sync::Arc;

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
