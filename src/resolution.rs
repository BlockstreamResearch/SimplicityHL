use std::path::Path;
use std::sync::Arc;

/// Powers error reporting by mapping compiler diagnostics to the specific file.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct SourceFile {
    /// The name or path of the source file (e.g., "./simf/main.simf").
    name: Arc<Path>,
    /// The actual text content of the source file.
    content: Arc<str>,
}

impl From<(&Path, &str)> for SourceFile {
    fn from((name, content): (&Path, &str)) -> Self {
        Self {
            name: Arc::from(name),
            content: Arc::from(content),
        }
    }
}

impl SourceFile {
    pub fn new(name: &Path, content: Arc<str>) -> Self {
        Self {
            name: Arc::from(name),
            content,
        }
    }

    pub fn name(&self) -> &Path {
        self.name.as_ref()
    }

    pub fn content(&self) -> Arc<str> {
        self.content.clone()
    }
}
