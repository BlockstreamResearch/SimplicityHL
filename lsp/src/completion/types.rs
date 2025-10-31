/// Template for all functions
#[derive(Debug, Clone)]
pub struct FunctionTemplate {
    /// Display name shown in completion list
    pub display_name: String,
    /// Base name for snippet
    pub snippet_base: String,
    /// Generic type parameters to include and use with snippet base
    pub generics: Vec<String>,
    /// Function arguments
    pub args: Vec<String>,
    /// Return type
    pub return_type: String,
    /// Documentation
    pub description: String,
}

impl FunctionTemplate {
    /// Create a template with generics (currently used only for builtin functions)
    pub fn new(
        display_name: impl Into<String>,
        snippet_base: impl Into<String>,
        generics: Vec<String>,
        args: Vec<String>,
        return_type: impl Into<String>,
        description: impl Into<String>,
    ) -> Self {
        Self {
            display_name: display_name.into(),
            snippet_base: snippet_base.into(),
            generics,
            args,
            return_type: return_type.into(),
            description: description.into(),
        }
    }

    /// Create a template without generics
    pub fn simple(
        name: impl Into<String>,
        args: Vec<String>,
        return_type: impl Into<String>,
        description: impl Into<String>,
    ) -> Self {
        let name = name.into();
        Self::new(name.clone(), name, vec![], args, return_type, description)
    }

    /// Get snippet for function
    pub fn get_snippet_name(&self) -> String {
        format!(
            "{}::<{}>",
            self.snippet_base,
            self.generics
                .iter()
                .enumerate()
                .map(|(index, item)| { format!("${{{}:{}}}", index + 1, item) })
                .collect::<Vec<_>>()
                .join(", ")
        )
    }

    /// Get text, which would inserted when completion triggered
    pub fn get_insert_text(&self) -> String {
        format!(
            "{}({})",
            if self.generics.is_empty() {
                self.snippet_base.clone()
            } else {
                self.get_snippet_name()
            },
            self.args
                .iter()
                .enumerate()
                .map(|(index, item)| {
                    format!("${{{}:{}}}", index + 1 + self.generics.len(), item)
                })
                .collect::<Vec<_>>()
                .join(", ")
        )
    }

    /// Get signature text for function, which would show in `detail` field
    pub fn get_signature(&self) -> String {
        format!(
            "fn({}) -> {}",
            self.args.join(", "),
            if self.return_type.is_empty() {
                "()".to_string()
            } else {
                self.return_type.clone()
            }
        )
    }
}
