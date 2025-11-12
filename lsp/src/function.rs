use simplicityhl::parse::Function;
use std::collections::HashMap;

/// Container for parsed functions and their corresponding source text.
#[derive(Debug, Clone)]
pub struct Functions {
    /// The map from function name to its parsed representation and source text.
    pub map: HashMap<String, (Function, String)>,
}

impl Functions {
    /// Creates a new, empty `Functions` structure.
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }

    /// Inserts or updates a function and its document text.
    pub fn insert(&mut self, name: String, func: Function, doc: String) {
        self.map.insert(name, (func, doc));
    }

    /// Get pair of function and documentation.
    pub fn get(&self, name: &str) -> Option<(&Function, &String)> {
        self.map.get(name).map(|(func, doc)| (func, doc))
    }

    /// Retrieves a reference to a parsed function by name.
    pub fn get_func(&self, name: &str) -> Option<&Function> {
        self.map.get(name).map(|(func, _)| func)
    }

    /// Returns a vector of all parsed functions.
    pub fn functions(&self) -> Vec<&Function> {
        self.map.values().map(|(func, _)| func).collect()
    }

    /// Returns a vector of (function name, function) pairs.
    pub fn functions_and_docs(&self) -> Vec<(&Function, &str)> {
        self.map
            .values()
            .map(|(func, doc)| (func, doc.as_str()))
            .collect()
    }
}
