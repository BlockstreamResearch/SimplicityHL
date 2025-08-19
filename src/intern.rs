//! String interning for performance optimization.
//! 
//! Commonly used identifiers and type names are interned to reduce memory usage
//! and improve comparison performance for large programs.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};

/// Global string interner for commonly used strings.
static STRING_INTERNER: OnceLock<Mutex<StringInterner>> = OnceLock::new();

/// String interner that deduplicates commonly used strings.
#[derive(Default)]
struct StringInterner {
    strings: HashMap<String, Arc<str>>,
    stats: InternerStats,
}

/// Statistics for the string interner.
#[derive(Default, Debug)]
struct InternerStats {
    total_requests: usize,
    cache_hits: usize,
    memory_saved: usize,
}

impl StringInterner {
    /// Intern a string, returning a shared reference.
    fn intern(&mut self, s: &str) -> Arc<str> {
        self.stats.total_requests += 1;
        
        if let Some(existing) = self.strings.get(s) {
            self.stats.cache_hits += 1;
            self.stats.memory_saved += s.len();
            Arc::clone(existing)
        } else {
            let arc_str: Arc<str> = Arc::from(s);
            self.strings.insert(s.to_string(), Arc::clone(&arc_str));
            arc_str
        }
    }
    
    /// Get interning statistics.
    fn stats(&self) -> &InternerStats {
        &self.stats
    }
}

/// Intern a string for better memory usage.
/// 
/// This is particularly useful for commonly used identifiers and type names.
pub fn intern_string(s: &str) -> Arc<str> {
    let interner = STRING_INTERNER.get_or_init(|| Mutex::new(StringInterner::default()));
    interner.lock().unwrap().intern(s)
}

/// Get string interning statistics.
/// 
/// Useful for performance analysis and debugging.
pub fn interning_stats() -> String {
    let interner = STRING_INTERNER.get_or_init(|| Mutex::new(StringInterner::default()));
    let stats = interner.lock().unwrap().stats();
    format!(
        "String Interning Stats: {} requests, {} hits ({:.1}% hit rate), {} bytes saved",
        stats.total_requests,
        stats.cache_hits,
        if stats.total_requests > 0 { 
            100.0 * stats.cache_hits as f64 / stats.total_requests as f64 
        } else { 
            0.0 
        },
        stats.memory_saved
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_string_interning() {
        let s1 = intern_string("test");
        let s2 = intern_string("test");
        
        // Should be the same Arc
        assert!(Arc::ptr_eq(&s1, &s2));
        assert_eq!(s1.as_ref(), "test");
    }

    #[test]
    fn test_interning_stats() {
        intern_string("unique_test_string");
        intern_string("unique_test_string");
        
        let stats = interning_stats();
        assert!(stats.contains("hit rate"));
    }
}
