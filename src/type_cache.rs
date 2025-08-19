//! Type equality caching for performance optimization.
//!
//! Caches the results of expensive type equality checks to avoid redundant computations
//! during compilation.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};
use crate::types::ResolvedType;

/// Global type equality cache.
static TYPE_CACHE: OnceLock<Mutex<TypeEqualityCache>> = OnceLock::new();

/// Cache for type equality checks.
#[derive(Default)]
struct TypeEqualityCache {
    cache: HashMap<(TypeKey, TypeKey), bool>,
    stats: CacheStats,
}

/// Statistics for the type cache.
#[derive(Default, Debug)]
struct CacheStats {
    total_checks: usize,
    cache_hits: usize,
}

/// A hashable key for types to enable caching.
#[derive(Hash, Eq, PartialEq, Clone)]
struct TypeKey(String);

impl From<&ResolvedType> for TypeKey {
    fn from(ty: &ResolvedType) -> Self {
        // Use display representation as key
        Self(ty.to_string())
    }
}

impl TypeEqualityCache {
    /// Check if two types are equal, using cache when possible.
    fn are_equal(&mut self, left: &ResolvedType, right: &ResolvedType) -> bool {
        self.stats.total_checks += 1;
        
        let left_key = TypeKey::from(left);
        let right_key = TypeKey::from(right);
        
        // Normalize key order for consistent caching
        let cache_key = if left_key <= right_key {
            (left_key, right_key)
        } else {
            (right_key, left_key)
        };
        
        if let Some(&result) = self.cache.get(&cache_key) {
            self.stats.cache_hits += 1;
            return result;
        }
        
        // Compute equality and cache result
        let result = left == right;
        self.cache.insert(cache_key, result);
        result
    }
    
    /// Get cache statistics.
    fn stats(&self) -> &CacheStats {
        &self.stats
    }
}

/// Check if two types are equal with caching.
/// 
/// This can significantly improve performance for programs with many type checks.
pub fn types_equal(left: &ResolvedType, right: &ResolvedType) -> bool {
    let cache = TYPE_CACHE.get_or_init(|| Mutex::new(TypeEqualityCache::default()));
    cache.lock().unwrap().are_equal(left, right)
}

/// Get type cache statistics.
/// 
/// Useful for performance analysis.
pub fn type_cache_stats() -> String {
    let cache = TYPE_CACHE.get_or_init(|| Mutex::new(TypeEqualityCache::default()));
    let stats = cache.lock().unwrap().stats();
    format!(
        "Type Cache Stats: {} checks, {} hits ({:.1}% hit rate)",
        stats.total_checks,
        stats.cache_hits,
        if stats.total_checks > 0 { 
            100.0 * stats.cache_hits as f64 / stats.total_checks as f64 
        } else { 
            0.0 
        }
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::ResolvedType;

    #[test]
    fn test_type_caching() {
        let ty1 = ResolvedType::boolean();
        let ty2 = ResolvedType::boolean();
        
        // First call should compute
        assert!(types_equal(&ty1, &ty2));
        
        // Second call should use cache
        assert!(types_equal(&ty1, &ty2));
        
        let stats = type_cache_stats();
        assert!(stats.contains("hit rate"));
    }
}
