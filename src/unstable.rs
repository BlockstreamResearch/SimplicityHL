//! Unstable feature management for SimplicityHL compiler.

use std::collections::HashSet;
use std::fmt;
use std::str::FromStr;

use crate::error::{Error, ErrorCollector, RichError, Span};
use crate::parse::{Item, Program, UseItems};

/// Keeps track of unstable features available in the compiler.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum UnstableFeature {
    /// The `use` keyword for including multiple source files.
    UseKeyword,
    /// The `crate` keyword for referencing the local project root.
    CrateKeyword,
    /// The `as` keyword for aliasing imports.
    AsKeyword,
}

impl fmt::Display for UnstableFeature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UseKeyword => write!(f, "use-keyword"),
            Self::CrateKeyword => write!(f, "crate-keyword"),
            Self::AsKeyword => write!(f, "as-keyword"),
        }
    }
}

impl FromStr for UnstableFeature {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "use-keyword" => Ok(UnstableFeature::UseKeyword),
            "crate-keyword" => Ok(UnstableFeature::CrateKeyword),
            "as-keyword" => Ok(UnstableFeature::AsKeyword),
            _ => Err(format!("Unknown unstable feature: '{}'", s)),
        }
    }
}

impl UnstableFeature {
    pub fn description(&self) -> &'static str {
        match self {
            Self::UseKeyword => "The 'use' keyword for using dependencies",
            Self::CrateKeyword => "The 'crate' keyword for referencing the local project root",
            Self::AsKeyword => "The 'as' keyword for aliasing imports",
        }
    }

    pub fn all() -> &'static [UnstableFeature] {
        &[Self::UseKeyword, Self::CrateKeyword, Self::AsKeyword]
    }

    fn detect_feature_in_item(self, item: &Item) -> Vec<Span> {
        match self {
            Self::UseKeyword => Self::detect_use_keyword(item),
            Self::CrateKeyword => Self::detect_crate_keyword(item),
            Self::AsKeyword => Self::detect_as_keyword(item),
        }
    }

    fn detect_use_keyword(item: &Item) -> Vec<Span> {
        match item {
            Item::Use(use_decl) => vec![*use_decl.span()],
            _ => vec![],
        }
    }

    fn detect_crate_keyword(item: &Item) -> Vec<Span> {
        match item {
            Item::Use(use_decl)
                if use_decl
                    .drp_name()
                    .is_ok_and(|drp| drp == crate::driver::CRATE_STR) =>
            {
                vec![*use_decl.span()]
            }
            _ => vec![],
        }
    }

    fn detect_as_keyword(item: &Item) -> Vec<Span> {
        match item {
            Item::Use(use_decl) => {
                let has_alias = match use_decl.items() {
                    UseItems::Single((_, alias)) => alias.is_some(),
                    UseItems::List(items) => items.iter().any(|(_, alias)| alias.is_some()),
                };
                if has_alias {
                    vec![*use_decl.span()]
                } else {
                    vec![]
                }
            }
            _ => vec![],
        }
    }

    fn used_features(item: &Item) -> Vec<(UnstableFeature, Span)> {
        let mut features = Vec::new();
        for &feature in Self::all() {
            for span in feature.detect_feature_in_item(item) {
                features.push((feature, span));
            }
        }
        features
    }
}

// TODO: Consider the possibility to optimize this structure with traits
/// Manages the state of unstable features during compilation.
/// This struct tracks which unstable features are enabled and provides
/// validation methods for checking feature availability.
/// In default mode, all features are disabled. Features can be enabled via command-line flags
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct UnstableFeatureManager {
    enabled_features: HashSet<UnstableFeature>,
}

impl UnstableFeatureManager {
    /// Creates a manager with specific features enabled.
    pub fn new(features: impl IntoIterator<Item = UnstableFeature>) -> Self {
        Self {
            enabled_features: features.into_iter().collect(),
        }
    }

    pub fn is_enabled(&self, feature: UnstableFeature) -> bool {
        self.enabled_features.contains(&feature)
    }

    pub fn check_feature(&self, feature: UnstableFeature) -> Result<(), Error> {
        if !self.is_enabled(feature) {
            return Err(Error::UnstableFeature {
                feature_name: feature.to_string(),
            });
        }
        Ok(())
    }

    pub fn check_program(&self, program: &Program, handler: &mut ErrorCollector) {
        for item in program.items() {
            for (feature, span) in UnstableFeature::used_features(item) {
                if let Err(error) = self.check_feature(feature) {
                    handler.push(RichError::new(error, span));
                }
            }
        }
    }

    pub fn from_feature_names(
        names: impl IntoIterator<Item = impl AsRef<str>>,
    ) -> Result<Self, String> {
        let mut features = HashSet::new();

        for name in names {
            let feature_name = name.as_ref().trim();
            if !feature_name.is_empty() {
                features.insert(feature_name.parse::<UnstableFeature>()?);
            }
        }

        Ok(Self {
            enabled_features: features,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_feature_display() {
        for feature in UnstableFeature::all() {
            let name = feature.to_string();
            assert!(!name.is_empty());
            assert!(!name.contains(' '));
        }
    }

    #[test]
    fn test_feature_descriptions() {
        for feature in UnstableFeature::all() {
            assert!(!feature.description().is_empty());
        }
    }

    #[test]
    fn test_all_features() {
        let all_features = UnstableFeature::all();
        let mut unique = HashSet::new();
        for feature in all_features {
            assert!(
                unique.insert(*feature),
                "Features in all() should be unique"
            );
        }
    }

    #[test]
    fn test_feature_from_str() {
        for feature in UnstableFeature::all() {
            let parsed = feature
                .to_string()
                .parse::<UnstableFeature>()
                .expect("Should parse from string");
            assert_eq!(*feature, parsed);
        }
    }

    #[test]
    fn test_default_manager() {
        let manager = UnstableFeatureManager::default();
        for feature in UnstableFeature::all() {
            assert!(!manager.is_enabled(*feature));
        }
    }

    #[test]
    fn test_new_single() {
        let Some(&feature) = UnstableFeature::all().first() else {
            return;
        };
        let manager = UnstableFeatureManager::new([feature]);
        assert!(manager.is_enabled(feature));
    }

    #[test]
    fn test_check_feature_enabled() {
        let Some(&feature) = UnstableFeature::all().first() else {
            return;
        };
        let manager = UnstableFeatureManager::new([feature]);
        assert!(manager.check_feature(feature).is_ok());
    }

    #[test]
    fn test_check_feature_disabled() {
        let manager = UnstableFeatureManager::default();
        let Some(&feature) = UnstableFeature::all().first() else {
            return;
        };
        let error = manager.check_feature(feature).unwrap_err().to_string();
        assert!(error.contains(&feature.to_string()));
        assert!(error.contains("not enabled"));
        assert!(error.contains("-Z"));
    }

    #[test]
    fn test_from_feature_names_single() {
        let Some(&feature) = UnstableFeature::all().first() else {
            return;
        };
        let manager =
            UnstableFeatureManager::from_feature_names(vec![feature.to_string()]).unwrap();
        assert!(manager.is_enabled(feature));
    }

    #[test]
    fn test_from_feature_names_multiple() {
        let names: Vec<_> = UnstableFeature::all()
            .iter()
            .map(|f| f.to_string())
            .collect();
        let manager = UnstableFeatureManager::from_feature_names(names).unwrap();
        for feature in UnstableFeature::all() {
            assert!(manager.is_enabled(*feature));
        }
    }

    #[test]
    fn test_from_feature_names_empty() {
        let manager = UnstableFeatureManager::from_feature_names(Vec::<&str>::new()).unwrap();
        for feature in UnstableFeature::all() {
            assert!(!manager.is_enabled(*feature));
        }
    }

    #[test]
    fn test_from_feature_names_with_whitespace() {
        let Some(&feature) = UnstableFeature::all().first() else {
            return;
        };
        let manager =
            UnstableFeatureManager::from_feature_names(vec![format!("  {}  ", feature)]).unwrap();
        assert!(manager.is_enabled(feature));
    }

    #[test]
    fn test_from_feature_names_unknown() {
        let result = UnstableFeatureManager::from_feature_names(vec!["unknown-feature"]);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Unknown"));
    }
}
