//! Unstable feature management for SimplicityHL compiler.

use std::collections::HashSet;
use std::fmt;
use std::str::FromStr;

use crate::error::{Error, ErrorCollector, RichError, Span};
use crate::source::SourceFile;

/// Keeps track of unstable features available in the compiler.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum UnstableFeature {
    /// Import and module syntax, including `use`, `crate::`, and import aliases.
    Imports,
}

impl fmt::Display for UnstableFeature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Imports => write!(f, "imports"),
        }
    }
}

impl FromStr for UnstableFeature {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "imports" => Ok(UnstableFeature::Imports),
            _ => Err(format!("Unknown unstable feature: '{}'", s)),
        }
    }
}

impl UnstableFeature {
    pub fn description(&self) -> &'static str {
        match self {
            Self::Imports => "Import syntax: 'use', 'crate::', and import aliases",
        }
    }

    pub fn all() -> &'static [UnstableFeature] {
        &[Self::Imports]
    }

    pub fn help_message() -> String {
        let max_len = Self::all()
            .iter()
            .map(|feature| feature.to_string().len())
            .max()
            .unwrap_or(0);

        let mut help = String::from("Enable unstable features. Available features:\n");
        for feature in Self::all() {
            help.push_str(&format!(
                "  {name:<width$} {desc}\n",
                name = feature.to_string(),
                width = max_len + 2,
                desc = feature.description()
            ));
        }
        help
    }
}

/// An unstable feature required by a parsed syntax node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct FeatureUse {
    feature: UnstableFeature,
    span: Span,
}

impl FeatureUse {
    pub(crate) fn new(feature: UnstableFeature, span: Span) -> Self {
        Self { feature, span }
    }
}

/// Implemented by parsed syntax nodes that can require unstable compiler features.
pub(crate) trait UnstableFeatureRequirements {
    fn unstable_feature_uses(&self, out: &mut Vec<FeatureUse>);
}

/// The unstable features enabled for this compiler invocation.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct UnstableFeatures {
    enabled_features: HashSet<UnstableFeature>,
}

impl UnstableFeatures {
    /// Creates a feature set with all unstable features disabled.
    pub fn none() -> Self {
        Self::default()
    }

    /// Creates a feature set with all known unstable features enabled.
    pub fn all() -> Self {
        Self::new(UnstableFeature::all().iter().copied())
    }

    /// Creates a feature set with specific unstable features enabled.
    pub fn new(features: impl IntoIterator<Item = UnstableFeature>) -> Self {
        Self {
            enabled_features: features.into_iter().collect(),
        }
    }

    fn is_enabled(&self, feature: UnstableFeature) -> bool {
        self.enabled_features.contains(&feature)
    }

    fn disabled_feature_error(&self, feature: UnstableFeature) -> Option<Error> {
        (!self.is_enabled(feature)).then(|| Error::UnstableFeature {
            feature_name: feature.to_string(),
        })
    }

    pub(crate) fn check_program(
        &self,
        program: &(impl UnstableFeatureRequirements + ?Sized),
        source: impl Into<SourceFile> + Clone,
        handler: &mut ErrorCollector,
    ) {
        let mut feature_uses = Vec::new();
        program.unstable_feature_uses(&mut feature_uses);

        for feature_use in feature_uses {
            if let Some(error) = self.disabled_feature_error(feature_use.feature) {
                handler.push(RichError::new(error, feature_use.span).with_source(source.clone()));
            }
        }
    }

    pub fn from_names(names: impl IntoIterator<Item = impl AsRef<str>>) -> Result<Self, String> {
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
    use std::sync::Arc;

    use crate::source::SourceFile;

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
    fn test_no_features_enabled_by_default() {
        let features = UnstableFeatures::none();
        for feature in UnstableFeature::all() {
            assert!(!features.is_enabled(*feature));
        }
    }

    #[test]
    fn test_new_single() {
        let Some(&feature) = UnstableFeature::all().first() else {
            return;
        };
        let features = UnstableFeatures::new([feature]);
        assert!(features.is_enabled(feature));
    }

    #[test]
    fn test_all_features_enabled() {
        let features = UnstableFeatures::all();
        for feature in UnstableFeature::all() {
            assert!(features.is_enabled(*feature));
        }
    }

    #[test]
    fn test_check_program_disabled() {
        struct RequiresImports;

        impl UnstableFeatureRequirements for RequiresImports {
            fn unstable_feature_uses(&self, out: &mut Vec<FeatureUse>) {
                out.push(FeatureUse::new(UnstableFeature::Imports, Span::new(0, 3)));
            }
        }

        let mut handler = ErrorCollector::new();
        UnstableFeatures::none().check_program(
            &RequiresImports,
            SourceFile::anonymous(Arc::from("use")),
            &mut handler,
        );

        let error = handler.to_string();
        assert!(error.contains("imports"));
        assert!(error.contains("not enabled"));
        assert!(error.contains("-Z"));
    }

    #[test]
    fn test_from_names_single() {
        let Some(&feature) = UnstableFeature::all().first() else {
            return;
        };
        let features = UnstableFeatures::from_names(vec![feature.to_string()]).unwrap();
        assert!(features.is_enabled(feature));
    }

    #[test]
    fn test_from_names_multiple() {
        let names: Vec<_> = UnstableFeature::all()
            .iter()
            .map(|f| f.to_string())
            .collect();
        let features = UnstableFeatures::from_names(names).unwrap();
        for feature in UnstableFeature::all() {
            assert!(features.is_enabled(*feature));
        }
    }

    #[test]
    fn test_from_names_empty() {
        let features = UnstableFeatures::from_names(Vec::<&str>::new()).unwrap();
        for feature in UnstableFeature::all() {
            assert!(!features.is_enabled(*feature));
        }
    }

    #[test]
    fn test_from_names_with_whitespace() {
        let Some(&feature) = UnstableFeature::all().first() else {
            return;
        };
        let features = UnstableFeatures::from_names(vec![format!("  {}  ", feature)]).unwrap();
        assert!(features.is_enabled(feature));
    }

    #[test]
    fn test_from_names_unknown() {
        let result = UnstableFeatures::from_names(vec!["unknown-feature"]);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Unknown"));
    }
}
