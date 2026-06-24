use std::fmt;
use std::fmt::Write;
use std::str::FromStr;

use crate::error::{Error, ErrorCollector, RichError, Span};
use crate::source::SourceFile;

/// <how to do that>
///
/// Them go to the [`UnstableFeatures`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnstableFeature {
    /// Imports are represented via `use`, `as`, `mod`, and `crate::` syntax.
    /// Code that contains those keywords is unstable. Use `simc -Z imports <atgs>` to compile
    /// code with mentioned symbols.
    Imports,
}

impl fmt::Display for UnstableFeature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Imports => write!(f, "imports"),
        }
    }
}

/// Used in CLI to parse a list of unstable features.
impl FromStr for UnstableFeature {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "imports" => Ok(UnstableFeature::Imports),
            _ => Err(format!("Unknown unstable feature: '{s}'")),
        }
    }
}

impl UnstableFeature {
    pub const ALL: &'static [Self] = &[Self::Imports];

    /// Used in the CLI to explain an unstable feature for the user.
    pub fn description(&self) -> &'static str {
        // DEV: when adding below, do not forget to add to the ALL constant
        match self {
            Self::Imports => {
                "Module system syntax: 'use' imports, 'mod' modules, 'as' aliases, 'crate::' paths"
            }
        }
    }

    pub fn help_message() -> String {
        let max_len = Self::ALL
            .iter()
            .map(|feature| feature.to_string().len())
            .max()
            .unwrap_or(0);

        let mut out = String::from("Enable unstable features. Available features:");

        for feature in Self::ALL {
            let _ = write!(
                out,
                "\n  {name:<width$}  {desc}",
                name = feature.to_string(),
                width = max_len,
                desc = feature.description(),
            );
        }

        out
    }
}

pub(crate) struct FeatureRequirement {
    feature: UnstableFeature,
    span: Span,
}

impl FeatureRequirement {
    pub(crate) fn new(feature: UnstableFeature, span: Span) -> Self {
        Self { feature, span }
    }
}

/// Implemented by parsed syntax nodes that can require unstable compiler features.
///
/// Each node pushes every feature-gated construct it owns (and recursively its
/// children's) into `out`. The caller then checks those uses against the enabled
/// feature set via [`UnstableFeatures::check_program`].
///
/// Enum implementations should match on `self` without a wildcard arm so adding
/// a variant forces a decision at compile time. Struct implementations should
/// forward into fields that can contain feature-gated syntax, preferably via
/// [`impl_require_feature`].
pub(crate) trait RequireFeature {
    fn feature_requirements(&self, out: &mut Vec<FeatureRequirement>);
}

impl<T: RequireFeature + ?Sized> RequireFeature for std::sync::Arc<T> {
    fn feature_requirements(&self, out: &mut Vec<FeatureRequirement>) {
        self.as_ref().feature_requirements(out);
    }
}

impl<T: RequireFeature> RequireFeature for [T] {
    fn feature_requirements(&self, out: &mut Vec<FeatureRequirement>) {
        for item in self {
            item.feature_requirements(out);
        }
    }
}

impl<T: RequireFeature> RequireFeature for Option<T> {
    fn feature_requirements(&self, out: &mut Vec<FeatureRequirement>) {
        if let Some(inner) = self {
            inner.feature_requirements(out);
        }
    }
}

impl<L: RequireFeature, R: RequireFeature> RequireFeature for either::Either<L, R> {
    fn feature_requirements(&self, out: &mut Vec<FeatureRequirement>) {
        match self {
            either::Either::Left(inner) => inner.feature_requirements(out),
            either::Either::Right(inner) => inner.feature_requirements(out),
        }
    }
}

/// Implement [`RequireFeature`] by forwarding to selected struct fields or enum
/// variant payloads.
macro_rules! impl_require_feature {
    (@recurse $out:ident; _) => {};
    (@recurse $out:ident; $field:ident) => {
        $crate::unstable::RequireFeature::feature_requirements($field, $out);
    };
    (
        $ty:ty {
            variants:
                $($variant:ident $(($($field:tt),* $(,)?))?),* $(,)?
        }
    ) => {
        impl $crate::unstable::RequireFeature for $ty {
            fn feature_requirements(
                &self,
                out: &mut Vec<$crate::unstable::FeatureRequirement>,
            ) {
                let _ = out;

                match self {
                    $(
                        Self::$variant $(($($field),*))? => {
                            $($(impl_require_feature!(@recurse out; $field);)*)?
                        },
                    )*
                }
            }
        }
    };
    (
        $ty:ty {
            $(requires: $feature:expr, span: $span:ident;)?
            recurse: $($recurse:tt),* $(,)?;
        }
    ) => {
        impl $crate::unstable::RequireFeature for $ty {
            fn feature_requirements(
                &self,
                out: &mut Vec<$crate::unstable::FeatureRequirement>,
            ) {
                let _ = out;

                $(
                    out.push($crate::unstable::FeatureRequirement::new(
                        $feature,
                        self.$span,
                    ));
                )?
                $(
                    $crate::unstable::RequireFeature::feature_requirements(
                        &self.$recurse,
                        out,
                    );
                )*
            }
        }
    };
}
pub(crate) use impl_require_feature;

/// <Rust doc needed>
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnstableFeatures {
    enabled_features: Vec<UnstableFeature>,
}

impl UnstableFeatures {
    pub fn none() -> Self {
        Self {
            enabled_features: Vec::new(),
        }
    }

    pub fn all() -> Self {
        Self::new(UnstableFeature::ALL.iter().copied())
    }

    pub fn new(features: impl IntoIterator<Item = UnstableFeature>) -> Self {
        let mut enabled_features: Vec<_> = features.into_iter().collect();
        enabled_features.sort_unstable();
        enabled_features.dedup();
        Self { enabled_features }
    }

    fn is_enabled(&self, feature: UnstableFeature) -> bool {
        self.enabled_features.contains(&feature)
    }

    pub(crate) fn check_program(
        &self,
        program: &impl RequireFeature,
        source: &SourceFile,
        handler: &mut ErrorCollector,
    ) {
        let mut uses = Vec::new();
        program.feature_requirements(&mut uses);
        for FeatureRequirement { feature, span } in uses {
            if self.is_enabled(feature) {
                continue;
            }
            let error = Error::UnstableFeature { feature };
            handler.push(RichError::new(error, span).with_source(source.clone()));
        }
    }

    pub(crate) fn validate_parse<T: RequireFeature>(
        &self,
        parsed: Option<T>,
        source: impl Into<SourceFile>,
        handler: &mut ErrorCollector,
    ) -> Option<T> {
        let parsed = parsed?;
        let source = source.into();
        self.check_program(&parsed, &source, handler);
        (!handler.has_errors()).then_some(parsed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;
    use std::sync::Arc;

    use crate::source::SourceFile;

    // Just dev sanity checks
    #[test]
    fn all_contains_every_variant() {
        let all_features = UnstableFeature::ALL;

        // When you add a variant to `UnstableFeature`, bump this count and add
        // the variant to `all()`. Pins that `all()` stays complete.
        assert_eq!(all_features.len(), 1);

        let mut unique = HashSet::new();
        for feature in all_features {
            assert!(
                unique.insert(*feature),
                "Features in all() should be unique"
            );
        }
    }

    /// A synthetic node that requires exactly one feature, for testing the
    /// check mechanism independently of any concrete syntax.
    struct Requires(UnstableFeature);

    impl RequireFeature for Requires {
        fn feature_requirements(&self, out: &mut Vec<FeatureRequirement>) {
            out.push(FeatureRequirement::new(self.0, Span::new(0, 3)));
        }
    }

    #[test]
    fn test_check_program_rejects_each_disabled_feature() {
        // A node requiring a feature is rejected when no features are enabled,
        // and the error names the feature and points at the `-Z` flag.
        let Some(&feature) = UnstableFeature::ALL.first() else {
            return;
        };

        let mut handler = ErrorCollector::new();
        let source = SourceFile::anonymous(Arc::from("x"));

        UnstableFeatures::none().check_program(&Requires(feature), &source, &mut handler);

        let error = handler.to_string();
        assert!(
            error.contains(&feature.to_string()),
            "error should name the feature `{feature}`: {error}"
        );
        assert!(error.contains("not enabled"), "{error}");
        assert!(error.contains("-Z"), "{error}");
    }

    #[test]
    fn test_check_program_accepts_each_enabled_feature() {
        let Some(&feature) = UnstableFeature::ALL.first() else {
            return;
        };

        let mut handler = ErrorCollector::new();
        let source = SourceFile::anonymous(Arc::from("x"));
        UnstableFeatures::new([feature]).check_program(&Requires(feature), &source, &mut handler);

        assert!(
            !handler.has_errors(),
            "enabling `{feature}` should accept a node that requires it: {}",
            handler
        );
    }
}
