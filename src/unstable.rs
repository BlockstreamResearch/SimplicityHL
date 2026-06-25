use std::fmt;
use std::fmt::Write;
use std::str::FromStr;

use crate::error::{Error, ErrorCollector, RichError, Span};
use crate::source::SourceFile;

#[allow(rustdoc::private_intra_doc_links)]
/// The set of unstable compiler features, enabled per-feature with
/// `simc -Z <name>`.
///
/// # Adding a new feature
///
/// 1. Add a variant to this enum.
/// 2. The compiler will then flag missing arms in `fmt::Display` and
///    [`Self::description`]; fix each one.
/// 3. Two hand updates remain the compiler is quiet:
///    - extend the slice in [`Self::ALL`];
///    - add a parse arm to `FromStr`.
/// 4. Gate the syntax itself by pushing a [`FeatureRequirement`] from the
///    relevant AST node's [`RequireFeature`] impl.
///
/// # Stabilizing a feature
///
/// Delete the variant. The compiler will then flag every arm in
/// `fmt::Display`, `FromStr`, [`Self::description`], every entry in
/// [`Self::ALL`], and every [`FeatureRequirement::new`] call that
/// referenced the variant; follow the errors to clean up.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnstableFeature {
    /// Import-system syntax: `use` imports, `mod` modules, `as` import
    /// aliases, and `crate::` paths. Enable with `simc -Z imports`.
    Imports,
}

impl UnstableFeature {
    #[allow(rustdoc::private_intra_doc_links)]
    /// Every defined feature, used by [`Self::help_message`] for `--help`
    /// rendering and by [`UnstableFeatures::all`] for "enable everything"
    /// in tests.
    ///
    /// # Third step when adding a feature
    ///
    /// Append the new variant here, bump the count in
    /// `all_contains_every_variant` ( in the `tests` module below), then
    /// gate the syntax via [`RequireFeature`].
    pub const ALL: &'static [Self] = &[Self::Imports];

    /// Human-readable description shown next to the feature's name under
    /// `simc --help`.
    pub fn description(&self) -> &'static str {
        match self {
            Self::Imports => {
                "Module system syntax: 'use' imports, 'mod' modules, 'as' aliases, 'crate::' paths"
            }
        }
    }

    /// Renders the multi-line block that appears under `-Z,
    /// --unstable-feature <FEATURE>` in `simc --help`.
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

/// The set of unstable features that the user has enabled on the command line.
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

        // `Vec::dedup` removes only consecutive duplicates, so we sort first.
        enabled_features.sort_unstable();
        enabled_features.dedup();

        Self { enabled_features }
    }

    fn is_enabled(&self, feature: UnstableFeature) -> bool {
        self.enabled_features.contains(&feature) // linear scan; n is always tiny
    }

    /// Walk a program and push one [`RichError`] per use of a feature
    /// that this set does not enable.
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
}

/// One recorded use of gated syntax: a feature name and the source span
/// where it appeared. AST nodes only *record* requirements via
/// [`RequireFeature::feature_requirements`]; deciding whether to emit an
/// error happens later in [`UnstableFeatures::check_program`].
pub(crate) struct FeatureRequirement {
    feature: UnstableFeature,
    span: Span,
}

impl FeatureRequirement {
    pub(crate) fn new(feature: UnstableFeature, span: Span) -> Self {
        Self { feature, span }
    }
}

/// Implemented by parsed syntax nodes that can require unstable compiler
/// features.
///
/// Each node pushes every feature-gated construct it owns (and
/// recursively its children's) into `out`. The caller then checks those
/// uses against the enabled feature set via
/// [`UnstableFeatures::check_program`].
///
/// Implementations must be exhaustive so that new syntax cannot silently
/// bypass the check: enum impls match on `self` without a wildcard arm
/// (adding a variant is a compile error until its arm is written), and
/// struct impls destructure every field (adding a field is a compile
/// error until the pattern is updated). Prefer [`impl_require_feature`]
/// for the boilerplate.
///
/// # Fourth step when adding a feature
///
/// Identify where the new syntax lives:
///
/// - **New AST node** (a new `Item`, expression, statement…): write its
///   `RequireFeature` impl. Push
///   `FeatureRequirement::new(YourFeature, span)`, then recurse into
///   children. The parent enum's exhaustive `match self` will fail to
///   compile until you add a delegate arm there too.
/// - **New syntax inside an existing node**: extend that node's existing
///   impl. For types specifically, the new `AliasedType` / `TypeInner`
///   variant in `src/types.rs` will refuse to compile until classified.
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

/// The canonical CLI name of a feature, used both by `simc -Z <name>` and
/// by error messages.
impl fmt::Display for UnstableFeature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Imports => write!(f, "imports"),
        }
    }
}

/// Parses the name written after `simc -Z` into an [`UnstableFeature`].
/// Arms must agree with `fmt::Display`
impl FromStr for UnstableFeature {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "imports" => Ok(UnstableFeature::Imports),
            _ => Err(format!("Unknown unstable feature: '{s}'")),
        }
    }
}

/// Generate a [`RequireFeature`] impl by listing the fields or variant
/// payloads to recurse into, and (optionally, for the struct arm) a
/// feature this whole node requires.
///
/// # Examples
///
/// ```ignore
/// // Enum: list every variant. Each tuple slot is either an identifier
/// // to recurse into, or `_` to skip.
/// impl_require_feature! {
///     Item {
///         variants:
///             Use(use_decl),
///             Module(module),
///             Function(function),
///             Ignored,
///     }
/// }
///
/// // Struct: just recurse into the fields that can carry gated syntax.
/// impl_require_feature! {
///     Module {
///         recurse: items;
///     }
/// }
///
/// // Struct that itself gates a feature. `span: <field>` names the
/// // struct field that holds the source span attached to the
/// // requirement.
/// impl_require_feature! {
///     UseDecl {
///         requires: UnstableFeature::Imports, span: span;
///         recurse: items;
///     }
/// }
/// ```
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;
    use std::sync::Arc;

    use crate::source::SourceFile;

    // Just dev sanity check
    #[test]
    fn all_contains_every_variant() {
        let all_features = UnstableFeature::ALL;

        // When you add a variant to `UnstableFeature`, bump this count and add
        // the variant to `ALL`. Pins that `ALL` stays complete.
        assert_eq!(
            all_features.len(),
            1,
            "update this count when adding a feature"
        );

        let mut unique = HashSet::new();
        for feature in all_features {
            assert!(unique.insert(*feature), "Features in ALL should be unique");
        }
    }

    /// A synthetic node that requires exactly one feature, for testing the
    /// check mechanism independently of any concrete syntax.
    struct Requires(UnstableFeature);

    impl RequireFeature for Requires {
        fn feature_requirements(&self, out: &mut Vec<FeatureRequirement>) {
            out.push(FeatureRequirement::new(
                self.0,
                Span::new_in_default_file(0..3),
            ));
        }
    }

    /// A node requiring a feature is rejected  when no features are enabled,
    /// and the error names the feature and poitns at the `-Z` flag.
    #[test]
    fn test_check_program_rejects_a_disabled_feature() {
        // `check_program` does not branch on the variant; one feature
        // witnesses the property for all of them. So, we can check only one instead of each.
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
