use core::fmt;
use std::sync::Arc;

/// A witness node in a templated Simplicity program.
///
/// Such a node may represent:
///
/// * An actual witness, identified by its name in the source code, which will be preserved
///   as a witness node when instantiating.
/// * A program parameter, identified by name in the source code, which will be replaced by
///   code to compute the parameter's value when instantiating.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct TemplateProgramWitness {
    inner: TemplateProgramWitnessInner,
}

impl TemplateProgramWitness {
    /// Create a witness-name [`TemplateProgramWitness`] from a bare string.
    ///
    /// The string is **not** checked to determine whether it collides with a
    /// language keyword, contains valid characters, or is otherwise valid.
    pub fn witness_from_str<S: Into<Arc<str>>>(s: S) -> Self {
        Self {
            inner: TemplateProgramWitnessInner::Witness(s.into()),
        }
    }

    /// Create a parameter [`TemplateProgramWitness`] from a bare string.
    ///
    /// The string is **not** checked to determine whether it collides with a
    /// language keyword, contains valid characters, or is otherwise valid.
    pub fn parameter_from_str<S: Into<Arc<str>>>(s: S) -> Self {
        Self {
            inner: TemplateProgramWitnessInner::Parameter(s.into()),
        }
    }

    /// Creates a witness-name [`TemplateProgramWitness`] from an identifier.
    pub fn witness_from_ident(ident: &crate::str::Identifier) -> Self {
        Self {
            inner: TemplateProgramWitnessInner::Witness(Arc::clone(ident.as_inner())),
        }
    }

    /// Creates a parameter [`TemplateProgramWitness`] from an identifier.
    pub fn parameter_from_ident(ident: &crate::str::Identifier) -> Self {
        Self {
            inner: TemplateProgramWitnessInner::Parameter(Arc::clone(ident.as_inner())),
        }
    }

    /// Access the inner string.
    pub fn as_inner(&self) -> &Arc<str> {
        use TemplateProgramWitnessInner as Inn;
        match self.inner {
            Inn::Witness(ref arc) => arc,
            Inn::Parameter(ref arc) => arc,
        }
    }

    /// Access the inner string.
    pub fn as_str(&self) -> &str {
        self.as_inner().as_ref()
    }

    /// Make a cheap copy of the name.
    pub fn shallow_clone(&self) -> Self {
        self.clone()
    }
}

impl core::cmp::PartialEq<str> for TemplateProgramWitness {
    fn eq(&self, other: &str) -> bool {
        self.as_ref() == other
    }
}

impl core::cmp::PartialEq<TemplateProgramWitness> for str {
    fn eq(&self, other: &TemplateProgramWitness) -> bool {
        self == other.as_ref()
    }
}

impl fmt::Display for TemplateProgramWitness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_inner().fmt(f)
    }
}

impl AsRef<str> for TemplateProgramWitness {
    fn as_ref(&self) -> &str {
        self.as_inner().as_ref()
    }
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
enum TemplateProgramWitnessInner {
    /// An actual witness value.
    Witness(Arc<str>),
    /// A program paramater.
    Parameter(Arc<str>),
}

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for TemplateProgramWitness {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        let len = u.int_in_range(1..=10)?;
        let mut string = String::with_capacity(len);
        for _ in 0..len {
            let offset = u.int_in_range(0..=25)?;
            string.push((b'a' + offset) as char)
        }
        if crate::lexer::is_keyword(string.as_str()) {
            string.push('_');
        }
        if bool::arbitrary(u)? {
            Ok(Self::witness_from_str(string.as_str()))
        } else {
            Ok(Self::parameter_from_str(string.as_str()))
        }
    }
}
