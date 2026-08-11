use core::fmt;
use std::sync::Arc;

/// The name of a witness.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct TemplateProgramWitness(Arc<str>);

impl TemplateProgramWitness {
    /// Create a [`TemplateProgramWitness`] from a bare string.
    pub fn from_str_unchecked(s: &str) -> Self {
        Self(Arc::from(s))
    }

    /// Access the inner string.
    pub fn as_inner(&self) -> &Arc<str> {
        &self.0
    }

    /// Access the inner string.
    pub fn as_str(&self) -> &str {
        self.as_inner().as_ref()
    }

    /// Make a cheap copy of the name.
    pub fn shallow_clone(&self) -> Self {
        self.clone()
    }

    /// Creates a [`TemplateProgramWitness`] from an identifier.
    pub fn from_ident(ident: &crate::str::Identifier) -> Self {
        Self(Arc::clone(ident.as_inner()))
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

impl fmt::Debug for TemplateProgramWitness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_inner().fmt(f)
    }
}

impl AsRef<str> for TemplateProgramWitness {
    fn as_ref(&self) -> &str {
        self.as_inner().as_ref()
    }
}
