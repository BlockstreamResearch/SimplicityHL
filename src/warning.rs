use std::fmt;

use crate::error::{Error, RichError, Span};
use crate::str::Identifier;

/// Category of a warning, used for per-class allow/deny control.
///
/// Unlike [`WarningName`], which carries instance-specific data for display,
/// `WarnCategory` is a unit enum that identifies the *class* of warning so that
/// callers can write `template.deny_warning(WarnCategory::UnusedVariable)` without
/// needing a concrete identifier.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum WarnCategory {
    /// A variable was bound but never used.
    UnusedVariable,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum WarningName {
    UnusedVariable(Identifier),
}

impl WarningName {
    /// Return the category this warning belongs to.
    pub fn category(&self) -> WarnCategory {
        match self {
            WarningName::UnusedVariable(_) => WarnCategory::UnusedVariable,
        }
    }
}

impl fmt::Display for WarningName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WarningName::UnusedVariable(identifier) => write!(f, "unused variable: `{identifier}`. Prefix the variable name with `_` to silence this warning."),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Warning {
    /// Canonical name used for allowing and denying specific warnings.
    pub canonical_name: WarningName,
    /// Span in which this warning occured.
    pub span: Span,
}

impl Warning {
    pub(crate) fn variable_unused<S: Into<Span>>(identifier: Identifier, span: S) -> Self {
        Warning {
            canonical_name: WarningName::UnusedVariable(identifier),
            span: span.into(),
        }
    }
}

impl From<Warning> for RichError {
    fn from(value: Warning) -> Self {
        RichError::new(Error::DeniedWarning(value.canonical_name), value.span)
    }
}
