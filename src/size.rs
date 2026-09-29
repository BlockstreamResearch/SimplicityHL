use core::fmt;
use std::num::NonZeroUsize;
use std::sync::Arc;

use crate::error::Error;
use crate::num::NonZeroPow2Usize;
use crate::types::{ResolvedType, UIntType};
use crate::value::{UIntValue, ValueInner};
use crate::witness::WitnessNameToValueMap;
use crate::Arguments;
use crate::TemplateProgramWitness;

pub(crate) fn make_mut_slice<T: Clone>(values: &mut Arc<[T]>) -> &mut [T] {
    if Arc::get_mut(values).is_none() {
        *values = Arc::from(values.iter().cloned().collect::<Vec<_>>());
    }
    Arc::get_mut(values).unwrap()
}

/// A size written directly as a literal or supplied as a compilation parameter.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum SizeExpression<T> {
    Literal(T),
    Parameter(TemplateProgramWitness),
}

impl<T> SizeExpression<T> {
    pub const fn literal(value: T) -> Self {
        Self::Literal(value)
    }

    pub fn parameter(name: TemplateProgramWitness) -> Self {
        Self::Parameter(name)
    }

    pub const fn as_literal(&self) -> Option<&T> {
        match self {
            Self::Literal(value) => Some(value),
            Self::Parameter(_) => None,
        }
    }

    pub const fn as_parameter(&self) -> Option<&TemplateProgramWitness> {
        match self {
            Self::Literal(_) => None,
            Self::Parameter(name) => Some(name),
        }
    }
}

impl<T: fmt::Display> fmt::Display for SizeExpression<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Literal(value) => value.fmt(f),
            Self::Parameter(name) => write!(f, "param::{name}"),
        }
    }
}

pub(crate) struct SizeResolver<'a> {
    arguments: &'a Arguments,
}

impl<'a> SizeResolver<'a> {
    pub const fn new(arguments: &'a Arguments) -> Self {
        Self { arguments }
    }

    pub fn array(&self, name: &TemplateProgramWitness) -> Result<usize, Error> {
        self.usize(name)
    }

    pub fn array_fold(&self, name: &TemplateProgramWitness) -> Result<NonZeroUsize, Error> {
        let size = self.usize(name)?;
        NonZeroUsize::new(size).ok_or(Error::ArraySizeNonZero { size })
    }

    pub fn list(&self, name: &TemplateProgramWitness) -> Result<NonZeroPow2Usize, Error> {
        let bound = self.usize(name)?;
        NonZeroPow2Usize::new(bound).ok_or(Error::ListBoundPow2 { bound })
    }

    fn usize(&self, name: &TemplateProgramWitness) -> Result<usize, Error> {
        let value = self
            .arguments
            .get(name)
            .ok_or_else(|| Error::ArgumentMissing { name: name.clone() })?;

        let ValueInner::UInt(UIntValue::U32(value)) = value.inner() else {
            return Err(Error::ArgumentTypeMismatch {
                name: name.clone(),
                declared: ResolvedType::from(UIntType::U32),
                assigned: value.ty().clone(),
            });
        };

        usize::try_from(*value).map_err(|_| Error::Internal {
            msg: format!("Size parameter `{name}` does not fit into usize"),
        })
    }
}
