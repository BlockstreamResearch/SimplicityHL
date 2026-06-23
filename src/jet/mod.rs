pub mod core;
#[cfg(feature = "external-jets")]
mod dynlib;
pub mod elements;
#[cfg(feature = "external-jets")]
pub mod external;

use crate::num::NonZeroPow2Usize;
use crate::num::Pow2Usize;
use crate::types::*;

use simplicity::jet::DynJet;
use simplicity::jet::Jet;

pub trait JetHL: DynJet + Jet + std::fmt::Debug + Send + Sync + 'static {
    fn source_jet_classification(&self) -> SourceJetClassification;
    fn target_jet_classification(&self) -> TargetJetClassification;
    fn is_disabled(&self) -> bool;
    fn clone_box(&self) -> Box<dyn JetHL>;
    fn as_jet(&self) -> &dyn Jet;
}

impl Clone for Box<dyn JetHL> {
    fn clone(&self) -> Self {
        (**self).clone_box()
    }
}

impl PartialEq for Box<dyn JetHL> {
    fn eq(&self, other: &Self) -> bool {
        (**self).dyn_eq(other.as_jet())
    }
}

impl Eq for Box<dyn JetHL> {}

impl std::hash::Hash for Box<dyn JetHL> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (**self).dyn_hash(state)
    }
}

/// Describes the arity and layout of a jet's source type in SimplicityHL.
///
/// For the standard cases, the input type is assumed to be a
/// balanced binary product of equal-width integer components, and the compiler derives
/// each component's [`UIntType`] automatically from the total source bit-width divided
/// by the divisor.
///
/// Use `Custom` when the argument layout does not follow this regular structure.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SourceJetClassification {
    /// Jet takes a single argument
    Unary,
    /// Jet takes two arguments of equal width.
    Binary,
    /// Jet takes three arguments of equal width.
    Ternary,
    /// Jet takes four arguments of equal width.
    Quaternary,
    /// Jet takes an arbitrary list of explicitly typed arguments.
    ///
    /// Use this when the source type cannot be described as a uniform split,
    /// e.g. when argument types differ or are not simple integers.
    Custom(Vec<AliasedType>),
}

impl SourceJetClassification {
    /// Returns the number of individual arguments the jet expects.
    ///
    /// For `Custom`, this is the length of the explicit type list.
    pub fn divisor(&self) -> usize {
        match self {
            SourceJetClassification::Unary => 1,
            SourceJetClassification::Binary => 2,
            SourceJetClassification::Ternary => 3,
            SourceJetClassification::Quaternary => 4,
            SourceJetClassification::Custom(types) => types.len(),
        }
    }
}

/// Describes the layout of a jet's **output** (target) type in SimplicityHL.
///
/// For the common case where the output is a single integer value whose width is
/// a power of two, use `Unary` and let the compiler derive the [`UIntType`] from
/// the target bit-width automatically.
///
/// Use `Custom` for any output type that cannot be represented as a plain integer.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TargetJetClassification {
    /// Jet returns a single integer value; the concrete [`UIntType`] is derived
    /// automatically from the Simplicity target bit-width.
    Unary,
    /// Jet returns an explicitly specified type.
    ///
    /// Use this when the output is not a simple integer.
    Custom(AliasedType),
}

pub fn tuple<A: Into<AliasedType>, I: IntoIterator<Item = A>>(elements: I) -> AliasedType {
    AliasedType::tuple(elements.into_iter().map(A::into))
}

pub fn array<A: Into<AliasedType>>(element: A, size: usize) -> AliasedType {
    AliasedType::array(element.into(), size)
}

pub fn list<A: Into<AliasedType>>(element: A, bound: usize) -> AliasedType {
    AliasedType::list(element.into(), NonZeroPow2Usize::new(bound).unwrap())
}

pub fn bool() -> AliasedType {
    AliasedType::boolean()
}

pub fn either<A: Into<AliasedType>, B: Into<AliasedType>>(left: A, right: B) -> AliasedType {
    AliasedType::either(left.into(), right.into())
}

pub fn option<A: Into<AliasedType>>(inner: A) -> AliasedType {
    AliasedType::option(inner.into())
}

pub fn source_type(jet: &dyn JetHL) -> Vec<AliasedType> {
    let source_class = jet.source_jet_classification();
    if let SourceJetClassification::Custom(custom_type) = source_class {
        return custom_type;
    }

    let divisor = source_class.divisor();
    let component_bit_width = jet.source_ty().to_bit_width() / divisor;
    if component_bit_width == 0 {
        return Vec::new();
    }

    let pow_of_2 = Pow2Usize::new(component_bit_width)
        .expect("the width of the source type should be power of 2");
    let num_type =
        UIntType::from_bit_width(pow_of_2).expect("the source type should be one of defined");

    vec![AliasedType::from(num_type); divisor]
}

pub fn target_type(jet: &dyn JetHL) -> AliasedType {
    if let TargetJetClassification::Custom(custom_type) = jet.target_jet_classification() {
        return custom_type;
    }

    let bit_width = jet.target_ty().to_bit_width();
    if bit_width == 0 {
        return AliasedType::unit();
    }

    let pow_of_2 = Pow2Usize::new(bit_width).expect("should be fine");
    let num_type = UIntType::from_bit_width(pow_of_2).expect("should exist");
    AliasedType::from(num_type)
}

#[cfg(test)]
mod tests {
    use super::*;
    use simplicity::jet::{Elements, Jet};

    #[test]
    fn compatible_source_type() {
        for jet in Elements::ALL {
            let resolved_ty = ResolvedType::tuple(
                source_type(&jet)
                    .into_iter()
                    .map(|t| t.resolve_builtin().unwrap()),
            );
            let structural_ty = StructuralType::from(&resolved_ty);
            let simplicity_ty = jet.source_ty().to_final();

            println!("{jet}");
            assert_eq!(structural_ty.as_ref(), simplicity_ty.as_ref());
        }
    }

    #[test]
    fn compatible_target_type() {
        for jet in Elements::ALL {
            let resolved_ty = target_type(&jet).resolve_builtin().unwrap();
            let structural_ty = StructuralType::from(&resolved_ty);
            let simplicity_ty = jet.target_ty().to_final();

            println!("{jet}");
            assert_eq!(structural_ty.as_ref(), simplicity_ty.as_ref());
        }
    }
}
