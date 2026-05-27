pub mod core;
pub mod elements;

use crate::num::NonZeroPow2Usize;
use crate::types::*;

use simplicity::jet::DynJet;
use simplicity::jet::Jet;

pub trait JetHL: DynJet + Jet + std::fmt::Debug + Send + Sync + 'static {
    fn source_type(&self) -> Vec<AliasedType>;
    fn target_type(&self) -> AliasedType;
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
