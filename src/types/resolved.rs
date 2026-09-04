use core::fmt;
use std::sync::Arc;

use miniscript::iter::{Tree, TreeLike};

use super::{
    EnumInfo, StructuralType, TypeConstructible, TypeDeconstructible, TypeInner, UIntType,
};
use crate::num::NonZeroPow2Usize;

/// SimplicityHL type without type aliases.
#[derive(PartialEq, Eq, Hash, Clone)]
pub struct ResolvedType(pub(super) TypeInner<Arc<Self>>);

impl ResolvedType {
    /// Access the inner type primitive.
    pub fn as_inner(&self) -> &TypeInner<Arc<Self>> {
        &self.0
    }
}

/// Nominal enum types.
///
/// These methods are inherent rather than part of [`TypeConstructible`] and [`TypeDeconstructible`].
/// Those traits model the structural type algebra that every type universe (aliased, resolved, structural)
/// shares, while a nominal enum exists only at the resolved level.
///
/// At the structural level its identity is erased into a balanced sum, and at the source level enums
/// enter types by name only.
/// Keeping the constructor off the shared traits also means that only [`crate::ast`]'s scope
/// (which owns the uniqueness of declaration ids) can mint enum types.
impl ResolvedType {
    /// Create a nominal enum type from the given definition.
    pub fn enumeration(info: EnumInfo) -> Self {
        Self(TypeInner::Enum(Arc::new(info)))
    }

    /// Access the enum definition if this is an enum type.
    pub fn as_enum(&self) -> Option<&EnumInfo> {
        match &self.0 {
            TypeInner::Enum(info) => Some(info),
            _ => None,
        }
    }

    /// Check whether the type mentions an enum, at any nesting depth.
    pub fn contains_enum(&self) -> bool {
        self.post_order_iter()
            .any(|data| data.node.as_enum().is_some())
    }

    /// Full description for the ABI: an enum expands into its variants and
    /// their payload types; every other type is unchanged from [`Display`].
    pub(crate) fn abi_description(&self) -> String {
        let Some(info) = self.as_enum() else {
            return self.to_string();
        };

        let variants = info
            .variants()
            .iter()
            .map(|v| {
                if v.payload().is_empty() {
                    v.name().to_string()
                } else {
                    let payload = v
                        .payload()
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{}({})", v.name(), payload)
                }
            })
            .collect::<Vec<_>>()
            .join(", ");
        format!("{} {{ {} }}", info.name(), variants)
    }
}

impl TypeConstructible for ResolvedType {
    fn either(left: Self, right: Self) -> Self {
        Self(TypeInner::Either(Arc::new(left), Arc::new(right)))
    }

    fn option(inner: Self) -> Self {
        Self(TypeInner::Option(Arc::new(inner)))
    }

    fn boolean() -> Self {
        Self(TypeInner::Boolean)
    }

    fn tuple<I: IntoIterator<Item = Self>>(elements: I) -> Self {
        Self(TypeInner::Tuple(
            elements.into_iter().map(Arc::new).collect(),
        ))
    }

    fn array(element: Self, size: usize) -> Self {
        Self(TypeInner::Array(Arc::new(element), size))
    }

    fn list(element: Self, bound: NonZeroPow2Usize) -> Self {
        Self(TypeInner::List(Arc::new(element), bound))
    }
}

impl TypeDeconstructible for ResolvedType {
    fn as_either(&self) -> Option<(&Self, &Self)> {
        match self.as_inner() {
            TypeInner::Either(ty_l, ty_r) => Some((ty_l, ty_r)),
            _ => None,
        }
    }

    fn as_option(&self) -> Option<&Self> {
        match self.as_inner() {
            TypeInner::Option(ty) => Some(ty),
            _ => None,
        }
    }

    fn is_boolean(&self) -> bool {
        matches!(self.as_inner(), TypeInner::Boolean)
    }

    fn as_integer(&self) -> Option<UIntType> {
        match self.as_inner() {
            TypeInner::UInt(ty) => Some(*ty),
            _ => None,
        }
    }

    fn as_tuple(&self) -> Option<&[Arc<Self>]> {
        match self.as_inner() {
            TypeInner::Tuple(components) => Some(components),
            _ => None,
        }
    }

    fn as_array(&self) -> Option<(&Self, usize)> {
        match self.as_inner() {
            TypeInner::Array(ty, size) => Some((ty, *size)),
            _ => None,
        }
    }

    fn as_list(&self) -> Option<(&Self, NonZeroPow2Usize)> {
        match self.as_inner() {
            TypeInner::List(ty, bound) => Some((ty, *bound)),
            _ => None,
        }
    }
}

impl TreeLike for &ResolvedType {
    fn as_node(&self) -> Tree<Self> {
        match &self.0 {
            TypeInner::Boolean | TypeInner::UInt(..) | TypeInner::Enum(..) => Tree::Nullary,
            TypeInner::Option(l) | TypeInner::Array(l, _) | TypeInner::List(l, _) => Tree::Unary(l),
            TypeInner::Either(l, r) => Tree::Binary(l, r),
            TypeInner::Tuple(elements) => Tree::Nary(elements.iter().map(Arc::as_ref).collect()),
        }
    }
}

impl fmt::Debug for ResolvedType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl fmt::Display for ResolvedType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for data in self.verbose_pre_order_iter() {
            data.node.0.display(f, data.n_children_yielded)?;
        }
        Ok(())
    }
}

impl From<UIntType> for ResolvedType {
    fn from(value: UIntType) -> Self {
        Self(TypeInner::UInt(value))
    }
}

#[cfg(feature = "arbitrary")]
impl crate::ArbitraryRec for ResolvedType {
    // Deliberately never generates `TypeInner::Enum`.
    // Enum values serialize as bare strings that only resolve against a program's declarations
    // (`UnresolvedValues::resolve`), so the self-contained witness JSON round-trip target (`parse_witness_json_rtt`)
    // would fail by design.
    fn arbitrary_rec(u: &mut arbitrary::Unstructured, budget: usize) -> arbitrary::Result<Self> {
        use arbitrary::Arbitrary;

        match budget.checked_sub(1) {
            None => match u.int_in_range(0..=1)? {
                0 => Ok(Self::boolean()),
                1 => UIntType::arbitrary(u).map(Self::from),
                _ => unreachable!(),
            },
            Some(new_budget) => match u.int_in_range(0..=6)? {
                0 => Ok(Self::boolean()),
                1 => UIntType::arbitrary(u).map(Self::from),
                2 => Self::arbitrary_rec(u, new_budget).map(Self::option),
                3 => {
                    let left = Self::arbitrary_rec(u, new_budget)?;
                    let right = Self::arbitrary_rec(u, new_budget)?;
                    Ok(Self::either(left, right))
                }
                4 => {
                    let len = u.int_in_range(0..=3)?;
                    (0..len)
                        .map(|_| Self::arbitrary_rec(u, new_budget))
                        .collect::<arbitrary::Result<Vec<Self>>>()
                        .map(Self::tuple)
                }
                5 => {
                    let element = Self::arbitrary_rec(u, new_budget)?;
                    let size = u.int_in_range(0..=3)?;
                    Ok(Self::array(element, size))
                }
                6 => {
                    let element = Self::arbitrary_rec(u, new_budget)?;
                    let exp = u.int_in_range(1u32..=4)?;
                    let bound = NonZeroPow2Usize::new_unchecked(2usize.saturating_pow(exp));
                    Ok(Self::list(element, bound))
                }
                _ => unreachable!(),
            },
        }
    }
}

impl From<&ResolvedType> for StructuralType {
    fn from(value: &ResolvedType) -> Self {
        let mut output = vec![];
        for data in value.post_order_iter() {
            match &data.node.0 {
                TypeInner::Either(_, _) => {
                    let right = output.pop().unwrap();
                    let left = output.pop().unwrap();
                    output.push(StructuralType::either(left, right));
                }
                TypeInner::Option(_) => {
                    let inner = output.pop().unwrap();
                    output.push(StructuralType::option(inner));
                }
                TypeInner::Boolean => output.push(StructuralType::boolean()),
                TypeInner::UInt(integer) => output.push(StructuralType::from(*integer)),
                TypeInner::Tuple(_) => {
                    let size = data.node.n_children();
                    let elements = output.split_off(output.len() - size);
                    debug_assert_eq!(elements.len(), size);
                    output.push(StructuralType::tuple(elements));
                }
                TypeInner::Array(_, size) => {
                    let element = output.pop().unwrap();
                    output.push(StructuralType::array(element, *size));
                }
                TypeInner::List(_, bound) => {
                    let element = output.pop().unwrap();
                    output.push(StructuralType::list(element, *bound));
                }
                TypeInner::Enum(info) => {
                    output.push(StructuralType::balanced_sum(info.structural_variants()));
                }
            }
        }
        debug_assert_eq!(output.len(), 1);
        output.pop().unwrap()
    }
}

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for ResolvedType {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        <Self as crate::ArbitraryRec>::arbitrary_rec(u, 3)
    }
}
