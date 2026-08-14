mod aliased;
mod inner;
mod resolved;

use std::fmt;
use std::sync::Arc;

use miniscript::iter::{Tree, TreeLike};
use simplicity::types::{CompleteBound, Final};

use crate::array::{BTreeSlice, Partition};
use crate::num::NonZeroPow2Usize;

pub use self::aliased::{AliasedType, BuiltinAlias};
pub use self::inner::{EnumInfo, EnumVariantInfo, TypeInner, UIntType};
pub use self::resolved::ResolvedType;

impl TryFrom<&StructuralType> for UIntType {
    type Error = ();

    fn try_from(value: &StructuralType) -> Result<Self, Self::Error> {
        let mut current = value.as_ref();
        let mut n = 0;
        while let Some((left, right)) = current.as_product() {
            if left.tmr() != right.tmr() {
                return Err(());
            }
            current = left;
            n += 1;
        }
        if let Some((left, right)) = current.as_sum() {
            if left.is_unit() && right.is_unit() {
                return UIntType::two_n(n).ok_or(());
            }
        }
        Err(())
    }
}

macro_rules! construct_int {
    ($name: ident, $ty: ident, $text: expr) => {
        #[doc = "Create the type of"]
        #[doc = $text]
        #[doc = "integers."]
        fn $name() -> Self {
            Self::from(UIntType::$ty)
        }
    };
}

/// Various type constructors.
pub trait TypeConstructible: Sized + From<UIntType> {
    /// Create a sum of the given `left` and `right` types.
    fn either(left: Self, right: Self) -> Self;

    /// Create an option of the given `inner` type.
    fn option(inner: Self) -> Self;

    /// Create the Boolean type.
    fn boolean() -> Self;

    /// Create a tuple from the given `elements`.
    ///
    /// The empty tuple is the unit type.
    /// A tuple of two types is a product.
    fn tuple<I: IntoIterator<Item = Self>>(elements: I) -> Self;

    /// Create the unit type.
    fn unit() -> Self {
        Self::tuple([])
    }

    /// Create a product of the given `left` and `right` types.
    fn product(left: Self, right: Self) -> Self {
        Self::tuple([left, right])
    }

    /// Create an array with `size` many values of the `element` type.
    fn array(element: Self, size: usize) -> Self;

    /// Create an array of `size` many bytes.
    fn byte_array(size: usize) -> Self {
        Self::array(Self::u8(), size)
    }

    /// Create a list with less than `bound` many values of the `element` type.
    fn list(element: Self, bound: NonZeroPow2Usize) -> Self;

    construct_int!(u1, U1, "1-bit");
    construct_int!(u2, U2, "2-bit");
    construct_int!(u4, U4, "4-bit");
    construct_int!(u8, U8, "8-bit");
    construct_int!(u16, U16, "16-bit");
    construct_int!(u32, U32, "32-bit");
    construct_int!(u64, U64, "64-bit");
    construct_int!(u128, U128, "128-bit");
    construct_int!(u256, U256, "256-bit");
}

/// Various type destructors for types that maintain the structure in which they were created.
///
/// [`StructuralType`] collapses its structure into Simplicity's units, sums and products,
/// which is why it does not implement this trait.
pub trait TypeDeconstructible: Sized {
    /// Access the left and right types of a sum.
    fn as_either(&self) -> Option<(&Self, &Self)>;

    /// Access the inner type of an option.
    fn as_option(&self) -> Option<&Self>;

    /// Check if the type is Boolean.
    fn is_boolean(&self) -> bool;

    /// Access the internals of an integer type.
    fn as_integer(&self) -> Option<UIntType>;

    /// Access the element types of a tuple.
    fn as_tuple(&self) -> Option<&[Arc<Self>]>;

    /// Check if the type is the unit (empty tuple).
    fn is_unit(&self) -> bool {
        matches!(self.as_tuple(), Some(components) if components.is_empty())
    }

    /// Access the element type and size of an array.
    fn as_array(&self) -> Option<(&Self, usize)>;

    /// Access the element type and bound of a list.
    fn as_list(&self) -> Option<(&Self, NonZeroPow2Usize)>;
}

/// Internal structure of a SimplicityHL type.
///
/// 1:1 isomorphism to Simplicity.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct StructuralType(Arc<Final>);

impl AsRef<Final> for StructuralType {
    fn as_ref(&self) -> &Final {
        &self.0
    }
}

impl From<StructuralType> for Arc<Final> {
    fn from(value: StructuralType) -> Self {
        value.0
    }
}

impl From<Arc<Final>> for StructuralType {
    fn from(value: Arc<Final>) -> Self {
        Self(value)
    }
}

impl TreeLike for StructuralType {
    fn as_node(&self) -> Tree<Self> {
        match self.0.bound() {
            CompleteBound::Unit => Tree::Nullary,
            CompleteBound::Sum(l, r) | CompleteBound::Product(l, r) => {
                Tree::Binary(Self(l.clone()), Self(r.clone()))
            }
        }
    }
}

impl fmt::Debug for StructuralType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for StructuralType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<UIntType> for StructuralType {
    fn from(value: UIntType) -> Self {
        let inner = match value {
            UIntType::U1 => Final::two_two_n(0),
            UIntType::U2 => Final::two_two_n(1),
            UIntType::U4 => Final::two_two_n(2),
            UIntType::U8 => Final::two_two_n(3),
            UIntType::U16 => Final::two_two_n(4),
            UIntType::U32 => Final::two_two_n(5),
            UIntType::U64 => Final::two_two_n(6),
            UIntType::U128 => Final::two_two_n(7),
            UIntType::U256 => Final::two_two_n(8),
        };
        Self(inner)
    }
}

impl TypeConstructible for StructuralType {
    fn either(left: Self, right: Self) -> Self {
        Self(Final::sum(left.0, right.0))
    }

    fn option(inner: Self) -> Self {
        Self::either(Self::unit(), inner)
    }

    fn boolean() -> Self {
        Self::either(Self::unit(), Self::unit())
    }

    fn tuple<I: IntoIterator<Item = Self>>(elements: I) -> Self {
        let elements: Vec<_> = elements.into_iter().collect();
        let tree = BTreeSlice::from_slice(&elements);
        tree.fold(Self::product).unwrap_or_else(Self::unit)
    }

    // Keep this implementation to prevent an infinite loop in <Self as TypeConstructible>::tuple
    fn unit() -> Self {
        Self(Final::unit())
    }

    // Keep this implementation to prevent an infinite loop in <Self as TypeConstructible>::tuple
    fn product(left: Self, right: Self) -> Self {
        Self(Final::product(left.0, right.0))
    }

    fn array(element: Self, size: usize) -> Self {
        // Cheap clone because Arc<Final> consists of Arcs
        let elements = vec![element; size];
        let tree = BTreeSlice::from_slice(&elements);
        tree.fold(Self::product).unwrap_or_else(Self::unit)
    }

    fn list(element: Self, bound: NonZeroPow2Usize) -> Self {
        // Cheap clone because Arc<Final> consists of Arcs
        let el_vector = vec![element.0; bound.get() - 1];
        let partition = Partition::from_slice(&el_vector, bound);
        debug_assert!(partition.is_complete());
        let process = |block: &[Arc<Final>], size: usize| -> Arc<Final> {
            debug_assert_eq!(block.len(), size);
            let tree = BTreeSlice::from_slice(block);
            let array = tree.fold(Final::product).unwrap();
            Final::sum(Final::unit(), array)
        };
        let inner = partition.fold(process, Final::product);
        Self(inner)
    }
}

impl StructuralType {
    /// The balanced sum of the given leaf types.
    /// The structural type of an enum whose variants have these payload types.
    /// The tree shape is the one of [`BTreeSlice`], values ([`StructuralValue::enum_injection`])
    /// and the match lowering navigate the same shape.
    ///
    /// ## Panics
    ///
    /// `leaves` is empty: a sum of zero types would be uninhabited.
    ///
    /// [`StructuralValue::enum_injection`]: crate::value::StructuralValue
    pub(crate) fn balanced_sum(leaves: Vec<Self>) -> Self {
        BTreeSlice::from_slice(&leaves)
            .fold(Self::either)
            .expect("at least one leaf")
    }

    /// Convert into an unfinalized type that can be used in Simplicity's unification algorithm.
    pub fn to_unfinalized<'brand>(
        &self,
        inference_context: &simplicity::types::Context<'brand>,
    ) -> simplicity::types::Type<'brand> {
        simplicity::types::Type::complete(inference_context, self.0.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::str::Identifier;

    #[test]
    fn display_type() {
        let unit = ResolvedType::unit();
        assert_eq!("()", &unit.to_string());
        let singleton = ResolvedType::tuple([ResolvedType::u1()]);
        assert_eq!("(u1,)", &singleton.to_string());
        let pair = ResolvedType::tuple([ResolvedType::u1(), ResolvedType::u8()]);
        assert_eq!("(u1, u8)", &pair.to_string());
        let triple =
            ResolvedType::tuple([ResolvedType::u1(), ResolvedType::u8(), ResolvedType::u16()]);
        assert_eq!("(u1, u8, u16)", &triple.to_string());
        let empty_array = ResolvedType::array(ResolvedType::unit(), 0);
        assert_eq!("[(); 0]", &empty_array.to_string());
        let array = ResolvedType::array(ResolvedType::unit(), 3);
        assert_eq!("[(); 3]", &array.to_string());
        let list = ResolvedType::list(ResolvedType::unit(), NonZeroPow2Usize::TWO);
        assert_eq!("List<(), 2>", &list.to_string());
        let either = ResolvedType::either(ResolvedType::unit(), ResolvedType::u32());
        assert_eq!("Either<(), u32>", &either.to_string());
    }

    #[test]
    fn enum_variant_info_payload_types() {
        let unit = EnumVariantInfo::new(Identifier::from_str_unchecked("Unit"), Arc::from([]));
        assert_eq!(&ResolvedType::unit(), unit.payload_type());

        let single = EnumVariantInfo::new(
            Identifier::from_str_unchecked("Single"),
            Arc::from([ResolvedType::boolean()]),
        );
        assert_eq!(&ResolvedType::boolean(), single.payload_type());

        let pair = EnumVariantInfo::new(
            Identifier::from_str_unchecked("Pair"),
            Arc::from([ResolvedType::boolean(), ResolvedType::boolean()]),
        );
        assert_eq!(
            &ResolvedType::tuple([ResolvedType::boolean(), ResolvedType::boolean()]),
            pair.payload_type()
        );

        let info = EnumInfo::new(Arc::from("Test"), Arc::from([unit, single, pair]));
        assert_eq!("Test", info.name());
        assert_eq!(3, info.structural_variants().len());
        let (index, variant) = info
            .variant(&Identifier::from_str_unchecked("Pair"))
            .expect("Pair is a declared variant");
        assert_eq!(2, index);
        assert_eq!("Pair", variant.name());
    }
}
