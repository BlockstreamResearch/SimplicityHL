mod aliased;
mod inner;
mod resolved;
mod structural;

use std::sync::Arc;

use crate::num::NonZeroPow2Usize;

pub use self::aliased::{AliasedType, BuiltinAlias};
pub use self::inner::{EnumInfo, EnumVariantInfo, TypeInner, UIntType};
pub use self::resolved::ResolvedType;
pub use self::structural::StructuralType;

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
