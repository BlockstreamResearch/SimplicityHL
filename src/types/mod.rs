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
    use simplicity::dag::{DagLike, InternalSharing};
    use simplicity::types::{CompleteBound, Final};

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
        let never = ResolvedType::never();
        assert_eq!("!", &never.to_string());
        let option_never = ResolvedType::option(ResolvedType::never());
        assert_eq!("Option<!>", &option_never.to_string());
    }

    #[test]
    fn builtin_alias_tag_is_not_part_of_the_type() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let hash = |ty: &ResolvedType| {
            let mut hasher = DefaultHasher::new();
            ty.hash(&mut hasher);
            hasher.finish()
        };

        let pubkey = BuiltinAlias::Pubkey.resolve();
        let u256 = ResolvedType::u256();
        assert_eq!(Some(BuiltinAlias::Pubkey), pubkey.builtin_alias());
        assert_eq!(None, u256.builtin_alias());
        assert_eq!(pubkey, u256);
        assert!(pubkey.same_as(&u256));
        assert_eq!(hash(&pubkey), hash(&u256));
        assert_eq!("u256", &pubkey.to_string());

        let point = BuiltinAlias::Point.resolve();
        assert_eq!(Some(BuiltinAlias::Point), point.builtin_alias());
        assert_eq!(
            ResolvedType::tuple([ResolvedType::u1(), ResolvedType::u256()]),
            point
        );
    }

    #[test]
    fn never_type() {
        assert!(ResolvedType::never().is_never());
        assert!(!ResolvedType::unit().is_never());
        // Only the outermost type is checked
        assert!(!ResolvedType::option(ResolvedType::never()).is_never());
    }

    #[test]
    #[should_panic(expected = "the never type has no structural type")]
    fn never_type_has_no_structural_type() {
        let _ = StructuralType::from(&ResolvedType::option(ResolvedType::never()));
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

    #[test]
    fn lowering_shared_subtypes_preserves_sharing() {
        let depth = 12;
        let mut ty = ResolvedType::u8();
        for _ in 0..depth {
            ty = ResolvedType::product(ty.clone(), ty);
        }

        let lowered = StructuralType::from(&ty);
        assert_eq!(
            lowered.as_ref(),
            Final::two_two_n(depth + 3).unwrap().as_ref()
        );
        // Count retained nodes rather than timing the conversion: the output
        // should be a small DAG, not the expanded tree of 2^depth leaves.
        assert!(
            lowered
                .as_ref()
                .post_order_iter::<InternalSharing>()
                .count()
                <= 2 * depth + 8
        );
    }

    #[test]
    fn lowering_shares_nested_enum_payloads_without_changing_shape() {
        let depth = 12;
        let mut shared = ResolvedType::u8();
        for _ in 0..depth {
            shared = ResolvedType::product(shared.clone(), shared);
        }
        let variant = |name, payload: Vec<ResolvedType>| {
            EnumVariantInfo::new(Identifier::from_str_unchecked(name), Arc::from(payload))
        };
        let inner = ResolvedType::enumeration(EnumInfo::new(
            Arc::from("Inner"),
            Arc::from([
                variant("Unit", vec![]),
                variant("Single", vec![shared.clone()]),
                variant("Pair", vec![ResolvedType::u16(), shared]),
                variant("Option", vec![ResolvedType::option(ResolvedType::u32())]),
                variant(
                    "List",
                    vec![ResolvedType::list(
                        ResolvedType::u8(),
                        NonZeroPow2Usize::new_unchecked(4),
                    )],
                ),
            ]),
        ));
        let outer = ResolvedType::enumeration(EnumInfo::new(
            Arc::from("Outer"),
            Arc::from([variant("Wrap", vec![inner.clone(), inner])]),
        ));

        let shared = StructuralType::from(Final::two_two_n(depth + 3).unwrap());
        let inner = StructuralType::balanced_sum(vec![
            StructuralType::unit(),
            shared.clone(),
            StructuralType::product(StructuralType::u16(), shared),
            StructuralType::option(StructuralType::u32()),
            StructuralType::list(StructuralType::u8(), NonZeroPow2Usize::new_unchecked(4)),
        ]);
        let lowered = StructuralType::from(&outer);
        assert_eq!(lowered, StructuralType::product(inner.clone(), inner));
        assert!(
            lowered
                .as_ref()
                .post_order_iter::<InternalSharing>()
                .count()
                <= 2 * depth + 64
        );
    }

    #[test]
    fn lowering_deep_types_is_iterative() {
        let depth = 8192;
        let mut ty = ResolvedType::u8();
        for _ in 0..depth {
            ty = ResolvedType::option(ty);
        }
        let lowered = StructuralType::from(&ty);
        assert_eq!(depth + 8, lowered.as_ref().bit_width());

        // Dismantle both chains iteratively too, so this tests lowering rather
        // than the recursive drop of their Arc-linked representation.
        while let Some(inner) = ty.as_option() {
            ty = inner.clone();
        }
        let mut lowered: Arc<Final> = lowered.into();
        while let CompleteBound::Sum(_, inner) = lowered.bound() {
            lowered = Arc::clone(inner);
        }
    }
}
