use core::fmt;
use core::str::FromStr;
use std::sync::Arc;

use crate::error::Span;
use crate::num::{NonZeroPow2Usize, Pow2Usize};
use crate::str::Identifier;

use super::{ResolvedType, StructuralType, TypeConstructible as _};

/// Primitives of the SimplicityHL type system, excluding type aliases.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
#[non_exhaustive]
pub enum TypeInner<A> {
    /// Sum of the left and right types
    Either(A, A),
    /// Option of the inner type
    Option(A),
    /// Boolean type
    Boolean,
    /// Unsigned integer type
    UInt(UIntType),
    /// Tuple of potentially different types
    Tuple(Arc<[A]>),
    /// Array of the same type
    Array(A, usize),
    /// List of the same type
    List(A, NonZeroPow2Usize),
    /// Nominal enum type, represented as a balanced sum of its variants'
    /// payload types
    Enum(Arc<EnumInfo>),
}

impl<A> TypeInner<A> {
    /// Helper method for displaying type primitives based on the number of yielded children.
    ///
    /// We cannot implement [`fmt::Display`] because `n_children_yielded` is an extra argument.
    pub(super) fn display(
        &self,
        f: &mut fmt::Formatter<'_>,
        n_children_yielded: usize,
    ) -> fmt::Result {
        match self {
            TypeInner::Either(_, _) => match n_children_yielded {
                0 => f.write_str("Either<"),
                1 => f.write_str(", "),
                n => {
                    debug_assert_eq!(n, 2);
                    f.write_str(">")
                }
            },
            TypeInner::Option(_) => match n_children_yielded {
                0 => f.write_str("Option<"),
                n => {
                    debug_assert_eq!(n, 1);
                    f.write_str(">")
                }
            },
            TypeInner::Boolean => f.write_str("bool"),
            TypeInner::UInt(ty) => write!(f, "{ty}"),
            TypeInner::Tuple(elements) => match n_children_yielded {
                0 => {
                    f.write_str("(")?;
                    if elements.is_empty() {
                        f.write_str(")")?;
                    }
                    Ok(())
                }
                n if n == elements.len() => {
                    if n == 1 {
                        f.write_str(",")?;
                    }
                    f.write_str(")")
                }
                n => {
                    debug_assert!(n < elements.len());
                    f.write_str(", ")
                }
            },
            TypeInner::Array(_, size) => match n_children_yielded {
                0 => f.write_str("["),
                n => {
                    debug_assert_eq!(n, 1);
                    write!(f, "; {size}]")
                }
            },
            TypeInner::List(_, bound) => match n_children_yielded {
                0 => f.write_str("List<"),
                n => {
                    debug_assert_eq!(n, 1);
                    write!(f, ", {bound}>")
                }
            },
            TypeInner::Enum(info) => write!(f, "{}", info.name()),
        }
    }
}

/// Unsigned integer type.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum UIntType {
    /// 1-bit unsigned integer
    U1,
    /// 2-bit unsigned integer
    U2,
    /// 4-bit unsigned integer
    U4,
    /// 8-bit unsigned integer
    U8,
    /// 16-bit unsigned integer
    U16,
    /// 32-bit unsigned integer
    U32,
    /// 64-bit unsigned integer
    U64,
    /// 128-bit unsigned integer
    U128,
    /// 256-bit unsigned integer
    U256,
}

impl UIntType {
    /// Take `n` and return the `2^n`-bit unsigned integer type.
    pub const fn two_n(n: u32) -> Option<Self> {
        match n {
            0 => Some(UIntType::U1),
            1 => Some(UIntType::U2),
            2 => Some(UIntType::U4),
            3 => Some(UIntType::U8),
            4 => Some(UIntType::U16),
            5 => Some(UIntType::U32),
            6 => Some(UIntType::U64),
            7 => Some(UIntType::U128),
            8 => Some(UIntType::U256),
            _ => None,
        }
    }

    /// Return the bit width of values of this type.
    pub const fn bit_width(self) -> Pow2Usize {
        let bit_width: usize = match self {
            UIntType::U1 => 1,
            UIntType::U2 => 2,
            UIntType::U4 => 4,
            UIntType::U8 => 8,
            UIntType::U16 => 16,
            UIntType::U32 => 32,
            UIntType::U64 => 64,
            UIntType::U128 => 128,
            UIntType::U256 => 256,
        };
        debug_assert!(bit_width.is_power_of_two());
        Pow2Usize::new_unchecked(bit_width)
    }

    /// Create the unsigned integer type for the given `bit_width`.
    pub const fn from_bit_width(bit_width: Pow2Usize) -> Option<Self> {
        match bit_width.get() {
            1 => Some(UIntType::U1),
            2 => Some(UIntType::U2),
            4 => Some(UIntType::U4),
            8 => Some(UIntType::U8),
            16 => Some(UIntType::U16),
            32 => Some(UIntType::U32),
            64 => Some(UIntType::U64),
            128 => Some(UIntType::U128),
            256 => Some(UIntType::U256),
            _ => None,
        }
    }

    /// Return the byte width of values of this type.
    ///
    /// Return 0 for types that take less than an entire byte: `u1`, `u2`, `u4`.
    pub const fn byte_width(self) -> usize {
        self.bit_width().get() / 8
    }
}

impl fmt::Debug for UIntType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl fmt::Display for UIntType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UIntType::U1 => f.write_str("u1"),
            UIntType::U2 => f.write_str("u2"),
            UIntType::U4 => f.write_str("u4"),
            UIntType::U8 => f.write_str("u8"),
            UIntType::U16 => f.write_str("u16"),
            UIntType::U32 => f.write_str("u32"),
            UIntType::U64 => f.write_str("u64"),
            UIntType::U128 => f.write_str("u128"),
            UIntType::U256 => f.write_str("u256"),
        }
    }
}

impl FromStr for UIntType {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "u1" => Ok(UIntType::U1),
            "u2" => Ok(UIntType::U2),
            "u4" => Ok(UIntType::U4),
            "u8" => Ok(UIntType::U8),
            "u16" => Ok(UIntType::U16),
            "u32" => Ok(UIntType::U32),
            "u64" => Ok(UIntType::U64),
            "u128" => Ok(UIntType::U128),
            "u256" => Ok(UIntType::U256),
            _ => Err("Unknown integer type".to_string()),
        }
    }
}

/// Definition of a nominal enum type: its name and variants in
/// declaration order.
///
/// An enum with `n` variants is represented as a balanced sum of its `n`
/// variant payload types (see [`BTreeSlice`] for the tree shape), so a value
/// of the type is exactly one of the `n` variants: an undeclared variant is
/// unrepresentable. A variant's position among the declared variants
/// determines its leaf in the sum; there is no separate discriminant.
///
/// Identity is the declared name: enums may only be declared at the top
/// level of the program's own files, so the name is unique program-wide and
/// serialized forms (such as the ABI) can identify an enum by it.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct EnumInfo {
    name: Arc<str>,
    variants: Arc<[EnumVariantInfo]>,
    span: Span,
}

impl EnumInfo {
    /// Create an enum definition with the given `name` and `variants`.
    ///
    /// `variants` must not be empty: a sum of zero types would be
    /// uninhabited, which Simplicity's type algebra cannot express.
    /// A single-variant enum is a named wrapper of its payload.
    pub(crate) fn new(name: Arc<str>, variants: Arc<[EnumVariantInfo]>, span: Span) -> Self {
        debug_assert!(!variants.is_empty());
        Self {
            name,
            variants,
            span,
        }
    }

    /// Access the declared name of the enum.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Access the variants of the enum in declaration order.
    pub fn variants(&self) -> &[EnumVariantInfo] {
        &self.variants
    }

    /// Get the variant with the given `name` and its position among the
    /// declared variants.
    ///
    /// The position determines the variant's leaf in the balanced sum.
    pub fn variant(&self, name: &Identifier) -> Option<(usize, &EnumVariantInfo)> {
        self.variants
            .iter()
            .enumerate()
            .find(|(_, v)| v.name() == name)
    }

    /// The structural payload types of all variants, in declaration order:
    /// the leaves of the enum's balanced sum.
    pub(crate) fn structural_variants(&self) -> Vec<StructuralType> {
        self.variants
            .iter()
            .map(EnumVariantInfo::structural_payload)
            .collect()
    }
}

/// One variant of a nominal enum type: its name and payload types.
///
/// A variant with no payload types is a unit variant; a variant with
/// payloads carries a tuple of values of those types.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct EnumVariantInfo {
    name: Identifier,
    payload: Arc<[ResolvedType]>,
    /// The SimplicityHL type of the variant's contents: unit for unit
    /// variants, the payload type itself for single payloads, a tuple
    /// otherwise. Precomputed so it can be borrowed during destructuring.
    payload_ty: ResolvedType,
}

impl EnumVariantInfo {
    pub(crate) fn new(name: Identifier, payload: Arc<[ResolvedType]>) -> Self {
        let payload_ty = match payload.len() {
            0 => ResolvedType::unit(),
            1 => payload[0].clone(),
            _ => ResolvedType::tuple(payload.iter().cloned()),
        };
        Self {
            name,
            payload,
            payload_ty,
        }
    }

    /// Access the name of the variant.
    pub const fn name(&self) -> &Identifier {
        &self.name
    }

    /// Access the payload types of the variant, in declaration order.
    /// Empty for unit variants.
    pub fn payload(&self) -> &[ResolvedType] {
        &self.payload
    }

    /// The SimplicityHL type of the variant's contents, as one type.
    pub fn payload_type(&self) -> &ResolvedType {
        &self.payload_ty
    }

    /// The structural type of the variant's contents: the leaf this
    /// variant occupies in the enum's balanced sum.
    pub(crate) fn structural_payload(&self) -> StructuralType {
        StructuralType::from(&self.payload_ty)
    }
}
