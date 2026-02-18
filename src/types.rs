use std::fmt;
use std::str::FromStr;
use std::sync::Arc;

use miniscript::iter::{Tree, TreeLike};
use simplicity::types::{CompleteBound, Final};

use crate::array::{BTreeSlice, Partition};
use crate::num::{NonZeroPow2Usize, Pow2Usize};
use crate::str::AliasName;

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
    /// Error type
    Error,
}

impl<A> TypeInner<A> {
    /// Helper method for displaying type primitives based on the number of yielded children.
    ///
    /// We cannot implement [`fmt::Display`] because `n_children_yielded` is an extra argument.
    fn display(&self, f: &mut fmt::Formatter<'_>, n_children_yielded: usize) -> fmt::Result {
        match self {
            TypeInner::Either(_, _) => match n_children_yielded {
                0 => f.write_str("Either<"),
                1 => f.write_str(","),
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
            TypeInner::Error => write!(f, "ERROR"),
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

impl TryFrom<&ResolvedType> for UIntType {
    type Error = ();

    fn try_from(value: &ResolvedType) -> Result<Self, Self::Error> {
        UIntType::try_from(&StructuralType::from(value))
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

/// SimplicityHL type without type aliases.
#[derive(PartialEq, Eq, Hash, Clone)]
pub struct ResolvedType(TypeInner<Arc<Self>>);

impl ResolvedType {
    /// Access the inner type primitive.
    pub fn as_inner(&self) -> &TypeInner<Arc<Self>> {
        &self.0
    }

    pub const fn error() -> Self {
        Self(TypeInner::Error)
    }

    pub fn is_error(&self) -> bool {
        matches!(self.as_inner(), TypeInner::Error)
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
            TypeInner::Boolean | TypeInner::UInt(..) => Tree::Nullary,
            TypeInner::Option(l) | TypeInner::Array(l, _) | TypeInner::List(l, _) => Tree::Unary(l),
            TypeInner::Either(l, r) => Tree::Binary(l, r),
            TypeInner::Tuple(elements) => Tree::Nary(elements.iter().map(Arc::as_ref).collect()),
            TypeInner::Error => Tree::Nullary,
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
                    let bound = NonZeroPow2Usize::arbitrary(u)?;
                    Ok(Self::list(element, bound))
                }
                _ => unreachable!(),
            },
        }
    }
}

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for ResolvedType {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        <Self as crate::ArbitraryRec>::arbitrary_rec(u, 3)
    }
}

/// SimplicityHL type with type aliases.
#[derive(PartialEq, Eq, Hash, Clone)]
pub struct AliasedType(AliasedInner);

/// Type alias or primitive.
///
/// Private struct to allow future changes.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
enum AliasedInner {
    /// Type alias.
    Alias(AliasName),
    /// Builtin type alias.
    Builtin(BuiltinAlias),
    /// Type primitive.
    Inner(TypeInner<Arc<AliasedType>>),
}

/// Type alias with predefined definition.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum BuiltinAlias {
    Ctx8,
    Pubkey,
    Message,
    Message64,
    Signature,
    Scalar,
    Fe,
    Ge,
    Gej,
    Point,
    Height,
    Time,
    Distance,
    Duration,
    Lock,
    Outpoint,
    Confidential1,
    ExplicitAsset,
    Asset1,
    ExplicitAmount,
    Amount1,
    ExplicitNonce,
    Nonce,
    TokenAmount1,
}

impl AliasedType {
    /// Access a user-defined alias.
    pub const fn as_alias(&self) -> Option<&AliasName> {
        match &self.0 {
            AliasedInner::Alias(name) => Some(name),
            _ => None,
        }
    }

    /// Access a buitlin alias.
    pub const fn as_builtin(&self) -> Option<&BuiltinAlias> {
        match &self.0 {
            AliasedInner::Builtin(builtin) => Some(builtin),
            _ => None,
        }
    }

    pub fn error() -> Self {
        Self(AliasedInner::Inner(TypeInner::Error))
    }

    /// Create a type alias from the given `identifier`.
    pub const fn alias(name: AliasName) -> Self {
        Self(AliasedInner::Alias(name))
    }

    /// Create a builtin type alias.
    pub const fn builtin(builtin: BuiltinAlias) -> Self {
        Self(AliasedInner::Builtin(builtin))
    }

    /// Resolve all aliases in the type based on the given map of `aliases` to types.
    pub fn resolve<F>(&self, mut get_alias: F) -> Result<ResolvedType, AliasName>
    where
        F: FnMut(&AliasName) -> Option<ResolvedType>,
    {
        let mut output = vec![];
        for data in self.post_order_iter() {
            match &data.node.0 {
                AliasedInner::Alias(name) => {
                    let resolved = get_alias(name).ok_or(name.clone())?;
                    output.push(resolved);
                }
                AliasedInner::Builtin(builtin) => {
                    let resolved = builtin.resolve();
                    output.push(resolved);
                }
                AliasedInner::Inner(inner) => match inner {
                    TypeInner::Either(_, _) => {
                        let right = output.pop().unwrap();
                        let left = output.pop().unwrap();
                        output.push(ResolvedType::either(left, right));
                    }
                    TypeInner::Option(_) => {
                        let inner = output.pop().unwrap();
                        output.push(ResolvedType::option(inner));
                    }
                    TypeInner::Boolean => output.push(ResolvedType::boolean()),
                    TypeInner::UInt(integer) => output.push(ResolvedType::from(*integer)),
                    TypeInner::Tuple(_) => {
                        let size = data.node.n_children();
                        let elements = output.split_off(output.len() - size);
                        debug_assert_eq!(elements.len(), size);
                        output.push(ResolvedType::tuple(elements));
                    }
                    TypeInner::Array(_, size) => {
                        let element = output.pop().unwrap();
                        output.push(ResolvedType::array(element, *size));
                    }
                    TypeInner::List(_, bound) => {
                        let element = output.pop().unwrap();
                        output.push(ResolvedType::list(element, *bound));
                    }
                    TypeInner::Error => return Ok(ResolvedType::error()),
                },
            }
        }
        debug_assert_eq!(output.len(), 1);
        Ok(output.pop().unwrap())
    }

    /// Resolve all aliases in the type based on the builtin type aliases only.
    pub fn resolve_builtin(&self) -> Result<ResolvedType, AliasName> {
        self.resolve(|_| None)
    }
}

impl TypeConstructible for AliasedType {
    fn either(left: Self, right: Self) -> Self {
        Self(AliasedInner::Inner(TypeInner::Either(
            Arc::new(left),
            Arc::new(right),
        )))
    }

    fn option(inner: Self) -> Self {
        Self(AliasedInner::Inner(TypeInner::Option(Arc::new(inner))))
    }

    fn boolean() -> Self {
        Self(AliasedInner::Inner(TypeInner::Boolean))
    }

    fn tuple<I: IntoIterator<Item = Self>>(elements: I) -> Self {
        Self(AliasedInner::Inner(TypeInner::Tuple(
            elements.into_iter().map(Arc::new).collect(),
        )))
    }

    fn array(element: Self, size: usize) -> Self {
        Self(AliasedInner::Inner(TypeInner::Array(
            Arc::new(element),
            size,
        )))
    }

    fn list(element: Self, bound: NonZeroPow2Usize) -> Self {
        Self(AliasedInner::Inner(TypeInner::List(
            Arc::new(element),
            bound,
        )))
    }
}

impl TypeDeconstructible for AliasedType {
    fn as_either(&self) -> Option<(&Self, &Self)> {
        match &self.0 {
            AliasedInner::Inner(TypeInner::Either(ty_l, ty_r)) => Some((ty_l, ty_r)),
            _ => None,
        }
    }

    fn as_option(&self) -> Option<&Self> {
        match &self.0 {
            AliasedInner::Inner(TypeInner::Option(ty)) => Some(ty),
            _ => None,
        }
    }

    fn is_boolean(&self) -> bool {
        matches!(&self.0, AliasedInner::Inner(TypeInner::Boolean))
    }

    fn as_integer(&self) -> Option<UIntType> {
        match &self.0 {
            AliasedInner::Inner(TypeInner::UInt(ty)) => Some(*ty),
            _ => None,
        }
    }

    fn as_tuple(&self) -> Option<&[Arc<Self>]> {
        match &self.0 {
            AliasedInner::Inner(TypeInner::Tuple(components)) => Some(components),
            _ => None,
        }
    }

    fn as_array(&self) -> Option<(&Self, usize)> {
        match &self.0 {
            AliasedInner::Inner(TypeInner::Array(ty, size)) => Some((ty, *size)),
            _ => None,
        }
    }

    fn as_list(&self) -> Option<(&Self, NonZeroPow2Usize)> {
        match &self.0 {
            AliasedInner::Inner(TypeInner::List(ty, bound)) => Some((ty, *bound)),
            _ => None,
        }
    }
}

impl TreeLike for &AliasedType {
    fn as_node(&self) -> Tree<Self> {
        match &self.0 {
            AliasedInner::Alias(_) | AliasedInner::Builtin(_) => Tree::Nullary,
            AliasedInner::Inner(inner) => match inner {
                TypeInner::Boolean | TypeInner::UInt(..) => Tree::Nullary,
                TypeInner::Option(l) | TypeInner::Array(l, _) | TypeInner::List(l, _) => {
                    Tree::Unary(l)
                }
                TypeInner::Either(l, r) => Tree::Binary(l, r),
                TypeInner::Tuple(elements) => {
                    Tree::Nary(elements.iter().map(Arc::as_ref).collect())
                }
                TypeInner::Error => Tree::Nullary,
            },
        }
    }
}

impl fmt::Debug for AliasedType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl fmt::Display for AliasedType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for data in self.verbose_pre_order_iter() {
            match &data.node.0 {
                AliasedInner::Alias(alias) => write!(f, "{alias}")?,
                AliasedInner::Builtin(builtin) => write!(f, "{builtin}")?,
                AliasedInner::Inner(inner) => inner.display(f, data.n_children_yielded)?,
            }
        }
        Ok(())
    }
}

impl From<UIntType> for AliasedType {
    fn from(value: UIntType) -> Self {
        Self(AliasedInner::Inner(TypeInner::UInt(value)))
    }
}

impl From<AliasName> for AliasedType {
    fn from(value: AliasName) -> Self {
        Self::alias(value)
    }
}

impl From<BuiltinAlias> for AliasedType {
    fn from(value: BuiltinAlias) -> Self {
        Self::builtin(value)
    }
}

#[cfg(feature = "arbitrary")]
impl crate::ArbitraryRec for AliasedType {
    fn arbitrary_rec(u: &mut arbitrary::Unstructured, budget: usize) -> arbitrary::Result<Self> {
        use arbitrary::Arbitrary;

        match budget.checked_sub(1) {
            None => match u.int_in_range(0..=3)? {
                0 => AliasName::arbitrary(u).map(Self::alias),
                1 => BuiltinAlias::arbitrary(u).map(Self::builtin),
                2 => Ok(Self::boolean()),
                3 => UIntType::arbitrary(u).map(Self::from),
                _ => unreachable!(),
            },
            Some(new_budget) => match u.int_in_range(0..=8)? {
                0 => AliasName::arbitrary(u).map(Self::alias),
                1 => BuiltinAlias::arbitrary(u).map(Self::builtin),
                2 => Ok(Self::boolean()),
                3 => UIntType::arbitrary(u).map(Self::from),
                4 => Self::arbitrary_rec(u, new_budget).map(Self::option),
                5 => {
                    let left = Self::arbitrary_rec(u, new_budget)?;
                    let right = Self::arbitrary_rec(u, new_budget)?;
                    Ok(Self::either(left, right))
                }
                6 => {
                    let len = u.int_in_range(0..=3)?;
                    (0..len)
                        .map(|_| Self::arbitrary_rec(u, new_budget))
                        .collect::<arbitrary::Result<Vec<Self>>>()
                        .map(Self::tuple)
                }
                7 => {
                    let element = Self::arbitrary_rec(u, new_budget)?;
                    let size = u.int_in_range(0..=3)?;
                    Ok(Self::array(element, size))
                }
                8 => {
                    let element = Self::arbitrary_rec(u, new_budget)?;
                    let bound = NonZeroPow2Usize::arbitrary(u)?;
                    Ok(Self::list(element, bound))
                }
                _ => unreachable!(),
            },
        }
    }
}

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for AliasedType {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        <Self as crate::ArbitraryRec>::arbitrary_rec(u, 3)
    }
}

impl BuiltinAlias {
    pub fn resolve(self) -> ResolvedType {
        use BuiltinAlias as B;
        use UIntType::*;

        match self {
            B::Ctx8 => ResolvedType::tuple([
                ResolvedType::list(U8.into(), NonZeroPow2Usize::new(64).unwrap()),
                ResolvedType::tuple([U64.into(), U256.into()]),
            ]),
            B::Pubkey | B::Message | B::Scalar | B::Fe | B::ExplicitAsset | B::ExplicitNonce => {
                U256.into()
            }
            B::Message64 | B::Signature => ResolvedType::array(U8.into(), 64),
            B::Ge => ResolvedType::tuple([U256.into(), U256.into()]),
            B::Gej => {
                ResolvedType::tuple([ResolvedType::tuple([U256.into(), U256.into()]), U256.into()])
            }
            B::Point | B::Confidential1 => ResolvedType::tuple([U1.into(), U256.into()]),
            B::Height | B::Time | B::Lock => U32.into(),
            B::Distance | B::Duration => U16.into(),
            B::Outpoint => ResolvedType::tuple([U256.into(), U32.into()]),
            B::Asset1 | B::Nonce => {
                ResolvedType::either(ResolvedType::tuple([U1.into(), U256.into()]), U256.into())
            }
            B::ExplicitAmount => U64.into(),
            B::Amount1 | B::TokenAmount1 => {
                ResolvedType::either(ResolvedType::tuple([U1.into(), U256.into()]), U64.into())
            }
        }
    }
}

impl fmt::Debug for BuiltinAlias {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl fmt::Display for BuiltinAlias {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BuiltinAlias::Ctx8 => f.write_str("Ctx8"),
            BuiltinAlias::Pubkey => f.write_str("Pubkey"),
            BuiltinAlias::Message => f.write_str("Message"),
            BuiltinAlias::Message64 => f.write_str("Message64"),
            BuiltinAlias::Signature => f.write_str("Signature"),
            BuiltinAlias::Scalar => f.write_str("Scalar"),
            BuiltinAlias::Fe => f.write_str("Fe"),
            BuiltinAlias::Ge => f.write_str("Ge"),
            BuiltinAlias::Gej => f.write_str("Gej"),
            BuiltinAlias::Point => f.write_str("Point"),
            BuiltinAlias::Height => f.write_str("Height"),
            BuiltinAlias::Time => f.write_str("Time"),
            BuiltinAlias::Distance => f.write_str("Distance"),
            BuiltinAlias::Duration => f.write_str("Duration"),
            BuiltinAlias::Lock => f.write_str("Lock"),
            BuiltinAlias::Outpoint => f.write_str("Outpoint"),
            BuiltinAlias::Confidential1 => f.write_str("Confidential1"),
            BuiltinAlias::ExplicitAsset => f.write_str("ExplicitAsset"),
            BuiltinAlias::Asset1 => f.write_str("Asset1"),
            BuiltinAlias::ExplicitAmount => f.write_str("ExplicitAmount"),
            BuiltinAlias::Amount1 => f.write_str("Amount1"),
            BuiltinAlias::ExplicitNonce => f.write_str("ExplicitNonce"),
            BuiltinAlias::Nonce => f.write_str("Nonce"),
            BuiltinAlias::TokenAmount1 => f.write_str("TokenAmount1"),
        }
    }
}

impl FromStr for BuiltinAlias {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "Ctx8" => Ok(BuiltinAlias::Ctx8),
            "Pubkey" => Ok(BuiltinAlias::Pubkey),
            "Message" => Ok(BuiltinAlias::Message),
            "Message64" => Ok(BuiltinAlias::Message64),
            "Signature" => Ok(BuiltinAlias::Signature),
            "Scalar" => Ok(BuiltinAlias::Scalar),
            "Fe" => Ok(BuiltinAlias::Fe),
            "Ge" => Ok(BuiltinAlias::Ge),
            "Gej" => Ok(BuiltinAlias::Gej),
            "Point" => Ok(BuiltinAlias::Point),
            "Height" => Ok(BuiltinAlias::Height),
            "Time" => Ok(BuiltinAlias::Time),
            "Distance" => Ok(BuiltinAlias::Distance),
            "Duration" => Ok(BuiltinAlias::Duration),
            "Lock" => Ok(BuiltinAlias::Lock),
            "Outpoint" => Ok(BuiltinAlias::Outpoint),
            "Confidential1" => Ok(BuiltinAlias::Confidential1),
            "ExplicitAsset" => Ok(BuiltinAlias::ExplicitAsset),
            "Asset1" => Ok(BuiltinAlias::Asset1),
            "ExplicitAmount" => Ok(BuiltinAlias::ExplicitAmount),
            "Amount1" => Ok(BuiltinAlias::Amount1),
            "ExplicitNonce" => Ok(BuiltinAlias::ExplicitNonce),
            "Nonce" => Ok(BuiltinAlias::Nonce),
            "TokenAmount1" => Ok(BuiltinAlias::TokenAmount1),
            _ => Err("Unknown alias".to_string()),
        }
    }
}

/// Internal structure of a SimplicityHL type.
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
        write!(f, "{}", &self.0)
    }
}

impl fmt::Display for StructuralType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", &self.0)
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
                // Not sure what to put here, but it should not be unreachable in correctly builded
                // AST.
                TypeInner::Error => output.push(StructuralType::unit()),
            }
        }
        debug_assert_eq!(output.len(), 1);
        output.pop().unwrap()
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
    }
}
