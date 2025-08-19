use std::fmt;
use std::sync::Arc;

use either::Either;
use miniscript::bitcoin::hex::DisplayHex;
use miniscript::iter::{Tree, TreeLike};
use simplicity::types::Final as SimType;
use simplicity::{BitCollector, Value as SimValue, ValueRef};

use crate::array::{BTreeSlice, Combiner, Partition, Unfolder};
use crate::error::{Error, RichError, WithSpan};
use crate::num::{NonZeroPow2Usize, Pow2Usize, U256};
use crate::parse::ParseFromStr;
use crate::str::{Binary, Decimal, Hexadecimal};
use crate::types::{
    ResolvedType, StructuralType, TypeConstructible, TypeDeconstructible, TypeInner, UIntType,
};
use crate::{ast, parse};

/// Unsigned integer value.
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
pub enum UIntValue {
    /// 1-bit unsigned integer.
    U1(u8),
    /// 2-bit unsigned integer.
    U2(u8),
    /// 4-bit unsigned integer.
    U4(u8),
    /// 8-bit unsigned integer.
    U8(u8),
    /// 16-bit unsigned integer.
    U16(u16),
    /// 32-bit unsigned integer.
    U32(u32),
    /// 64-bit unsigned integer.
    U64(u64),
    /// 128-bit unsigned integer.
    U128(u128),
    /// 256-bit unsigned integer.
    U256(U256),
}

impl fmt::Debug for UIntValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self, self.get_type())
    }
}

impl fmt::Display for UIntValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UIntValue::U1(n) => <u8 as fmt::Display>::fmt(n, f),
            UIntValue::U2(n) => <u8 as fmt::Display>::fmt(n, f),
            UIntValue::U4(n) => <u8 as fmt::Display>::fmt(n, f),
            UIntValue::U8(n) => <u8 as fmt::Display>::fmt(n, f),
            UIntValue::U16(n) => <u16 as fmt::Display>::fmt(n, f),
            UIntValue::U32(n) => <u32 as fmt::Display>::fmt(n, f),
            UIntValue::U64(n) => <u64 as fmt::Display>::fmt(n, f),
            UIntValue::U128(n) => write!(f, "0x{}", n.to_be_bytes().as_hex()),
            UIntValue::U256(n) => write!(f, "0x{}", n.as_ref().as_hex()),
        }
    }
}

impl UIntValue {
    /// Get the type of type value.
    pub const fn get_type(self) -> UIntType {
        match self {
            UIntValue::U1(_) => UIntType::U1,
            UIntValue::U2(_) => UIntType::U2,
            UIntValue::U4(_) => UIntType::U4,
            UIntValue::U8(_) => UIntType::U8,
            UIntValue::U16(_) => UIntType::U16,
            UIntValue::U32(_) => UIntType::U32,
            UIntValue::U64(_) => UIntType::U64,
            UIntValue::U128(_) => UIntType::U128,
            UIntValue::U256(_) => UIntType::U256,
        }
    }

    /// Check if the value is of the given type.
    pub fn is_of_type(self, ty: UIntType) -> bool {
        self.get_type() == ty
    }

    /// Create a value of type `u1`.
    ///
    /// ## Errors
    ///
    /// Value is greater than 1.
    pub const fn u1(value: u8) -> Result<Self, Error> {
        match value {
            0 | 1 => Ok(Self::U1(value)),
            _ => Err(Error::IntegerOutOfBounds(UIntType::U1)),
        }
    }

    /// Create a value of type `u2`.
    ///
    /// ## Errors
    ///
    /// Value is greater than 3.
    pub const fn u2(value: u8) -> Result<Self, Error> {
        match value {
            0..=3 => Ok(Self::U2(value)),
            _ => Err(Error::IntegerOutOfBounds(UIntType::U2)),
        }
    }

    /// Create a value of type `u4`.
    ///
    /// ## Errors
    ///
    /// Value is greater than 15.
    pub const fn u4(value: u8) -> Result<Self, Error> {
        match value {
            0..=15 => Ok(Self::U4(value)),
            _ => Err(Error::IntegerOutOfBounds(UIntType::U4)),
        }
    }

    /// Create an integer from a `decimal` string and type.
    pub fn parse_decimal(decimal: &Decimal, ty: UIntType) -> Result<Self, Error> {
        let s = decimal.as_inner();
        match ty {
            UIntType::U1 => s.parse::<u8>().map_err(Error::from).and_then(Self::u1),
            UIntType::U2 => s.parse::<u8>().map_err(Error::from).and_then(Self::u2),
            UIntType::U4 => s.parse::<u8>().map_err(Error::from).and_then(Self::u4),
            UIntType::U8 => s.parse::<u8>().map_err(Error::from).map(Self::U8),
            UIntType::U16 => s.parse::<u16>().map_err(Error::from).map(Self::U16),
            UIntType::U32 => s.parse::<u32>().map_err(Error::from).map(Self::U32),
            UIntType::U64 => s.parse::<u64>().map_err(Error::from).map(Self::U64),
            UIntType::U128 => s.parse::<u128>().map_err(Error::from).map(Self::U128),
            UIntType::U256 => s.parse::<U256>().map_err(Error::from).map(Self::U256),
        }
    }

    /// Create an integer from a `binary` string and type.
    pub fn parse_binary(binary: &Binary, ty: UIntType) -> Result<Self, Error> {
        let s = binary.as_inner();
        let bit_len = Pow2Usize::new(s.len()).ok_or(Error::BitStringPow2(s.len()))?;
        let bit_ty = UIntType::from_bit_width(bit_len).ok_or(Error::BitStringPow2(s.len()))?;
        if ty != bit_ty {
            return Err(Error::ExpressionTypeMismatch(ty.into(), bit_ty.into()));
        }

        let byte_len = bit_len.get().div_ceil(8);
        let mut bytes = Vec::with_capacity(byte_len);
        let padding_len = 8usize.saturating_sub(bit_len.get());
        let padding = std::iter::repeat('0').take(padding_len);
        let mut padded_bits = padding.chain(s.chars());

        for _ in 0..byte_len {
            let mut byte = 0u8;
            for _ in 0..8 {
                let bit = padded_bits.next().unwrap();
                byte = (byte << 1) | u8::from(bit == '1');
            }
            bytes.push(byte);
        }

        match ty {
            UIntType::U1 => {
                debug_assert!(bytes[0] < 2);
                Ok(Self::U1(bytes[0]))
            }
            UIntType::U2 => {
                debug_assert!(bytes[0] < 4);
                Ok(Self::U2(bytes[0]))
            }
            UIntType::U4 => {
                debug_assert!(bytes[0] < 16);
                Ok(Self::U4(bytes[0]))
            }
            _ => Ok(Self::try_from(bytes.as_ref()).expect("Enough bytes")),
        }
    }
}

#[cfg(feature = "arbitrary")]
impl crate::ArbitraryOfType for UIntValue {
    type Type = UIntType;

    fn arbitrary_of_type(
        u: &mut arbitrary::Unstructured,
        ty: &Self::Type,
    ) -> arbitrary::Result<Self> {
        use arbitrary::Arbitrary;

        match ty {
            UIntType::U1 => u.int_in_range(0..=1).map(Self::U1),
            UIntType::U2 => u.int_in_range(0..=3).map(Self::U2),
            UIntType::U4 => u.int_in_range(0..=15).map(Self::U4),
            UIntType::U8 => u8::arbitrary(u).map(Self::U8),
            UIntType::U16 => u16::arbitrary(u).map(Self::U16),
            UIntType::U32 => u32::arbitrary(u).map(Self::U32),
            UIntType::U64 => u64::arbitrary(u).map(Self::U64),
            UIntType::U128 => u128::arbitrary(u).map(Self::U128),
            UIntType::U256 => U256::arbitrary(u).map(Self::U256),
        }
    }
}

impl From<u8> for UIntValue {
    fn from(value: u8) -> Self {
        Self::U8(value)
    }
}

impl From<u16> for UIntValue {
    fn from(value: u16) -> Self {
        Self::U16(value)
    }
}

impl From<u32> for UIntValue {
    fn from(value: u32) -> Self {
        Self::U32(value)
    }
}

impl From<u64> for UIntValue {
    fn from(value: u64) -> Self {
        Self::U64(value)
    }
}

impl From<u128> for UIntValue {
    fn from(value: u128) -> Self {
        Self::U128(value)
    }
}

impl From<U256> for UIntValue {
    fn from(value: U256) -> Self {
        Self::U256(value)
    }
}

impl TryFrom<&[u8]> for UIntValue {
    type Error = &'static str;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        match value.len() {
            1 => Ok(Self::U8(value[0])),
            2 => Ok(Self::U16(u16::from_be_bytes(value.try_into().unwrap()))),
            4 => Ok(Self::U32(u32::from_be_bytes(value.try_into().unwrap()))),
            8 => Ok(Self::U64(u64::from_be_bytes(value.try_into().unwrap()))),
            16 => Ok(Self::U128(u128::from_be_bytes(value.try_into().unwrap()))),
            32 => Ok(Self::U256(U256::from_byte_array(value.try_into().unwrap()))),
            _ => Err("Too many bytes"),
        }
    }
}

macro_rules! construct_int_fallible {
    ($name: ident, $ty: ty, $text: expr) => {
        #[doc = "Create"]
        #[doc = $text]
        #[doc = "integer.\n\n"]
        #[doc = "## Panics\n"]
        #[doc = "The value is ouf of range."]
        fn $name(value: $ty) -> Self {
            Self::from(UIntValue::$name(value).expect("The value is out of range"))
        }
    };
}

macro_rules! construct_int {
    ($name: ident, $ty: ty, $text: expr) => {
        #[doc = "Create"]
        #[doc = $text]
        #[doc = "integer."]
        fn $name(value: $ty) -> Self {
            Self::from(UIntValue::from(value))
        }
    };
}

/// Various value constructors.
pub trait ValueConstructible: Sized + From<bool> + From<UIntValue> {
    /// The type of the constructed value.
    type Type: TypeConstructible;

    /// Create the unit value.
    fn unit() -> Self {
        Self::tuple([])
    }

    /// Create the product value `(left, right)`.
    fn product(left: Self, right: Self) -> Self {
        Self::tuple([left, right])
    }

    /// Create the left value `Left(left)`.
    ///
    /// The type of the value is `Either<type_of<left>, right>`.
    fn left(left: Self, right: Self::Type) -> Self;

    /// Create the right value `Right(right)`.
    ///
    /// The type of the value is `Either<left, type_of<right>>`.
    fn right(left: Self::Type, right: Self) -> Self;

    /// Create the empty value `None`.
    ///
    /// The type of the value is `Option<inner>`.
    fn none(inner: Self::Type) -> Self;

    /// Create the nonempty value `Some(inner)`.
    fn some(inner: Self) -> Self;

    /// Create a tuple from the given `elements`.
    ///
    /// The empty tuple is the unit value.
    /// A tuple of two values is a product.
    fn tuple<I: IntoIterator<Item = Self>>(elements: I) -> Self;

    /// Create an array from the given `elements`.
    ///
    /// The type of the value is `[ty; elements.len()]`.
    ///
    /// ## Panics
    ///
    /// The given `elements` are not of the given type.
    fn array<I: IntoIterator<Item = Self>>(elements: I, ty: Self::Type) -> Self;

    /// Create an array from the given `bytes`.
    fn byte_array<I: IntoIterator<Item = u8>>(bytes: I) -> Self {
        let converted = bytes.into_iter().map(UIntValue::U8).map(Self::from);
        Self::array(converted, Self::Type::u8())
    }

    /// Create `bound`ed list from the given `elements`.
    ///
    /// The type of the value is `List<ty, bound>`.
    ///
    /// ## Boundedness
    ///
    /// There must be fewer `elements` than the given `bound`.
    /// The `bound` is an exclusive upper bound on the number of `elements`.
    ///
    /// ## Panics
    ///
    /// - There are too many `elements`.
    /// - The given `elements` are not of the given type.
    fn list<I: IntoIterator<Item = Self>>(
        elements: I,
        ty: Self::Type,
        bound: NonZeroPow2Usize,
    ) -> Self;

    construct_int_fallible!(u1, u8, "a 1-bit");
    construct_int_fallible!(u2, u8, "a 2-bit");
    construct_int_fallible!(u4, u8, "a 4-bit");
    construct_int!(u8, u8, "an 8-bit");
    construct_int!(u16, u16, "a 16-bit");
    construct_int!(u32, u32, "a 32-bit");
    construct_int!(u64, u64, "a 64-bit");
    construct_int!(u128, u128, "a 128-bit");
    construct_int!(u256, U256, "a 256-bit");
}

/// The structure of a SimplicityHL value.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum ValueInner {
    /// Left value.
    Either(Either<Arc<Value>, Arc<Value>>),
    /// Option value.
    Option(Option<Arc<Value>>),
    /// Boolean value.
    Boolean(bool),
    /// Unsigned integer.
    UInt(UIntValue),
    /// Tuple of values.
    ///
    /// Each component may have a different type.
    Tuple(Arc<[Value]>),
    /// Array of values.
    ///
    /// Each element must have the same type.
    Array(Arc<[Value]>),
    /// Bounded list of values.
    ///
    /// Each element must have the same type.
    /// The number of elements must be strictly less than the bound.
    /// 
    /// Safety: List construction is validated by the `list()` method which
    /// checks bounds and type consistency before creating the list.
    List(Arc<[Value]>, NonZeroPow2Usize),
}

/// A SimplicityHL value.
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct Value {
    inner: ValueInner,
    ty: ResolvedType,
}

impl TreeLike for &Value {
    fn as_node(&self) -> Tree<Self> {
        match &self.inner {
            ValueInner::Option(None) | ValueInner::Boolean(_) | ValueInner::UInt(_) => {
                Tree::Nullary
            }
            ValueInner::Either(Either::Left(l))
            | ValueInner::Either(Either::Right(l))
            | ValueInner::Option(Some(l)) => Tree::Unary(l),
            ValueInner::Tuple(elements)
            | ValueInner::Array(elements)
            | ValueInner::List(elements, _) => Tree::Nary(elements.iter().collect()),
        }
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self, self.ty())
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut print_hex_byte_array = false;
        for data in self.verbose_pre_order_iter() {
            match &data.node.inner {
                ValueInner::Either(either) => match data.n_children_yielded {
                    0 => match either {
                        Either::Left(..) => f.write_str("Left(")?,
                        Either::Right(..) => f.write_str("Right(")?,
                    },
                    n => {
                        debug_assert_eq!(n, 1);
                        f.write_str(")")?;
                    }
                },
                ValueInner::Option(option) => match data.n_children_yielded {
                    0 => match option {
                        None => f.write_str("None")?,
                        Some(..) => f.write_str("Some(")?,
                    },
                    n => {
                        debug_assert_eq!(n, 1);
                        f.write_str(")")?;
                    }
                },
                ValueInner::Boolean(bit) => write!(f, "{bit}")?,
                ValueInner::UInt(integer) => {
                    if !print_hex_byte_array {
                        write!(f, "{integer}")?
                    }
                }
                ValueInner::Tuple(tuple) => {
                    if data.n_children_yielded == 0 {
                        write!(f, "(")?;
                    } else if !data.is_complete || tuple.len() == 1 {
                        write!(f, ", ")?;
                    }
                    if data.is_complete {
                        write!(f, ")")?;
                    }
                }
                ValueInner::Array(array) => {
                    // Non-empty byte arrays are directly displayed as hex strings.
                    // This means we need to skip the array elements during the iteration.
                    // We use a Boolean variable to toggle the skipping.
                    if print_hex_byte_array && 0 < data.n_children_yielded {
                        if data.is_complete {
                            print_hex_byte_array = false;
                        }
                        continue;
                    }
                    let maybe_bytes = array
                        .iter()
                        .map(|element| match element.inner() {
                            ValueInner::UInt(UIntValue::U8(byte)) => Some(*byte),
                            _ => None,
                        })
                        .collect::<Option<Vec<u8>>>();
                    match maybe_bytes {
                        Some(bytes) if !bytes.is_empty() => {
                            write!(f, "0x{}", bytes.as_hex())?;
                            print_hex_byte_array = true;
                            continue;
                        }
                        _ => {}
                    }

                    if data.n_children_yielded == 0 {
                        write!(f, "[")?;
                    } else if !data.is_complete {
                        write!(f, ", ")?;
                    }
                    if data.is_complete {
                        write!(f, "]")?;
                    }
                }
                ValueInner::List(..) => {
                    if data.n_children_yielded == 0 {
                        write!(f, "list![")?;
                    } else if !data.is_complete {
                        write!(f, ", ")?;
                    }
                    if data.is_complete {
                        write!(f, "]")?;
                    }
                }
            }
        }

        Ok(())
    }
}

impl ValueConstructible for Value {
    type Type = ResolvedType;

    fn left(left: Self, right: Self::Type) -> Self {
        Self {
            ty: ResolvedType::either(left.ty().clone(), right),
            inner: ValueInner::Either(Either::Left(Arc::new(left))),
        }
    }

    fn right(left: Self::Type, right: Self) -> Self {
        Self {
            ty: ResolvedType::either(left, right.ty().clone()),
            inner: ValueInner::Either(Either::Right(Arc::new(right))),
        }
    }

    fn none(inner: Self::Type) -> Self {
        Self {
            inner: ValueInner::Option(None),
            ty: ResolvedType::option(inner),
        }
    }

    fn some(inner: Self) -> Self {
        Self {
            ty: ResolvedType::option(inner.ty().clone()),
            inner: ValueInner::Option(Some(Arc::new(inner))),
        }
    }

    fn tuple<I: IntoIterator<Item = Self>>(elements: I) -> Self {
        let values: Arc<[Self]> = elements.into_iter().collect();
        let ty = ResolvedType::tuple(values.iter().map(Value::ty).map(ResolvedType::clone));
        Self {
            inner: ValueInner::Tuple(values),
            ty,
        }
    }

    fn array<I: IntoIterator<Item = Self>>(elements: I, ty: Self::Type) -> Self {
        let values: Arc<[Self]> = elements.into_iter().collect();
        for value in values.iter() {
            assert!(
                value.is_of_type(&ty),
                "Element {value} is not of expected type {ty}"
            );
        }
        Self {
            ty: ResolvedType::array(ty, values.len()),
            inner: ValueInner::Array(values),
        }
    }

    fn list<I: IntoIterator<Item = Self>>(
        elements: I,
        ty: Self::Type,
        bound: NonZeroPow2Usize,
    ) -> Self {
        let elements: Arc<[Self]> = elements.into_iter().collect();
        assert!(
            elements.len() < bound.get(),
            "There must be fewer list elements than the bound {bound}"
        );
        for element in elements.iter() {
            assert!(
                element.is_of_type(&ty),
                "Element {element} is not of expected type {ty}"
            );
        }
        Self {
            inner: ValueInner::List(elements, bound),
            ty: ResolvedType::list(ty, bound),
        }
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Self {
            inner: ValueInner::Boolean(value),
            ty: ResolvedType::boolean(),
        }
    }
}

impl From<UIntValue> for Value {
    fn from(value: UIntValue) -> Self {
        Self {
            ty: value.get_type().into(),
            inner: ValueInner::UInt(value),
        }
    }
}

impl Value {
    /// Access the inner structure of the value.
    pub const fn inner(&self) -> &ValueInner {
        &self.inner
    }

    /// Access the type of the value.
    pub const fn ty(&self) -> &ResolvedType {
        &self.ty
    }

    /// Check if the value is of the given type.
    pub fn is_of_type(&self, ty: &ResolvedType) -> bool {
        self.ty() == ty
    }

    /// Create a value from the given `hexadecimal` string and type.
    pub fn parse_hexadecimal(hexadecimal: &Hexadecimal, ty: &ResolvedType) -> Result<Self, Error> {
        use miniscript::bitcoin::hex::FromHex;

        let expected_byte_len = match ty.as_inner() {
            TypeInner::UInt(int) => int.byte_width(),
            TypeInner::Array(inner, len) if inner.as_integer() == Some(UIntType::U8) => *len,
            _ => return Err(Error::ExpressionUnexpectedType(ty.clone())),
        };
        let s = hexadecimal.as_inner();
        if s.len() % 2 != 0 || s.len() != expected_byte_len * 2 {
            return Err(Error::ExpressionUnexpectedType(ty.clone()));
        }
        let bytes = Vec::<u8>::from_hex(s).expect("valid chars and valid length");
        let ret = match ty.as_inner() {
            TypeInner::UInt(..) => {
                Self::from(UIntValue::try_from(bytes.as_ref()).expect("valid length"))
            }
            TypeInner::Array(..) => Self::byte_array(bytes),
            _ => unreachable!(),
        };
        Ok(ret)
    }
}

impl Value {
    /// Create value from a constant expression.
    ///
    /// ## Errors
    ///
    /// The expression includes invalid components that cannot be (yet) evaluated at compile time:
    ///
    /// - Block expressions
    /// - Variable expressions
    /// - Witness expressions
    /// - Match expressions
    /// - Call expressions
    pub fn from_const_expr(expr: &ast::Expression) -> Option<Self> {
        use ast::ExprTree;
        use ast::SingleExpressionInner as S;

        let mut output = vec![];
        for data in ExprTree::Expression(expr).post_order_iter() {
            let single = match &data.node {
                ExprTree::Expression(..) => continue, // skip
                ExprTree::Single(single) => single,
                ExprTree::Block(..)
                | ExprTree::Statement(..)
                | ExprTree::Assignment(..)
                | ExprTree::Call(..)
                | ExprTree::Match(..) => return None, // not const
            };
            let size = data.node.n_children();
            match single.inner() {
                S::Constant(value) => output.push(value.clone()),
                S::Witness(..)
                | S::Parameter(..)
                | S::Variable(..)
                | S::Call(..)
                | S::Match(..) => return None, // not const
                S::Expression(..) => continue, // skip
                S::Tuple(..) => {
                    let elements = output.split_off(output.len() - size);
                    debug_assert_eq!(elements.len(), size);
                    output.push(Self::tuple(elements));
                }
                S::Array(..) => {
                    let elements = output.split_off(output.len() - size);
                    debug_assert_eq!(elements.len(), size);
                    let ty = single.ty().as_array().expect("value is type-checked").0;
                    output.push(Self::array(elements, ty.clone()));
                }
                S::List(..) => {
                    let elements = output.split_off(output.len() - size);
                    debug_assert_eq!(elements.len(), size);
                    let (ty, bound) = single.ty().as_list().expect("value is type-checked");
                    output.push(Self::list(elements, ty.clone(), bound));
                }
                S::Either(Either::Left(..)) => {
                    let left = output.pop().unwrap();
                    let right = single.ty().as_either().expect("value is type-checked").1;
                    output.push(Self::left(left, right.clone()));
                }
                S::Either(Either::Right(..)) => {
                    let left = single.ty().as_either().expect("value is type-checked").0;
                    let right = output.pop().unwrap();
                    output.push(Self::right(left.clone(), right));
                }
                S::Option(None) => {
                    let inner = single.ty().as_option().expect("value is type-checked");
                    output.push(Self::none(inner.clone()));
                }
                S::Option(Some(..)) => {
                    let inner = output.pop().unwrap();
                    output.push(Self::some(inner));
                }
            }
        }
        debug_assert_eq!(output.len(), 1);
        output.pop()
    }

    /// Reconstruct the given structural value according to the given type.
    ///
    /// Return `None` if reconstructing fails.
    /// In this case, the structural value was not of the given type.
    pub fn reconstruct(value: &StructuralValue, ty: &ResolvedType) -> Option<Self> {
        let mut output = vec![];
        for data in value.destruct(ty).post_order_iter() {
            let size = data.node.n_children();
            let (value, ty) = match data.node {
                Destructor::Ok { value, ty } => (value, ty),
                Destructor::WrongType => return None,
            };
            match ty.as_inner() {
                TypeInner::Boolean => {
                    let bit = destruct::as_bit(value)?;
                    output.push(Self::from(bit));
                }
                TypeInner::UInt(ty) => {
                    let integer = destruct::as_integer(value, *ty)?;
                    output.push(Self::from(integer));
                }
                TypeInner::Tuple(..) => {
                    let elements = output.split_off(output.len() - size);
                    debug_assert_eq!(elements.len(), size);
                    output.push(Self::tuple(elements));
                }
                TypeInner::Array(ty, _) => {
                    let elements = output.split_off(output.len() - size);
                    debug_assert_eq!(elements.len(), size);
                    output.push(Self::array(elements, ty.as_ref().clone()));
                }
                TypeInner::List(ty, bound) => {
                    let elements = output.split_off(output.len() - size);
                    debug_assert_eq!(elements.len(), size);
                    output.push(Self::list(elements, ty.as_ref().clone(), *bound));
                }
                TypeInner::Either(ty_l, ty_r) => {
                    let val = output.pop().unwrap();
                    match destruct::as_either(value).expect("parent is type-checked") {
                        Either::Left(..) => output.push(Self::left(val, ty_r.as_ref().clone())),
                        Either::Right(..) => output.push(Self::right(ty_l.as_ref().clone(), val)),
                    }
                }
                TypeInner::Option(ty_r) => {
                    match destruct::as_option(value).expect("parent is type-checked") {
                        None => output.push(Self::none(ty_r.as_ref().clone())),
                        Some(..) => {
                            let val_r = output.pop().unwrap();
                            output.push(Self::some(val_r));
                        }
                    }
                }
            }
        }
        debug_assert_eq!(output.len(), 1);
        output.pop()
    }

    /// Parse a value of the given type from a string.
    pub fn parse_from_str(s: &str, ty: &ResolvedType) -> Result<Self, RichError> {
        let parse_expr = parse::Expression::parse_from_str(s)?;
        let ast_expr = ast::Expression::analyze_const(&parse_expr, ty)?;
        Self::from_const_expr(&ast_expr)
            .ok_or(Error::ExpressionUnexpectedType(ty.clone()))
            .with_span(s)
    }
}

#[cfg(feature = "arbitrary")]
impl crate::ArbitraryOfType for Value {
    type Type = ResolvedType;

    fn arbitrary_of_type(
        u: &mut arbitrary::Unstructured,
        ty: &Self::Type,
    ) -> arbitrary::Result<Self> {
        use arbitrary::Arbitrary;

        match ty.as_inner() {
            TypeInner::Boolean => bool::arbitrary(u).map(Self::from),
            TypeInner::UInt(ty_int) => UIntValue::arbitrary_of_type(u, ty_int).map(Self::from),
            TypeInner::Either(ty_l, ty_r) => match u.int_in_range(0..=1)? {
                0 => Self::arbitrary_of_type(u, ty_l)
                    .map(|val_l| Self::left(val_l, ty_r.as_ref().clone())),
                1 => Self::arbitrary_of_type(u, ty_r)
                    .map(|val_r| Self::right(ty_l.as_ref().clone(), val_r)),
                _ => unreachable!(),
            },
            TypeInner::Option(ty_r) => match u.int_in_range(0..=1)? {
                0 => Ok(Self::none(ty_r.as_ref().clone())),
                1 => Self::arbitrary_of_type(u, ty_r).map(Self::some),
                _ => unreachable!(),
            },
            TypeInner::Tuple(tys) => {
                let components = tys
                    .iter()
                    .map(|ty| Self::arbitrary_of_type(u, ty))
                    .collect::<arbitrary::Result<Vec<Self>>>()?;
                Ok(Self::tuple(components))
            }
            TypeInner::Array(ty, size) => {
                let elements = (0..*size)
                    .map(|_| Self::arbitrary_of_type(u, ty))
                    .collect::<arbitrary::Result<Vec<Self>>>()?;
                Ok(Self::array(elements, ty.as_ref().clone()))
            }
            TypeInner::List(ty, bound) => {
                let size = u.int_in_range(0..=bound.get().saturating_sub(1))?;
                let elements = (0..size)
                    .map(|_| Self::arbitrary_of_type(u, ty))
                    .collect::<arbitrary::Result<Vec<Self>>>()?;
                Ok(Self::list(elements, ty.as_ref().clone(), *bound))
            }
        }
    }
}

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for Value {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        use crate::ArbitraryOfType;

        let ty = ResolvedType::arbitrary(u)?;
        Self::arbitrary_of_type(u, &ty)
    }
}

/// Structure of a SimplicityHL value.
/// 1:1 isomorphism to Simplicity.
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct StructuralValue(SimValue);

impl AsRef<SimValue> for StructuralValue {
    fn as_ref(&self) -> &SimValue {
        &self.0
    }
}

impl From<StructuralValue> for SimValue {
    fn from(value: StructuralValue) -> Self {
        value.0
    }
}

impl From<SimValue> for StructuralValue {
    fn from(value: SimValue) -> Self {
        Self(value)
    }
}

impl TreeLike for StructuralValue {
    fn as_node(&self) -> Tree<Self> {
        use simplicity::dag::{Dag, DagLike};

        match self.0.as_ref().as_dag_node() {
            Dag::Nullary => Tree::Nullary,
            Dag::Unary(l) => Tree::Unary(Self(l.to_value())),
            Dag::Binary(l, r) => Tree::Binary(Self(l.to_value()), Self(r.to_value())),
        }
    }
}

impl fmt::Debug for StructuralValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", &self.0)
    }
}

impl fmt::Display for StructuralValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", &self.0)
    }
}

impl ValueConstructible for StructuralValue {
    type Type = StructuralType;

    // Keep this implementation to prevent an infinite loop in <Self as ValueConstructible>::tuple
    fn unit() -> Self {
        Self(SimValue::unit())
    }

    // Keep this implementation to prevent an infinite loop in <Self as ValueConstructible>::tuple
    fn product(left: Self, right: Self) -> Self {
        Self(SimValue::product(left.0, right.0))
    }

    fn left(left: Self, right: Self::Type) -> Self {
        Self(SimValue::left(left.0, right.into()))
    }

    fn right(left: Self::Type, right: Self) -> Self {
        Self(SimValue::right(left.into(), right.0))
    }

    fn none(inner: Self::Type) -> Self {
        Self(SimValue::none(inner.into()))
    }

    fn some(inner: Self) -> Self {
        Self(SimValue::some(inner.0))
    }

    fn tuple<I: IntoIterator<Item = Self>>(elements: I) -> Self {
        let elements: Vec<Self> = elements.into_iter().collect();
        let tree = BTreeSlice::from_slice(&elements);
        tree.fold(Self::product).unwrap_or_else(Self::unit)
    }

    fn array<I: IntoIterator<Item = Self>>(elements: I, ty: Self::Type) -> Self {
        let elements: Vec<Self> = elements.into_iter().collect();
        for element in &elements {
            assert!(
                element.is_of_type(&ty),
                "Element {element} is not of expected type {ty}"
            );
        }
        let tree = BTreeSlice::from_slice(&elements);
        tree.fold(Self::product).unwrap_or_else(Self::unit)
    }

    fn list<I: IntoIterator<Item = Self>>(
        elements: I,
        ty: Self::Type,
        bound: NonZeroPow2Usize,
    ) -> Self {
        let elements: Vec<Self> = elements.into_iter().collect();
        assert!(
            elements.len() < bound.get(),
            "There must be fewer list elements than the bound {bound}"
        );
        for element in &elements {
            assert!(
                element.is_of_type(&ty),
                "Element {element} is not of expected type {ty}"
            );
        }
        let partition = Partition::from_slice(&elements, bound);
        let process = |block: &[Self], size: usize| -> Self {
            let tree = BTreeSlice::from_slice(block);
            match tree.fold(Self::product) {
                Some(array) => Self::some(array),
                None => Self::none(StructuralType::array(ty.clone(), size)),
            }
        };
        let ret = partition.fold(process, Self::product);
        debug_assert!(ret.is_of_type(&StructuralType::list(ty, bound)));
        ret
    }
}

impl From<bool> for StructuralValue {
    fn from(value: bool) -> Self {
        match value {
            false => Self(SimValue::left(SimValue::unit(), SimType::unit())),
            true => Self(SimValue::right(SimType::unit(), SimValue::unit())),
        }
    }
}

impl From<UIntValue> for StructuralValue {
    fn from(value: UIntValue) -> Self {
        match value {
            UIntValue::U1(n) => Self(SimValue::u1(n)),
            UIntValue::U2(n) => Self(SimValue::u2(n)),
            UIntValue::U4(n) => Self(SimValue::u4(n)),
            UIntValue::U8(n) => Self(SimValue::u8(n)),
            UIntValue::U16(n) => Self(SimValue::u16(n)),
            UIntValue::U32(n) => Self(SimValue::u32(n)),
            UIntValue::U64(n) => Self(SimValue::u64(n)),
            UIntValue::U128(n) => Self(SimValue::u128(n)),
            UIntValue::U256(n) => Self(SimValue::u256(n.to_byte_array())),
        }
    }
}

impl From<&Value> for StructuralValue {
    fn from(value: &Value) -> Self {
        let mut output = vec![];
        for data in value.post_order_iter() {
            match &data.node.inner {
                ValueInner::Either(Either::Left(_)) => {
                    let left = output.pop().unwrap();
                    let right = data.node.ty().as_either().expect("value is type-checked").1;
                    output.push(Self::left(left, right.into()));
                }
                ValueInner::Either(Either::Right(_)) => {
                    let left = data.node.ty().as_either().expect("value is type-checked").0;
                    let right = output.pop().unwrap();
                    output.push(Self::right(left.into(), right));
                }
                ValueInner::Option(None) => {
                    let inner = data.node.ty().as_option().expect("value is type-checked");
                    output.push(Self::none(inner.into()))
                }
                ValueInner::Option(Some(_)) => {
                    let inner = output.pop().unwrap();
                    output.push(Self::some(inner));
                }
                ValueInner::Boolean(bit) => output.push(Self::from(*bit)),
                ValueInner::UInt(integer) => output.push(Self::from(*integer)),
                ValueInner::Tuple(_) => {
                    let size = data.node.n_children();
                    let elements = output.split_off(output.len() - size);
                    debug_assert_eq!(elements.len(), size);
                    output.push(Self::tuple(elements));
                }
                ValueInner::Array(_) => {
                    let size = data.node.n_children();
                    let elements = output.split_off(output.len() - size);
                    debug_assert_eq!(elements.len(), size);
                    let ty = data.node.ty().as_array().expect("value is type-checked").0;
                    output.push(Self::array(elements, ty.into()));
                }
                ValueInner::List(_, bound) => {
                    let size = data.node.n_children();
                    let elements = output.split_off(output.len() - size);
                    debug_assert!(elements.len() < bound.get());
                    let ty = data.node.ty().as_list().expect("value is type-checked").0;
                    output.push(Self::list(elements, ty.into(), *bound));
                }
            }
        }
        debug_assert_eq!(output.len(), 1);
        output.pop().unwrap()
    }
}

impl StructuralValue {
    /// Check if the value is of the given type.
    pub fn is_of_type(&self, ty: &StructuralType) -> bool {
        self.as_ref().is_of_type(ty.as_ref())
    }

    fn destruct<'a>(&'a self, ty: &'a ResolvedType) -> Destructor<'a> {
        Destructor::Ok {
            value: self.0.as_ref(),
            ty,
        }
    }
}

/// An iterator over the contents of a Simplicity value in terms of a SimplicityHL type.
///
/// ## Examples
///
/// A SimplicityHL array is a nested Simplicity product.
/// The destructor allows simple iteration over all array elements.
///
/// A SimplicityHL list is a nested Simplicity product _(partition)_
/// of options of more products _(blocks)_.
/// The destructor allows simple iteration over all list elements.
///
/// ## Lazy type checking
///
/// The destructor creates a tree of Simplicity value-SimplicityHL type pairs.
/// The SimplicityHL type dictates whether the node has children.
/// Parent nodes are type-checked. Leaf nodes are not type-checked.
///
/// The destructor tries to destruct the Simplicity value into child values.
/// If destructing fails, then a single `Destructor::WrongType` leaf is created instead.
/// This leaf signifies that the entire tree is ill-typed and that the original Simplicity value
/// was not of the given SimplicityHL type.`Destructor::WrongType` leaves, if there are any,
/// should appear early during post-order iteration, enabling early termination.
///
/// The leaf values (Boolean, unsigned integer, empty tuple, empty array) are not checked.
/// Extraction of actual SimplicityHL values (Boolean, unsigned integer, ...)
/// from the leaf Simplicity values may fail, in which case the entire tree is, again, ill-typed.
#[derive(Clone, Debug)]
enum Destructor<'a> {
    Ok {
        value: ValueRef<'a>,
        ty: &'a ResolvedType,
    },
    WrongType,
}

impl<'a> Destructor<'a> {
    /// Create a destructor for the given Simplicity `value` and the given SimplicityHL type.
    pub const fn new(value: ValueRef<'a>, ty: &'a ResolvedType) -> Self {
        Self::Ok { value, ty }
    }

    const fn new_pair((value, ty): (ValueRef<'a>, &'a ResolvedType)) -> Self {
        Self::Ok { value, ty }
    }
}

impl TreeLike for Destructor<'_> {
    fn as_node(&self) -> Tree<Self> {
        let (value, ty) = match self {
            Self::Ok { value, ty } => (value.clone(), ty),
            Self::WrongType => return Tree::Nullary,
        };
        match ty.as_inner() {
            TypeInner::Boolean | TypeInner::UInt(..) => Tree::Nullary,
            TypeInner::Either(ty_l, ty_r) => match destruct::as_either(value) {
                Some(Either::Left(val_l)) => Tree::Unary(Self::new(val_l, ty_l)),
                Some(Either::Right(val_r)) => Tree::Unary(Self::new(val_r, ty_r)),
                None => Tree::Unary(Self::WrongType),
            },
            TypeInner::Option(ty_r) => match destruct::as_option(value) {
                Some(None) => Tree::Nullary,
                Some(Some(val_r)) => Tree::Unary(Self::new(val_r, ty_r)),
                None => Tree::Unary(Self::WrongType),
            },
            TypeInner::Tuple(tys) => match destruct::as_tuple(value, tys.len()) {
                Some(elements) => Tree::Nary(
                    elements
                        .into_iter()
                        .zip(tys.iter().map(Arc::as_ref))
                        .map(Destructor::new_pair)
                        .collect(),
                ),
                None => Tree::Unary(Self::WrongType),
            },
            TypeInner::Array(ty, size) => match destruct::as_array(value, *size) {
                Some(elements) => Tree::Nary(
                    elements
                        .into_iter()
                        .zip(std::iter::repeat(ty.as_ref()))
                        .map(Destructor::new_pair)
                        .collect(),
                ),
                None => Tree::Unary(Self::WrongType),
            },
            TypeInner::List(ty, bound) => match destruct::as_list(value, *bound) {
                Some(elements) => Tree::Nary(
                    elements
                        .into_iter()
                        .zip(std::iter::repeat(ty.as_ref()))
                        .map(Destructor::new_pair)
                        .collect(),
                ),
                None => Tree::Unary(Self::WrongType),
            },
        }
    }
}

/// Functions for destructing Simplicity values alongside SimplicityHL types.
mod destruct {
    use super::*;
    use simplicity::ValueRef;

    pub fn as_bit(value: ValueRef) -> Option<bool> {
        match value.as_left() {
            Some(unit) if unit.is_unit() => Some(false),
            _ => match value.as_right() {
                Some(unit) if unit.is_unit() => Some(true),
                _ => None,
            },
        }
    }

    pub fn as_integer(value: ValueRef, ty: UIntType) -> Option<UIntValue> {
        let bit_len = ty.bit_width().get();
        let unfolder = Unfolder::new(value, bit_len);
        let bit_values = unfolder.unfold(|v| v.as_product())?;
        let (bytes, written_bits) = bit_values.into_iter().filter_map(as_bit).collect_bits();
        if bit_len != written_bits {
            return None;
        }
        match bit_len {
            1 => Some(UIntValue::U1(bytes[0] >> 7)),
            2 => Some(UIntValue::U2(bytes[0] >> 6)),
            4 => Some(UIntValue::U4(bytes[0] >> 4)),
            8 | 16 | 32 | 64 | 128 | 256 => {
                Some(UIntValue::try_from(bytes.as_slice()).expect("Enough bytes"))
            }
            _ => unreachable!(),
        }
    }

    pub fn as_tuple(value: ValueRef, size: usize) -> Option<Vec<ValueRef>> {
        Unfolder::new(value, size).unfold(|v| v.as_product())
    }

    pub fn as_array(value: ValueRef, size: usize) -> Option<Vec<ValueRef>> {
        Unfolder::new(value, size).unfold(|v| v.as_product())
    }

    pub fn as_list<'a>(value: ValueRef<'a>, bound: NonZeroPow2Usize) -> Option<Vec<ValueRef<'a>>> {
        let as_block = |value: ValueRef<'a>, size: usize| match as_option(value) {
            Some(Some(folded)) => as_array(folded, size),
            Some(None) => Some(vec![]),
            None => None,
        };
        Combiner::new(value, bound).unfold(as_block, |v| v.as_product())
    }

    pub fn as_either(value: ValueRef) -> Option<Either<ValueRef, ValueRef>> {
        match value.as_left() {
            Some(inner) => Some(Either::Left(inner)),
            None => value.as_right().map(Either::Right),
        }
    }

    pub fn as_option(value: ValueRef) -> Option<Option<ValueRef>> {
        match value.as_left() {
            Some(inner) if inner.is_unit() => Some(None),
            _ => value.as_right().map(Some),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse;
    use crate::types::{StructuralType, TypeConstructible};

    #[test]
    fn display_value() {
        let unit = Value::unit();
        assert_eq!("()", &unit.to_string());
        let singleton = Value::tuple([Value::u1(1)]);
        assert_eq!("(1, )", &singleton.to_string());
        let pair = Value::tuple([Value::u8(1), Value::u8(42)]);
        assert_eq!("(1, 42)", &pair.to_string());
        let triple = Value::tuple([Value::u1(1), Value::u8(42), Value::u16(1337)]);
        assert_eq!("(1, 42, 1337)", &triple.to_string());
        let empty_array = Value::array([], ResolvedType::unit());
        assert_eq!("[]", &empty_array.to_string());
        let array = Value::array(
            [Value::unit(), Value::unit(), Value::unit()],
            ResolvedType::unit(),
        );
        assert_eq!("[(), (), ()]", &array.to_string());
        let list = Value::list([Value::unit()], ResolvedType::unit(), NonZeroPow2Usize::TWO);
        assert_eq!("list![()]", &list.to_string());
        let byte_array = Value::byte_array([0xde, 0xad, 0xbe, 0xef]);
        assert_eq!("0xdeadbeef", &byte_array.to_string());
    }

    #[test]
    fn value_is_of_type() {
        let bit = Value::from(false);
        let actual_boolean = ResolvedType::boolean();
        let structural_boolean = ResolvedType::either(ResolvedType::unit(), ResolvedType::unit());
        assert_eq!(
            StructuralType::from(&actual_boolean),
            StructuralType::from(&structural_boolean)
        );
        assert!(bit.is_of_type(&actual_boolean));
        assert!(!bit.is_of_type(&structural_boolean));
    }

    #[test]
    fn parse_const_expression() {
        let bound4 = NonZeroPow2Usize::new(4).unwrap();
        let string_ty_value = [
            ("false", ResolvedType::boolean(), Value::from(false)),
            ("42", ResolvedType::u8(), Value::u8(42)),
            (
                "Left(false)",
                ResolvedType::either(ResolvedType::boolean(), ResolvedType::unit()),
                Value::left(false.into(), ResolvedType::unit()),
            ),
            (
                "Some(false)",
                ResolvedType::option(ResolvedType::boolean()),
                Value::some(false.into()),
            ),
            (
                "(1, 2, 3)",
                ResolvedType::tuple([
                    UIntType::U1.into(),
                    UIntType::U2.into(),
                    UIntType::U4.into(),
                ]),
                Value::tuple([Value::u1(1), Value::u2(2), Value::u4(3)]),
            ),
            (
                "[1, 2, 3]",
                ResolvedType::array(UIntType::U4.into(), 3),
                Value::array(
                    [Value::u4(1), Value::u4(2), Value::u4(3)],
                    UIntType::U4.into(),
                ),
            ),
            (
                "list![1, 2, 3]",
                ResolvedType::list(UIntType::U4.into(), bound4),
                Value::list(
                    [Value::u4(1), Value::u4(2), Value::u4(3)],
                    UIntType::U4.into(),
                    bound4,
                ),
            ),
        ];

        for (string, ty, expected_value) in string_ty_value {
            let parse_expr = parse::Expression::parse_from_str(string).unwrap();
            let ast_expr = ast::Expression::analyze_const(&parse_expr, &ty).unwrap();
            let parsed_value = Value::from_const_expr(&ast_expr).unwrap();
            assert_eq!(parsed_value, expected_value);
            assert!(parsed_value.is_of_type(&ty));
        }
    }
}
