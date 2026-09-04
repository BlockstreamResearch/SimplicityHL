use core::fmt;
use core::str::FromStr;
use std::sync::Arc;

use miniscript::iter::{Tree, TreeLike};

use super::{ResolvedType, TypeConstructible, TypeDeconstructible, TypeInner, UIntType};
use crate::num::NonZeroPow2Usize;
use crate::str::AliasName;
use crate::unstable::impl_require_feature;

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

    /// Create a type alias from the given `identifier`.
    pub const fn alias(name: AliasName) -> Self {
        Self(AliasedInner::Alias(name))
    }

    /// Create a builtin type alias.
    pub const fn builtin(builtin: BuiltinAlias) -> Self {
        Self(AliasedInner::Builtin(builtin))
    }

    /// Resolve all aliases in the type based on the given map of `aliases` to types.
    pub fn resolve<F, E>(&self, mut get_alias: F) -> Result<ResolvedType, E>
    where
        F: FnMut(&AliasName) -> Result<ResolvedType, E>,
    {
        let mut output = vec![];
        for data in self.post_order_iter() {
            match &data.node.0 {
                AliasedInner::Alias(name) => {
                    let resolved = get_alias(name)?;
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
                    // There is no syntax for writing an enum type inline (enums enter aliased types only by name)
                    TypeInner::Enum(info) => {
                        output.push(ResolvedType(TypeInner::Enum(Arc::clone(info))));
                    }
                },
            }
        }
        debug_assert_eq!(output.len(), 1);
        Ok(output.pop().unwrap())
    }

    /// Resolve all aliases in the type based on the builtin type aliases only.
    pub fn resolve_builtin(&self) -> Result<ResolvedType, AliasName> {
        self.resolve(|name: &AliasName| Err(name.clone()))
    }
}

impl_require_feature!(AliasedType {
    recurse: 0;
});

impl_require_feature!(AliasedInner {
    variants:
        Alias(_),
        Builtin(_),
        Inner(inner),
});

impl_require_feature!(TypeInner<Arc<AliasedType>> {
    variants:
        Either(left, right),
        Option(element),
        Boolean,
        UInt(_),
        Tuple(elements),
        Array(element, _),
        List(element, _),
        Enum(_),
});

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
                TypeInner::Boolean | TypeInner::UInt(..) | TypeInner::Enum(..) => Tree::Nullary,
                TypeInner::Option(l) | TypeInner::Array(l, _) | TypeInner::List(l, _) => {
                    Tree::Unary(l)
                }
                TypeInner::Either(l, r) => Tree::Binary(l, r),
                TypeInner::Tuple(elements) => {
                    Tree::Nary(elements.iter().map(Arc::as_ref).collect())
                }
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
