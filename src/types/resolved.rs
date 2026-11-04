use core::fmt;
use core::hash::{Hash, Hasher};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use miniscript::iter::{Tree, TreeLike};

use super::{
    EnumInfo, StructuralType, TypeConstructible, TypeDeconstructible, TypeInner, UIntType,
};
use crate::{num::NonZeroPow2Usize, types::BuiltinAlias};

/// SimplicityHL type without type aliases.
#[derive(Clone)]
pub struct ResolvedType {
    inner: TypeInner<Arc<Self>>,
    flags: TypeFlags,
    builtin: Option<BuiltinAlias>,
}

/// The builtin alias is metadata for tooling, not part of the type,
/// so `Pubkey` and `u256` stay interchangeable.
impl PartialEq for ResolvedType {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner && self.flags == other.flags
    }
}

impl Eq for ResolvedType {}

impl Hash for ResolvedType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.inner.hash(state);
        self.flags.hash(state);
    }
}

/// Facts about a type, computed once from its parts when the type is built.
///
/// We need these cached flags because searching a [`TypeInner::Never`], including inside
/// enum payloads, can take exponential time on types built from shared aliases.
#[derive(PartialEq, Eq, Hash, Clone, Copy, Default)]
struct TypeFlags {
    has_enum: bool,
    has_never: bool,
    has_never_in_enum: bool,
}

impl TypeFlags {
    const fn union(self, other: Self) -> Self {
        Self {
            has_enum: self.has_enum || other.has_enum,
            has_never: self.has_never || other.has_never,
            has_never_in_enum: self.has_never_in_enum || other.has_never_in_enum,
        }
    }
}

impl ResolvedType {
    fn new(inner: TypeInner<Arc<Self>>) -> Self {
        let flags = match &inner {
            TypeInner::Boolean | TypeInner::UInt(_) => TypeFlags::default(),
            TypeInner::Never => Self::never().flags,
            TypeInner::Enum(info) => TypeFlags {
                has_enum: true,
                has_never: false,
                has_never_in_enum: info
                    .variants()
                    .iter()
                    .any(|variant| !variant.payload_type().has_structural_type()),
            },
            TypeInner::Option(inner) | TypeInner::Array(inner, _) | TypeInner::List(inner, _) => {
                inner.flags
            }
            TypeInner::Either(left, right) => left.flags.union(right.flags),
            TypeInner::Tuple(elements) => elements
                .iter()
                .fold(TypeFlags::default(), |flags, element| {
                    flags.union(element.flags)
                }),
        };

        Self {
            inner,
            flags,
            builtin: None,
        }
    }

    /// Access the inner type primitive.
    pub fn as_inner(&self) -> &TypeInner<Arc<Self>> {
        &self.inner
    }

    /// Access the builtin alias that this type was resolved from, such as `Pubkey` or `Fe`.
    pub const fn builtin_alias(&self) -> Option<BuiltinAlias> {
        self.builtin
    }

    pub(crate) fn with_builtin_alias(mut self, alias: BuiltinAlias) -> Self {
        self.builtin = Some(alias);
        self
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
        Self::new(TypeInner::Enum(info))
    }

    /// Access the enum definition if this is an enum type.
    pub const fn as_enum(&self) -> Option<&EnumInfo> {
        match &self.inner {
            TypeInner::Enum(info) => Some(info),
            _ => None,
        }
    }

    /// Check whether the type mentions an enum, at any nesting depth.
    pub const fn contains_enum(&self) -> bool {
        self.flags.has_enum
    }
}

/// The uninhabited type.
impl ResolvedType {
    /// Create the uninhabited type.
    pub const fn never() -> Self {
        Self {
            inner: TypeInner::Never,
            flags: TypeFlags {
                has_enum: false,
                has_never: true,
                has_never_in_enum: false,
            },
            builtin: None,
        }
    }

    /// Check whether this is the uninhabited type.
    pub const fn is_never(&self) -> bool {
        matches!(self.inner, TypeInner::Never)
    }

    /// Check whether the type mentions the uninhabited type, except inside enum payloads,
    /// because an enum is identified by its name.
    pub const fn contains_never(&self) -> bool {
        self.flags.has_never
    }

    /// Check whether the type can be lowered to a structural type.
    ///
    /// Use this before [`StructuralType::from`], which panics on `!`. Unlike
    /// [`Self::contains_never`], this looks inside enum payloads.
    pub const fn has_structural_type(&self) -> bool {
        !self.flags.has_never && !self.flags.has_never_in_enum
    }

    /// Check whether the types are equal, where a type that mentions `!` is equal to every type.
    pub(crate) fn compatible(&self, other: &Self) -> bool {
        self.contains_never() || other.contains_never() || self.same_as(other)
    }

    /// Check whether the types are equal, like `==` but without walking shared parts as trees.
    ///
    /// Use this instead of `==`, which takes exponential time on equal types
    /// built from different aliases
    pub(crate) fn same_as(&self, other: &Self) -> bool {
        self.matches_with(other, |one, two| {
            matches!(
                one.inner,
                TypeInner::Boolean | TypeInner::UInt(_) | TypeInner::Enum(_) | TypeInner::Never
            ) && one == two
        })
    }

    /// Check whether the types match, using `leaves_match` for their leaves.
    ///
    /// Shared by [`Self::same_as`] and the enum check of casts.
    pub(crate) fn matches_with(
        &self,
        other: &Self,
        mut leaves_match: impl FnMut(&Self, &Self) -> bool,
    ) -> bool {
        let mut seen = HashSet::new();
        let mut stack = vec![(self, other)];

        while let Some((one, two)) = stack.pop() {
            if std::ptr::eq(one, two)
                || !seen.insert((std::ptr::from_ref(one), std::ptr::from_ref(two)))
            {
                continue;
            }

            match (&one.inner, &two.inner) {
                (TypeInner::Either(l1, r1), TypeInner::Either(l2, r2)) => {
                    stack.extend([(l1.as_ref(), l2.as_ref()), (r1.as_ref(), r2.as_ref())]);
                }
                (TypeInner::Option(i1), TypeInner::Option(i2)) => {
                    stack.push((i1.as_ref(), i2.as_ref()))
                }
                (TypeInner::Tuple(e1), TypeInner::Tuple(e2)) if Arc::ptr_eq(e1, e2) => {}
                (TypeInner::Tuple(e1), TypeInner::Tuple(e2)) if e1.len() == e2.len() => {
                    stack.extend(e1.iter().map(Arc::as_ref).zip(e2.iter().map(Arc::as_ref)));
                }
                (TypeInner::Array(i1, n1), TypeInner::Array(i2, n2)) if n1 == n2 => {
                    stack.push((i1.as_ref(), i2.as_ref()));
                }
                (TypeInner::List(i1, b1), TypeInner::List(i2, b2)) if b1 == b2 => {
                    stack.push((i1.as_ref(), i2.as_ref()));
                }
                _ if leaves_match(one, two) => {}
                _ => return false,
            }
        }

        true
    }
}

impl TypeConstructible for ResolvedType {
    fn either(left: Self, right: Self) -> Self {
        Self::new(TypeInner::Either(Arc::new(left), Arc::new(right)))
    }

    fn option(inner: Self) -> Self {
        Self::new(TypeInner::Option(Arc::new(inner)))
    }

    fn boolean() -> Self {
        Self::new(TypeInner::Boolean)
    }

    fn tuple<I: IntoIterator<Item = Self>>(elements: I) -> Self {
        Self::new(TypeInner::Tuple(
            elements.into_iter().map(Arc::new).collect(),
        ))
    }

    fn array(element: Self, size: usize) -> Self {
        Self::new(TypeInner::Array(Arc::new(element), size))
    }

    fn list(element: Self, bound: NonZeroPow2Usize) -> Self {
        Self::new(TypeInner::List(Arc::new(element), bound))
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
        match &self.inner {
            TypeInner::Boolean | TypeInner::UInt(..) | TypeInner::Enum(..) | TypeInner::Never => {
                Tree::Nullary
            }
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
            data.node.inner.display(f, data.n_children_yielded)?;
        }
        Ok(())
    }
}

impl From<UIntType> for ResolvedType {
    fn from(value: UIntType) -> Self {
        Self::new(TypeInner::UInt(value))
    }
}

#[cfg(feature = "arbitrary")]
impl crate::ArbitraryRec for ResolvedType {
    // Deliberately never generates `TypeInner::Never`, which has no values.
    //
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

/// ## Panics
///
/// Panics if the type mentions [`TypeInner::Never`].
impl From<&ResolvedType> for StructuralType {
    fn from(value: &ResolvedType) -> Self {
        let mut output = vec![];
        // Keep the traversal iterative, but visit shared subtypes only once.
        // Structural hashing would itself expand aliases, so key by address.
        // Every key points into `value`, which stays alive for this conversion.
        let mut lowered = HashMap::<*const ResolvedType, StructuralType>::new();
        let mut stack = vec![(value, false)];
        while let Some((ty, children_visited)) = stack.pop() {
            let key = std::ptr::from_ref(ty);
            if !children_visited {
                if let Some(structural) = lowered.get(&key) {
                    output.push(structural.clone());
                    continue;
                }

                stack.push((ty, true));
                match &ty.inner {
                    TypeInner::Either(left, right) => {
                        stack.extend([(right.as_ref(), false), (left.as_ref(), false)]);
                    }
                    TypeInner::Option(inner)
                    | TypeInner::Array(inner, _)
                    | TypeInner::List(inner, _) => stack.push((inner.as_ref(), false)),
                    TypeInner::Tuple(elements) => {
                        stack.extend(elements.iter().rev().map(|el| (el.as_ref(), false)));
                    }
                    TypeInner::Enum(info) => {
                        stack.extend(
                            info.variants()
                                .iter()
                                .rev()
                                .map(|variant| (variant.payload_type(), false)),
                        );
                    }
                    TypeInner::Boolean | TypeInner::UInt(_) | TypeInner::Never => {}
                }
                continue;
            }

            match &ty.inner {
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
                TypeInner::Tuple(elements) => {
                    let size = elements.len();
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
                    // Reuse payloads lowered through this traversal's shared cache.
                    let variants = output.split_off(output.len() - info.variants().len());
                    output.push(StructuralType::balanced_sum(variants));
                }
                TypeInner::Never => {
                    panic!(
                        "the never type has no structural type; check `is_never` before lowering"
                    )
                }
            }
            // Cache the completed result for later visits to the same node.
            lowered.insert(key, output.last().unwrap().clone());
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
