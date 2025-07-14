use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::Arc;

use miniscript::iter::{Tree, TreeLike};

use crate::array::BTreeSlice;
use crate::error::Error;
use crate::named::{PairBuilder, SelectorBuilder};
use crate::str::Identifier;
use crate::types::{ResolvedType, TypeInner};
use crate::ProgNode;

/// Pattern for binding values to variables.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Pattern {
    /// Match any value and bind it to variable name.
    Identifier(Identifier),
    /// Match any value but ignore it.
    Ignore,
    /// Recursively match the components of a tuple value
    Tuple(Arc<[Self]>),
    /// Recursively match the elements of an array value.
    Array(Arc<[Self]>),
}

impl Pattern {
    /// Construct a product pattern.
    pub fn product(l: Self, r: Self) -> Self {
        Self::tuple([l, r])
    }

    /// Construct a tuple pattern.
    pub fn tuple<I: IntoIterator<Item = Self>>(elements: I) -> Self {
        Self::Tuple(elements.into_iter().collect())
    }

    /// Construct an array pattern.
    pub fn array<I: IntoIterator<Item = Self>>(elements: I) -> Self {
        Self::Array(elements.into_iter().collect())
    }

    /// Check if the pattern matches the given type.
    ///
    /// Return a map of bound variable identifiers to their assigned type.
    pub fn is_of_type(
        &self,
        ty: &ResolvedType,
    ) -> Result<HashMap<Identifier, ResolvedType>, Error> {
        let mut stack = vec![(self, ty)];
        let mut output = HashMap::new();
        while let Some((pattern, ty)) = stack.pop() {
            match (pattern, ty.as_inner()) {
                (Pattern::Identifier(i), _) => match output.entry(i.clone()) {
                    Entry::Occupied(..) => return Err(Error::VariableReuseInPattern(i.clone())),
                    Entry::Vacant(entry) => {
                        entry.insert(ty.clone());
                    }
                },
                (Pattern::Ignore, _) => {}
                (Pattern::Tuple(pats), TypeInner::Tuple(types)) => {
                    stack.extend(pats.iter().zip(types.iter().map(Arc::as_ref)));
                }
                (Pattern::Array(pats), TypeInner::Array(ty, size)) if pats.len() == *size => {
                    stack.extend(pats.iter().zip(std::iter::repeat(ty.as_ref())));
                }
                _ => return Err(Error::ExpressionUnexpectedType(ty.clone())),
            }
        }
        Ok(output)
    }
}

impl TreeLike for &Pattern {
    fn as_node(&self) -> Tree<Self> {
        match self {
            Pattern::Identifier(_) | Pattern::Ignore => Tree::Nullary,
            Pattern::Tuple(elements) | Pattern::Array(elements) => {
                Tree::Nary(elements.iter().collect())
            }
        }
    }
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for data in self.verbose_pre_order_iter() {
            match data.node {
                Pattern::Identifier(i) => write!(f, "{i}")?,
                Pattern::Ignore => write!(f, "_")?,
                Pattern::Tuple(tuple) => {
                    if data.n_children_yielded == 0 {
                        write!(f, "(")?;
                    } else if !data.is_complete || tuple.len() == 1 {
                        write!(f, ", ")?;
                    }
                    if data.is_complete {
                        write!(f, ")")?;
                    }
                }
                Pattern::Array(..) => {
                    if data.n_children_yielded == 0 {
                        write!(f, "[")?;
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

#[cfg(feature = "arbitrary")]
impl<'a> arbitrary::Arbitrary<'a> for Pattern {
    fn arbitrary(u: &mut arbitrary::Unstructured<'a>) -> arbitrary::Result<Self> {
        <Self as crate::ArbitraryRec>::arbitrary_rec(u, 3)
    }
}

#[cfg(feature = "arbitrary")]
impl crate::ArbitraryRec for Pattern {
    fn arbitrary_rec(u: &mut arbitrary::Unstructured, budget: usize) -> arbitrary::Result<Self> {
        use arbitrary::Arbitrary;

        match budget.checked_sub(1) {
            None => match u.int_in_range(0..=1)? {
                0 => Identifier::arbitrary(u).map(Self::Identifier),
                1 => Ok(Self::Ignore),
                _ => unreachable!(),
            },
            Some(new_budget) => match u.int_in_range(0..=3)? {
                0 => Identifier::arbitrary(u).map(Self::Identifier),
                1 => Ok(Self::Ignore),
                2 => {
                    let len = u.int_in_range(0..=3)?;
                    (0..len)
                        .map(|_| Self::arbitrary_rec(u, new_budget))
                        .collect::<arbitrary::Result<Arc<[Self]>>>()
                        .map(Self::Tuple)
                }
                3 => {
                    let len = u.int_in_range(0..=3)?;
                    (0..len)
                        .map(|_| Self::arbitrary_rec(u, new_budget))
                        .collect::<arbitrary::Result<Arc<[Self]>>>()
                        .map(Self::Array)
                }
                _ => unreachable!(),
            },
        }
    }
}

/// Basic structure of a SimplicityHL value for pattern matching.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum BasePattern {
    /// Ignore: Match any value.
    ///
    /// Used for matching values that are not assigned to a variable.
    Ignore,
    /// Variable identifier: Match any value and bind it to an identifier.
    Identifier(Identifier),
    /// Product: Match product value component-wise.
    Product(Arc<Self>, Arc<Self>),
}

impl TreeLike for &BasePattern {
    fn as_node(&self) -> Tree<Self> {
        match self {
            BasePattern::Ignore | BasePattern::Identifier(_) => Tree::Nullary,
            BasePattern::Product(l, r) => Tree::Binary(l, r),
        }
    }
}

impl BasePattern {
    /// Construct a product of patterns `left` and `right`.
    pub fn product(left: Self, right: Self) -> Self {
        Self::Product(Arc::new(left), Arc::new(right))
    }

    /// Access the identifier inside an identifier pattern.
    pub fn as_identifier(&self) -> Option<&Identifier> {
        match self {
            Self::Identifier(identifier) => Some(identifier),
            _ => None,
        }
    }

    /// Check if the `identifier` is contained inside the pattern.
    pub fn contains(&self, identifier: &Identifier) -> bool {
        self.get(identifier).is_some()
    }

    /// Compute a Simplicity expression that returns the value of the given `identifier`.
    /// The expression takes as input a value that matches the `self` pattern.
    ///
    /// The expression is a sequence of `take` and `drop` followed by `iden`.
    fn get(&self, identifier: &Identifier) -> Option<SelectorBuilder<ProgNode>> {
        let mut selector = SelectorBuilder::default();

        for data in self.verbose_pre_order_iter() {
            match data.node {
                BasePattern::Identifier(id) if id == identifier => return Some(selector),
                BasePattern::Identifier(_) | BasePattern::Ignore => {
                    selector = selector.pop();
                }
                BasePattern::Product(..) => match data.n_children_yielded {
                    0 => selector = selector.o(),
                    1 => selector = selector.i(),
                    n => {
                        debug_assert_eq!(n, 2);
                        selector = selector.pop();
                    }
                },
            }
        }

        None
    }

    /// Check if `self` subsumes the `other` pattern.
    ///
    /// ## Subsumption
    ///
    /// - Ignore: `_` subsumes every pattern.
    /// - Identifier: `a` subsumes `b` iff `a` = `b`
    /// - Product: `(a1, a2)` subsumes `(b1, b2)` iff `a1` subsumes `b1` and `a2` subsumes `b2`.
    ///
    /// ## Matching
    ///
    /// If value `v` matches pattern `p` and pattern `p'` subsumes `p`,
    /// then `v` matches `p'`.
    ///
    /// The subsuming pattern is more general than the subsumed pattern.
    pub fn subsumes(&self, other: &Self) -> bool {
        let mut check_subsumes = vec![(self, other)];

        while let Some((a, b)) = check_subsumes.pop() {
            match (a, b) {
                (BasePattern::Ignore, _) => {}
                (BasePattern::Identifier(a_id), BasePattern::Identifier(b_id)) if a_id == b_id => {}
                (BasePattern::Product(a1, a2), BasePattern::Product(b1, b2)) => {
                    check_subsumes.push((a2, b2));
                    check_subsumes.push((a1, b1));
                }
                _ => return false,
            }
        }

        true
    }

    /// Get an iterator over all identifiers inside the pattern.
    pub fn identifiers(&self) -> impl Iterator<Item = &Identifier> {
        self.pre_order_iter().filter_map(BasePattern::as_identifier)
    }

    /// Check if all `identifiers` are contained inside the pattern.
    pub fn contains_all<'a, I>(&self, mut identifiers: I) -> bool
    where
        I: Iterator<Item = &'a Identifier>,
    {
        let contained_ids = self
            .pre_order_iter()
            .filter_map(BasePattern::as_identifier)
            .collect::<HashSet<&Identifier>>();
        identifiers.all(|id| contained_ids.contains(id))
    }

    /// Check if `self` covers the `other` pattern in terms of variable names.
    ///
    /// ## Coverage
    ///
    /// Pattern `p1` covers pattern `p2` if `p1` contains all variable names from `p2`.
    pub fn covers(&self, other: &Self) -> bool {
        self.contains_all(other.identifiers())
    }

    /// Check if the pattern is the ignore pattern.
    pub fn is_ignore(&self) -> bool {
        matches!(self, BasePattern::Ignore)
    }

    /// Check if the pattern contains an ignore pattern.
    pub fn contains_ignore(&self) -> bool {
        self.pre_order_iter().any(BasePattern::is_ignore)
    }

    /// Compute a Simplicity expression that takes as input a value that matches the `self` pattern
    /// and that produces as output a value that matches the `to` pattern.
    ///
    /// ## Panics
    ///
    /// The `to` pattern contains ignore patterns: Every value matches the ignore pattern.
    /// This means there are infinitely many translating expressions from `self` to `to`.
    /// For instance, `iden`, `iden & iden`, `(iden & iden) & iden`, and so on.
    /// We enforce a unique translation by banning ignore from the `to` pattern.
    pub fn translate(
        &self,
        ctx: &simplicity::types::Context,
        to: &Self,
    ) -> Option<PairBuilder<ProgNode>> {
        #[derive(Debug, Clone)]
        enum Task<'a> {
            Translate(&'a BasePattern, &'a BasePattern),
            MakeTake,
            MakeDrop,
            MakePair,
        }

        assert!(
            !to.contains_ignore(),
            "Ambiguous translation because `to` pattern contains ignore"
        );
        // Every variable in `to` needs a value which is extracted from `from`.
        // If there are variables inside `to` that are not contained in `from`,
        // then there is no translation from `from` to `to`.
        if !self.covers(to) {
            return None;
        }

        let mut stack = vec![Task::Translate(self, to)];
        let mut output = vec![];

        while let Some(task) = stack.pop() {
            match task {
                Task::Translate(from, to) => {
                    debug_assert!(from.covers(to));

                    match to {
                        BasePattern::Ignore => {
                            output.push(PairBuilder::iden(ctx));
                        }
                        BasePattern::Identifier(to_id) => {
                            output.push(from.get(to_id).map(|selector| selector.h(ctx))?);
                        }
                        BasePattern::Product(to_left, to_right) => {
                            if to.subsumes(from) {
                                // Every value that matches `from` also matches `to`.
                                //
                                // `iden` is the smallest expression that translates a value
                                // that matches `from` into a value that matches `to`.
                                //
                                // The translated value is not always minimal with respect to
                                // the pattern `to`. Here, we optimize for the size of the
                                // translating expression and not for the size of the translated
                                // value.
                                output.push(SelectorBuilder::default().h(ctx));
                            } else if let BasePattern::Product(from_left, from_right) = from {
                                if from_right.covers(to) {
                                    stack.push(Task::MakeDrop);
                                    stack.push(Task::Translate(from_right, to));
                                    continue;
                                }
                                if from_left.covers(to) {
                                    stack.push(Task::MakeTake);
                                    stack.push(Task::Translate(from_left, to));
                                    continue;
                                }

                                stack.push(Task::MakePair);

                                if from_right.covers(to_right) {
                                    stack.push(Task::MakeDrop);
                                    stack.push(Task::Translate(from_right, to_right));
                                } else {
                                    stack.push(Task::Translate(from, to_right));
                                }
                                if from_left.covers(to_left) {
                                    stack.push(Task::MakeTake);
                                    stack.push(Task::Translate(from_left, to_left));
                                } else {
                                    stack.push(Task::Translate(from, to_left));
                                }
                            } else {
                                // Patterns contain no identifier duplicates.
                                // The `to` pattern may not contain ignore patterns.
                                // That is why, if the `to` pattern is a product,
                                // then the `from` pattern must also be a product.
                                // Otherwise, the `from` pattern would contain strictly fewer
                                // variables than the `to` pattern, and there would be no
                                // translation from `from` to `to`.
                                unreachable!("The `from` pattern must be a product if the `to` pattern is a product");
                            }
                        }
                    }
                }
                Task::MakeTake => {
                    let translate = output.pop().unwrap();
                    output.push(translate.take());
                }
                Task::MakeDrop => {
                    let translate = output.pop().unwrap();
                    output.push(translate.drop_());
                }
                Task::MakePair => {
                    let translate_right = output.pop().unwrap();
                    let translate_left = output.pop().unwrap();
                    output.push(translate_left.pair(translate_right));
                }
            }
        }

        debug_assert_eq!(output.len(), 1);
        output.pop()
    }
}

impl From<&Pattern> for BasePattern {
    fn from(pattern: &Pattern) -> Self {
        let mut output = vec![];
        for data in pattern.post_order_iter() {
            match data.node {
                Pattern::Identifier(i) => output.push(Self::Identifier(i.clone())),
                Pattern::Ignore => output.push(Self::Ignore),
                Pattern::Tuple(elements) | Pattern::Array(elements) => {
                    let size = elements.len();
                    let elements = &output[output.len() - size..];
                    debug_assert_eq!(elements.len(), size);
                    let tree = BTreeSlice::from_slice(elements);
                    let out = tree.fold(Self::product).unwrap_or(Self::Ignore);
                    output.truncate(output.len() - size);
                    output.push(out);
                }
            }
        }
        debug_assert_eq!(output.len(), 1);
        output.pop().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn translate_pattern() {
        let a = BasePattern::Identifier(Identifier::from_str_unchecked("a"));
        let b = BasePattern::Identifier(Identifier::from_str_unchecked("b"));
        let c = BasePattern::Identifier(Identifier::from_str_unchecked("c"));
        let env = BasePattern::product(BasePattern::product(a.clone(), b.clone()), c.clone());

        let target_expr = [
            (a.clone(), "OOH"),
            (b.clone(), "OIH"),
            (c.clone(), "IH"),
            (BasePattern::product(a.clone(), b.clone()), "OH"),
            (BasePattern::product(a.clone(), c.clone()), "OOH & IH"),
            (BasePattern::product(b.clone(), a.clone()), "take (IH & OH)"),
            (BasePattern::product(b.clone(), c.clone()), "OIH & IH"),
            (BasePattern::product(c.clone(), a.clone()), "IH & OOH"),
            (BasePattern::product(c.clone(), b.clone()), "IH & OIH"),
            (env.clone(), "iden"),
        ];

        for (target, expected_expr) in target_expr {
            let ctx = simplicity::types::Context::new();
            let expr = env.translate(&ctx, &target).unwrap();
            assert_eq!(expected_expr, expr.as_ref().display_expr().to_string());
        }
    }
}
