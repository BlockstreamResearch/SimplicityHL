use crate::num::NonZeroPow2Usize;
use miniscript::iter::{Tree, TreeLike};

/// View of a slice as a balanced binary tree.
///
/// Each node is labelled with a slice.
/// Leaves contain single elements.
///
/// The tree is right-associative:
/// `&[a b c]` becomes `&[a] (&[b] &[c])`.
///
/// The tree is empty if the slice is empty.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct BTreeSlice<'a, A>(&'a [A]);

impl<'a, A> BTreeSlice<'a, A> {
    /// View the slice as a balanced binary tree.
    pub fn from_slice(slice: &'a [A]) -> Self {
        Self(slice)
    }
}

impl<A: Clone> BTreeSlice<'_, A> {
    /// Fold the tree in post order, using the binary function `f`.
    ///
    /// Returns `None` if the tree is empty.
    ///
    /// ## See
    ///
    /// Opposite of [`Unfolder::unfold`].
    pub fn fold<F>(self, f: F) -> Option<A>
    where
        F: Fn(A, A) -> A,
    {
        if self.0.is_empty() {
            return None;
        }

        let mut output = vec![];
        for item in self.post_order_iter() {
            match item.child_indices.len() {
                2 => {
                    let r = output.pop().unwrap();
                    let l = output.pop().unwrap();
                    output.push(f(l, r));
                }
                n => {
                    debug_assert_eq!(n, 0);
                    debug_assert_eq!(item.node.0.len(), 1);
                    output.push(item.node.0[0].clone());
                }
            }
        }

        debug_assert_eq!(output.len(), 1);
        output.pop()
    }
}

/// Index at which [`BTreeSlice`] splits a slice of length `n` into a left
/// and a right subtree.
///
/// Exposed so that consumers which need to *navigate* the balanced tree.
///
/// ## Panics
///
/// `n` must be at least 2.
pub fn btree_split_index(n: usize) -> usize {
    debug_assert!(2 <= n);
    let next_pow2 = n.next_power_of_two();
    debug_assert!(0 < next_pow2 / 2);
    debug_assert!(0 < n - next_pow2 / 2);
    n - next_pow2 / 2
}

impl<A: Clone> TreeLike for BTreeSlice<'_, A> {
    fn as_node(&self) -> Tree<Self> {
        match self.0.len() {
            0 | 1 => Tree::Nullary,
            n => {
                let half = btree_split_index(n);
                let left = BTreeSlice::from_slice(&self.0[..half]);
                let right = BTreeSlice::from_slice(&self.0[half..]);
                Tree::Binary(left, right)
            }
        }
    }
}

/// Helper struct to unfold a tree into a list of leaves.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Unfolder<A> {
    tree: A,
    n: usize,
}

impl<A: Clone> Unfolder<A> {
    /// Create an unfolder to yield `n` leaves of the given `tree`.
    pub fn new(tree: A, n: usize) -> Self {
        Self { tree, n }
    }

    /// Unfold the tree into `n` leaves using function `f`.
    ///
    /// Function `f` tries to split a tree node into two children.
    /// `f` returns `None` when it is called on a leaf node.
    ///
    /// The unfold function returns `None` if any tree node could not be split.
    /// This means that the tree had fewer than `n` leaves.
    ///
    /// ## See
    ///
    /// Opposite of [`BTreeSlice::fold`].
    pub fn unfold<F>(self, f: F) -> Option<Vec<A>>
    where
        F: Fn(A) -> Option<(A, A)>,
    {
        let n = self.n;
        let mut stack = vec![self];
        let mut output = Vec::with_capacity(n);
        while let Some(top) = stack.pop() {
            match top.n {
                0 => continue,
                1 => output.push(top.tree),
                _ => {
                    let (left, right) = f(top.tree.clone())?;
                    let next_pow2 = top.n.next_power_of_two();
                    let half = top.n - next_pow2 / 2;
                    stack.push(Self::new(right, top.n.saturating_sub(half)));
                    stack.push(Self::new(left, half));
                }
            }
        }

        debug_assert_eq!(output.len(), n);
        Some(output)
    }
}

/// Partition of a slice into blocks of (lengths of) powers of two.
///
/// ## Partition of less than 2^(n + 1) elements
///
/// ```text
///               .
///              / \
/// [block of 2^n] [partition of <2^n]
/// ```
///
/// ## Partition of less than 2^1 elements
///
/// ```text
/// [block of 2^0]
/// ```
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum Partition<'a, A> {
    Leaf {
        slice: &'a [A],
        size: usize,
    },
    Parent {
        slice: &'a [A],
        bound: NonZeroPow2Usize,
    },
}

impl<'a, A> Partition<'a, A> {
    /// Partition a `slice` of less than `bound` many elements.
    ///
    /// ## Panics
    ///
    /// The `slice` has `bound` many elements or more.
    pub fn from_slice(slice: &'a [A], bound: NonZeroPow2Usize) -> Self {
        assert!(
            slice.len() < bound.get(),
            "The slice must be shorter than the given bound"
        );
        match bound {
            NonZeroPow2Usize::TWO => Self::Leaf { slice, size: 1 },
            _ => Self::Parent { slice, bound },
        }
    }
}

impl<A: Clone> Partition<'_, A> {
    /// Check if the partition is complete.
    ///
    /// A complete partition contains no empty blocks.
    pub fn is_complete(&self) -> bool {
        match self {
            Partition::Leaf { slice, size } => slice.len() == *size,
            Partition::Parent { slice, bound } => slice.len() + 1 == bound.get(),
        }
    }

    /// Fold the tree of blocks in post-order.
    ///
    /// Function `f` converts a slice of elements into a block of the given size.
    /// `f` produces a filled block if the slice has block-size many elements.
    /// `f` produces an empty block if the slice is empty. Other cases are impossible.
    ///
    /// Function `g` combines a block (left child) and a partition (right child)
    /// into a larger partition.
    pub fn fold<B, F, G>(self, f: F, g: G) -> B
    where
        F: Fn(&[A], usize) -> B,
        G: Fn(B, B) -> B,
    {
        let mut output = vec![];
        for item in self.post_order_iter() {
            match item.node {
                Partition::Leaf { slice, size } => {
                    output.push(f(slice, size));
                }
                Partition::Parent { .. } => {
                    let r = output.pop().unwrap();
                    let l = output.pop().unwrap();
                    output.push(g(l, r));
                }
            }
        }

        debug_assert_eq!(output.len(), 1);
        output.pop().unwrap()
    }
}

#[rustfmt::skip]
impl<A: Clone> TreeLike for Partition<'_, A> {
    fn as_node(&self) -> Tree<Self> {
        match self {
            Self::Leaf {..} => Tree::Nullary,
            Self::Parent { slice, bound } => {
                debug_assert!(NonZeroPow2Usize::TWO < *bound);
                let smaller_bound = bound.checked_div2().unwrap();

                let (l, r) = if slice.len() < smaller_bound.get() {
                    (
                        Self::Leaf { slice: &[], size: smaller_bound.get() },
                        Self::from_slice(slice, smaller_bound),
                    )
                } else {
                    (
                        Self::Leaf { slice: &slice[..smaller_bound.get()], size: smaller_bound.get() },
                        Self::from_slice(&slice[smaller_bound.get()..], smaller_bound),
                    )
                };
                Tree::Binary(l, r)
            }
        }
    }
}

/// Helper struct to combine elements of a partition.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Combiner<A> {
    partition: A,
    bound: NonZeroPow2Usize,
}

impl<A: Clone> Combiner<A> {
    /// Create a combiner for the given `partition` of less than `bound` many elements.
    pub fn new(partition: A, bound: NonZeroPow2Usize) -> Self {
        Self { partition, bound }
    }

    /// Unfold the partition into a list of its elements.
    ///
    /// Function `f` takes a block and its size and tries extract the block's elements.
    /// `f` returns `None` if the input is not a block.
    ///
    /// Function `g` splits a partition into a block (left child)
    /// and a smaller partition (right child).
    /// `g` returns `None` if the partition cannot be split.
    ///
    /// The combine function returns `None` if the input was not a partition with the given bound.
    ///
    /// ## See
    ///
    /// Opposite of [`Partition::fold`].
    pub fn unfold<F, G, B>(self, f: F, g: G) -> Option<Vec<B>>
    where
        F: Fn(A, usize) -> Option<Vec<B>>,
        G: Fn(A) -> Option<(A, A)>,
    {
        let mut next = Some(self);
        let mut output = vec![];

        while let Some(top) = next.take() {
            match top.bound.checked_div2() {
                Some(smaller_bound) => {
                    let (block, partition) = g(top.partition)?;
                    let elements = f(block, smaller_bound.get())?;
                    debug_assert!(elements.is_empty() || elements.len() == smaller_bound.get());
                    output.extend(elements);
                    next = Some(Combiner::new(partition, smaller_bound));
                }
                None => {
                    let elements = f(top.partition, 1)?;
                    debug_assert!(elements.is_empty() || elements.len() == 1);
                    output.extend(elements);
                }
            }
        }

        Some(output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pattern::{BasePattern, Pattern};
    use crate::str::Identifier;

    #[derive(Debug, Clone, PartialEq, Eq)]
    enum Tree {
        Leaf(u16),
        Product(Box<Self>, Box<Self>),
        Array(Box<[Self]>),
    }

    impl Tree {
        fn product(left: Self, right: Self) -> Self {
            Self::Product(Box::new(left), Box::new(right))
        }

        fn array<I: IntoIterator<Item = Self>>(iter: I) -> Self {
            Self::Array(iter.into_iter().collect())
        }

        fn as_product(&self) -> Option<(&Self, &Self)> {
            match self {
                Self::Product(left, right) => Some((left, right)),
                _ => None,
            }
        }

        fn as_array(&self) -> Option<&[Self]> {
            match self {
                Self::Array(elements) => Some(elements.as_ref()),
                _ => None,
            }
        }
    }

    #[test]
    #[rustfmt::skip]
    fn fold_btree_slice() {
        let slice_output: [(&[&str], &str); 9] = [
            (&[], ""),
            (&["a"], "a"),
            (&["a", "b"], "(ab)"),
            (&["a", "b", "c"], "(a(bc))"),
            (&["a", "b", "c", "d"], "((ab)(cd))"),
            (&["a", "b", "c", "d", "e"], "(a((bc)(de)))"),
            (&["a", "b", "c", "d", "e", "f"], "((ab)((cd)(ef)))"),
            (&["a", "b", "c", "d", "e", "f", "g"], "((a(bc))((de)(fg)))"),
            (&["a", "b", "c", "d", "e", "f", "g", "h"], "(((ab)(cd))((ef)(gh)))"),
        ];
        let concat = |a: String, b: String| format!("({a}{b})");

        for (slice, expected_output) in slice_output {
            let vector: Vec<_> = slice.iter().map(|s| s.to_string()).collect();
            let tree = BTreeSlice::from_slice(&vector);
            let output = tree.fold(concat).unwrap_or_default();
            assert_eq!(&output, expected_output);
        }
    }

    #[test]
    fn unfold_btree_slice() {
        let elements = (0..255).map(Tree::Leaf).collect::<Vec<Tree>>();

        for n in 0..255 {
            let slice = &elements[0..n];
            let folded = BTreeSlice::from_slice(slice)
                .fold(Tree::product)
                .unwrap_or(Tree::Leaf(1337));
            let unfolded = Unfolder::new(&folded, n).unfold(Tree::as_product).unwrap();
            assert_eq!(unfolded.len(), n);
            for i in 0..n {
                assert_eq!(&slice[i], unfolded[i]);
            }
        }
    }

    #[test]
    #[rustfmt::skip]
    fn fold_partition() {
        let slice_len_output: [(&[&str], usize, &str); 14] = [
            (&[], 2, ""),
            (&["a"], 2, "a"),
            (&[], 4, "(:)"),
            (&["a"], 4, "(:a)"),
            (&["a", "b"], 4, "(ab:)"),
            (&["a", "b", "c"], 4, "(ab:c)"),
            (&[], 8, "(:(:))"),
            (&["a"], 8, "(:(:a))"),
            (&["a", "b"], 8, "(:(ab:))"),
            (&["a", "b", "c"], 8, "(:(ab:c))"),
            (&["a", "b", "c", "d"], 8, "(abcd:(:))"),
            (&["a", "b", "c", "d", "e"], 8, "(abcd:(:e))"),
            (&["a", "b", "c", "d", "e", "f"], 8, "(abcd:(ef:))"),
            (&["a", "b", "c", "d", "e", "f", "g"], 8, "(abcd:(ef:g))"),
        ];
        let process = |block: &[String], _| block.join("");
        let join = |a: String, b: String| format!("({a}:{b})");

        for (slice, bound, expected_output) in slice_len_output {
            let vector: Vec<_> = slice.iter().map(|s| s.to_string()).collect();
            let partition = Partition::from_slice(&vector, NonZeroPow2Usize::new_unchecked(bound));
            let output = partition.fold(process, join);
            assert_eq!(&output, expected_output);
        }
    }

    #[test]
    fn unfold_partition() {
        let elements = (0..255).map(Tree::Leaf).collect::<Vec<Tree>>();
        let bound = NonZeroPow2Usize::new_unchecked(256);
        let pack_block = |block: &[Tree], _size: usize| Tree::array(block.iter().cloned());
        let unpack_block = |block: &Tree, _size: usize| block.as_array().map(<[Tree]>::to_vec);

        for n in 0..255 {
            let slice = &elements[0..n];
            let folded = Partition::from_slice(slice, bound).fold(pack_block, Tree::product);
            let unfolded = Combiner::new(&folded, bound)
                .unfold(unpack_block, Tree::as_product)
                .unwrap();
            assert_eq!(unfolded.len(), n);
            for i in 0..n {
                assert_eq!(slice[i], unfolded[i]);
            }
        }
    }

    #[test]
    fn base_pattern() {
        let a = Pattern::Identifier(Identifier::from_str_unchecked("a"));
        let b = Pattern::Identifier(Identifier::from_str_unchecked("b"));
        let c = Pattern::Identifier(Identifier::from_str_unchecked("c"));
        let d = Pattern::Identifier(Identifier::from_str_unchecked("d"));
        let a_ = BasePattern::Identifier(Identifier::from_str_unchecked("a"));
        let b_ = BasePattern::Identifier(Identifier::from_str_unchecked("b"));
        let c_ = BasePattern::Identifier(Identifier::from_str_unchecked("c"));
        let d_ = BasePattern::Identifier(Identifier::from_str_unchecked("d"));

        let pattern_string = [
            // a = a
            (a.clone(), a_.clone()),
            // (a, b) = (a, b)
            (
                Pattern::product(a.clone(), b.clone()),
                BasePattern::product(a_.clone(), b_.clone()),
            ),
            // [a] = a
            (Pattern::array([a.clone()]), a_.clone()),
            // [[a]] = a
            (Pattern::array([Pattern::array([a.clone()])]), a_.clone()),
            // [a b] = (a, b)
            (
                Pattern::array([a.clone(), b.clone()]),
                BasePattern::product(a_.clone(), b_.clone()),
            ),
            // [a b c] = (a, (b, c))
            (
                Pattern::array([a.clone(), b.clone(), c.clone()]),
                BasePattern::product(a_.clone(), BasePattern::product(b_.clone(), c_.clone())),
            ),
            // [[a, b], [c, d]] = ((a, b), (c, d))
            (
                Pattern::array([
                    Pattern::array([a.clone(), b.clone()]),
                    Pattern::array([c.clone(), d.clone()]),
                ]),
                BasePattern::product(BasePattern::product(a_, b_), BasePattern::product(c_, d_)),
            ),
        ];

        for (pattern, expected_base_pattern) in pattern_string {
            let base_pattern = BasePattern::from(&pattern);
            assert_eq!(expected_base_pattern, base_pattern);
        }
    }
}
