use std::num::NonZeroUsize;
use std::sync::Arc;

use simplicity::node::{CoreConstructible, JetConstructible};

use super::ProgNode;
use crate::array::btree_split_index;
use crate::ast::JetHinter;
use crate::jet::JetHL;
use crate::named::CoreExt;
use crate::types::UIntType;

#[derive(Clone, Debug, Eq, Hash)]
#[allow(clippy::derived_hash_with_manual_eq)]
pub struct RawHashJets {
    init: Box<dyn JetHL>,
    adds: Arc<[Box<dyn JetHL>]>,
    finalize: Box<dyn JetHL>,
}

// Manually implemented because the 1.74 (MSRV) derive expands to a body that
// moves out of the non-Copy `Box<dyn JetHL>` fields, later rustc versions are fine.
impl PartialEq for RawHashJets {
    fn eq(&self, other: &Self) -> bool {
        self.init.eq(&other.init) && self.adds == other.adds && self.finalize.eq(&other.finalize)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum RawHashJetsError {
    UnsupportedWidth(UIntType),
    Unavailable,
}

impl RawHashJets {
    /// Construct the jets for hashing a tuple whose elements have the given types.
    pub fn new(
        hinter: &dyn JetHinter,
        widths: impl IntoIterator<Item = UIntType>,
    ) -> Result<Self, RawHashJetsError> {
        let adds = widths
            .into_iter()
            .map(|width| {
                let construct = match width {
                    UIntType::U1 | UIntType::U2 | UIntType::U4 => {
                        return Err(RawHashJetsError::UnsupportedWidth(width))
                    }
                    UIntType::U8 => JetHinter::construct_sha_256_ctx_8_add_1,
                    UIntType::U16 => JetHinter::construct_sha_256_ctx_8_add_2,
                    UIntType::U32 => JetHinter::construct_sha_256_ctx_8_add_4,
                    UIntType::U64 => JetHinter::construct_sha_256_ctx_8_add_8,
                    UIntType::U128 => JetHinter::construct_sha_256_ctx_8_add_16,
                    UIntType::U256 => JetHinter::construct_sha_256_ctx_8_add_32,
                };
                construct(hinter).ok_or(RawHashJetsError::Unavailable)
            })
            .collect::<Result<Arc<[Box<dyn JetHL>]>, RawHashJetsError>>()?;

        let init = hinter
            .construct_sha_256_ctx_8_init()
            .ok_or(RawHashJetsError::Unavailable)?;
        let finalize = hinter
            .construct_sha_256_ctx_8_finalize()
            .ok_or(RawHashJetsError::Unavailable)?;

        Ok(Self {
            init,
            adds,
            finalize,
        })
    }
}

/// Hash a tuple of integers with SHA-256.
///
/// `jets.adds[i]` is the `sha_256_ctx_8_add_N` jet for the `i`-th tuple element.
///
/// The recursion follows the tuple layout of [`BTreeSlice`](crate::array::BTreeSlice),
/// so the element order is the source order.
pub fn raw_hash<'brand>(
    ctx: &simplicity::types::Context<'brand>,
    jets: &RawHashJets,
) -> Result<ProgNode<'brand>, simplicity::types::Error> {
    /// Add the elements of a (sub)tuple to a context.
    ///
    /// The resulting program has type `Ctx8 × T → Ctx8`.
    fn add_tuple<'brand>(
        ctx: &simplicity::types::Context<'brand>,
        add_jets: &[Box<dyn JetHL>],
    ) -> Result<ProgNode<'brand>, simplicity::types::Error> {
        match add_jets {
            // Nothing to add: return the context unchanged.
            [] => Ok(ProgNode::o().h(ctx).build()),
            [jet] => Ok(ProgNode::jet(ctx, jet.as_jet())),
            _ => {
                // A tuple is a balanced binary tree, like arrays; see `BTreeSlice`.
                // The input is (ctx, (L, R)). Add L first, then R.
                let (left_jets, right_jets) = add_jets.split_at(btree_split_index(add_jets.len()));
                let add_left = add_tuple(ctx, left_jets)?;
                let add_right = add_tuple(ctx, right_jets)?;

                let hash_ctx = ProgNode::o().h(ctx);
                let left = ProgNode::i().o().h(ctx);
                let right = ProgNode::i().i().h(ctx);
                let left_ctx = hash_ctx.pair(left).comp(&add_left)?;
                let right_ctx = left_ctx.pair(right).comp(&add_right)?;
                Ok(right_ctx.build())
            }
        }
    }

    let init = ProgNode::comp(
        &ProgNode::unit(ctx),
        &ProgNode::jet(ctx, jets.init.as_jet()),
    )?;
    let ctx_and_input = ProgNode::pair(&init, &ProgNode::iden(ctx))?;
    let absorbed = ProgNode::comp(&ctx_and_input, &add_tuple(ctx, &jets.adds)?)?;
    ProgNode::comp(&absorbed, &ProgNode::jet(ctx, jets.finalize.as_jet()))
}

/// Fold an array of size `size` elements using function `f`.
///
/// Function `f: E × A → A`
/// takes an array element of type `E` and an accumulator of type `A`,
/// and it produces an updated accumulator of type `A`.
///
/// The fold `(fold f)_n : E^n × A → A`
/// takes the array of type `E^n` and an initial accumulator of type `A`,
/// and it produces the final accumulator of type `A`.
pub fn array_fold<'brand>(
    size: NonZeroUsize,
    f: &ProgNode<'brand>,
) -> Result<ProgNode<'brand>, simplicity::types::Error> {
    /// Recursively fold the array using the precomputed folding functions.
    fn tree_fold<'brand>(
        n: usize,
        f_powers_of_two: &[ProgNode<'brand>],
    ) -> Result<ProgNode<'brand>, simplicity::types::Error> {
        // Array is a left-balanced (right-associative) binary tree.
        let max_pow2 = n.ilog2() as usize;
        debug_assert!(max_pow2 < f_powers_of_two.len());
        let f_right = &f_powers_of_two[max_pow2];

        // If the tree is balanced, return precomputed solution.
        let size_right = 1 << max_pow2;
        if n == size_right {
            return Ok(Arc::clone(f_right));
        }
        debug_assert!(size_right < n);

        let f_left = tree_fold(n - size_right, f_powers_of_two)?;
        f_array_fold(&f_left, f_right)
    }

    /// Fold the two arrays applying the folding function sequentially left -> right.
    fn f_array_fold<'brand>(
        f_left: &ProgNode<'brand>,
        f_right: &ProgNode<'brand>,
    ) -> Result<ProgNode<'brand>, simplicity::types::Error> {
        // The input is a tuple ((L, R), acc): ([E; n], A) where:
        // - L and R are arrays of varying size E^x and E^y respectively (x + y = n).
        // - acc is an accumulator of type A.
        let ctx = f_left.inference_context();
        let left_arr = ProgNode::o().o().h(ctx);
        let right_arr = ProgNode::o().i().h(ctx);
        let acc = ProgNode::i().h(ctx);
        let left_res = left_arr.pair(acc).comp(f_left)?;
        let right_res = right_arr.pair(left_res).comp(f_right)?;
        Ok(right_res.build())
    }

    // Precompute the folding functions for arrays of size 2^i where i < n.
    let n = size.get();
    let mut f_powers_of_two: Vec<ProgNode> = Vec::with_capacity(1 + n.ilog2() as usize);

    // An array of size 1 is just the element itself, so f_array_fold_1 is the same as the folding function.
    let mut f_prev = f.clone();
    f_powers_of_two.push(f_prev.clone());

    let mut i = 1;
    while i < n {
        f_prev = f_array_fold(&f_prev, &f_prev)?;
        f_powers_of_two.push(Arc::clone(&f_prev));
        i *= 2;
    }

    tree_fold(n, &f_powers_of_two)
}

#[cfg(test)]
mod tests {
    use crate::{tests::TestCase, WitnessValues};

    #[test]
    fn array_fold() {
        TestCase::program_file("./examples/array_fold.simf")
            .with_witness_values(WitnessValues::default())
            .assert_run_success();
    }
}
