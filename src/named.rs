use std::sync::Arc;

use simplicity::dag::{InternalSharing, PostOrderIterItem};
use simplicity::jet::Jet;
use simplicity::node::{
    self, Converter, CoreConstructible, Inner, NoDisconnect, NoWitness, Node, WitnessConstructible,
};
use simplicity::Cmr;
use simplicity::{types, FailEntropy};

use crate::str::WitnessName;
use crate::value::StructuralValue;
use crate::witness::WitnessValues;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct WithNames<T>(T);

impl<M: node::Marker> node::Marker for WithNames<M> {
    type CachedData = M::CachedData;
    type Witness = WitnessName;
    // It's quite difficult to wrap M::Disconnect because of Rust's lack of HKTs, and
    // we don't use disconnect in this library right now, so punt on it for now.
    type Disconnect = NoDisconnect;
    type SharingId = M::SharingId;
    type Jet = M::Jet;

    fn compute_sharing_id(cmr: Cmr, cached_data: &Self::CachedData) -> Option<Self::SharingId> {
        M::compute_sharing_id(cmr, cached_data)
    }
}

/// Helper trait so we can abstract over witness and disconnects of any type,
/// as long as we can produce them from a no-witness no-disconnect object.
pub trait Nullable {
    fn none() -> Self;
}

impl<T> Nullable for Option<T> {
    fn none() -> Self {
        None
    }
}

impl Nullable for NoWitness {
    fn none() -> Self {
        NoWitness
    }
}

impl Nullable for NoDisconnect {
    fn none() -> Self {
        NoDisconnect
    }
}

/// [`simplicity::ConstructNode`] with named witness nodes.
///
/// Nodes other than witness don't have names.
pub type ConstructNode<J> = Node<WithNames<node::Construct<J>>>;

/// [`simplicity::CommitNode`] with named witness nodes.
///
/// Nodes other than witness don't have names.
pub type CommitNode<J> = Node<WithNames<node::Commit<J>>>;

// FIXME: The following methods cannot be implemented for simplicity::node::Node because that is a foreign type
pub fn finalize_types<J: Jet>(
    node: &Node<WithNames<node::Construct<J>>>,
) -> Result<Arc<Node<WithNames<node::Commit<J>>>>, types::Error> {
    // We finalize all types but don't bother to set the root source and target
    // to unit. This is a bit annoying to do, and anyway these types will already
    // be unit by construction.
    translate(node, |node, inner| {
        let inner = inner.map_witness(|_| &NoWitness);
        node::CommitData::new(node.cached_data().arrow(), inner).map(Arc::new)
    })
}

fn translate<M, N, F, E>(
    node: &Node<WithNames<M>>,
    translatefn: F,
) -> Result<Arc<Node<WithNames<N>>>, E>
where
    M: node::Marker,
    N: node::Marker<Jet = M::Jet>,
    N::Witness: Nullable,
    F: FnMut(
        &Node<WithNames<M>>,
        Inner<&N::CachedData, N::Jet, &NoDisconnect, &WitnessName>,
    ) -> Result<N::CachedData, E>,
{
    struct Translator<F>(F);

    impl<M, N, F, E> Converter<WithNames<M>, WithNames<N>> for Translator<F>
    where
        M: node::Marker,
        N: node::Marker<Jet = M::Jet>,
        N::Witness: Nullable,
        F: FnMut(
            &Node<WithNames<M>>,
            Inner<&N::CachedData, N::Jet, &NoDisconnect, &WitnessName>,
        ) -> Result<N::CachedData, E>,
    {
        type Error = E;

        fn convert_witness(
            &mut self,
            _: &PostOrderIterItem<&Node<WithNames<M>>>,
            wit: &WitnessName,
        ) -> Result<WitnessName, Self::Error> {
            Ok(wit.shallow_clone())
        }

        fn convert_disconnect(
            &mut self,
            _: &PostOrderIterItem<&Node<WithNames<M>>>,
            _: Option<&Arc<Node<WithNames<N>>>>,
            _: &NoDisconnect,
        ) -> Result<NoDisconnect, Self::Error> {
            Ok(NoDisconnect)
        }

        fn convert_data(
            &mut self,
            data: &PostOrderIterItem<&Node<WithNames<M>>>,
            inner: Inner<&Arc<Node<WithNames<N>>>, N::Jet, &NoDisconnect, &WitnessName>,
        ) -> Result<N::CachedData, Self::Error> {
            let new_inner = inner.map(|node| node.cached_data());
            self.0(data.node, new_inner)
        }
    }

    node.convert::<InternalSharing, _, _>(&mut Translator(translatefn))
}

/// Convert [`ConstructNode`] into [`CommitNode`] by dropping the name of witness nodes.
pub fn forget_names<M>(node: &Node<WithNames<M>>) -> Arc<Node<M>>
where
    M: node::Marker,
    M::Disconnect: Nullable,
    M::Witness: Nullable,
{
    struct Forgetter;

    impl<M> Converter<WithNames<M>, M> for Forgetter
    where
        M: node::Marker,
        M::Disconnect: Nullable,
        M::Witness: Nullable,
    {
        type Error = core::convert::Infallible;

        fn convert_witness(
            &mut self,
            _: &PostOrderIterItem<&Node<WithNames<M>>>,
            _: &WitnessName,
        ) -> Result<M::Witness, Self::Error> {
            Ok(M::Witness::none())
        }

        fn convert_disconnect(
            &mut self,
            _: &PostOrderIterItem<&Node<WithNames<M>>>,
            _: Option<&Arc<Node<M>>>,
            _: &NoDisconnect,
        ) -> Result<M::Disconnect, Self::Error> {
            Ok(M::Disconnect::none())
        }

        fn convert_data(
            &mut self,
            data: &PostOrderIterItem<&Node<WithNames<M>>>,
            _: Inner<&Arc<Node<M>>, M::Jet, &M::Disconnect, &M::Witness>,
        ) -> Result<M::CachedData, Self::Error> {
            Ok(data.node.cached_data().clone())
        }
    }

    match node.convert::<InternalSharing, _, _>(&mut Forgetter) {
        Ok(ret) => ret,
        Err(inf) => match inf {},
    }
}

/// Converts a named [`ConstructNode`] into a standard [`node::ConstructNode`], by populating
/// witness nodes with their assigned values.
///
/// Each witness node has a name. If there is no value assigned to this name,
/// then the node is left empty.
///
/// When [`node::ConstructNode`] is finalized to [`node::RedeemNode`], there will be an error if any witness
/// node on a used (unpruned) branch is empty. It is the responsibility of the caller to ensure that
/// all used witness nodes have an assigned value.
///
/// ## Soundness
///
/// It is the responsibility of the caller to ensure that the given witness `values` match the
/// types in the construct `node`. This can be done by calling [`WitnessValues::is_consistent`]
/// on the original SimplicityHL program before it is compiled to Simplicity.
pub fn populate_witnesses<J: Jet>(
    node: &ConstructNode<J>,
    values: WitnessValues,
) -> Arc<node::ConstructNode<J>> {
    struct Populator {
        values: WitnessValues,
    }

    impl<J: Jet> Converter<WithNames<node::Construct<J>>, node::Construct<J>> for Populator {
        type Error = core::convert::Infallible;

        fn convert_witness(
            &mut self,
            _: &PostOrderIterItem<&ConstructNode<J>>,
            witness: &WitnessName,
        ) -> Result<Option<simplicity::Value>, Self::Error> {
            let maybe_value = self
                .values
                .get(witness)
                .map(StructuralValue::from)
                .map(simplicity::Value::from);
            Ok(maybe_value)
        }

        fn convert_disconnect(
            &mut self,
            _: &PostOrderIterItem<&ConstructNode<J>>,
            _: Option<&Arc<node::ConstructNode<J>>>,
            _: &NoDisconnect,
        ) -> Result<Option<Arc<node::ConstructNode<J>>>, Self::Error> {
            Ok(None)
        }

        fn convert_data(
            &mut self,
            data: &PostOrderIterItem<&ConstructNode<J>>,
            _: Inner<
                &Arc<node::ConstructNode<J>>,
                J,
                &Option<Arc<node::ConstructNode<J>>>,
                &Option<simplicity::Value>,
            >,
        ) -> Result<node::ConstructData<J>, Self::Error> {
            Ok(data.node.cached_data().clone())
        }
    }

    let mut populator = Populator { values };
    match node.convert::<InternalSharing, _, _>(&mut populator) {
        Ok(ret) => ret,
        Err(inf) => match inf {},
    }
}

// This awkward construction is required by rust-simplicity to implement WitnessConstructible
// for Node<WithNames<Construct>>. See
//     https://docs.rs/simplicity-lang/latest/simplicity/node/trait.WitnessConstructible.html#foreign-impls
impl<J: Jet> WitnessConstructible<WitnessName> for node::ConstructData<J> {
    fn witness(inference_context: &types::Context, _: WitnessName) -> Self {
        WitnessConstructible::<Option<_>>::witness(inference_context, None)
    }
}

/// More constructors for types that implement [`CoreConstructible`].
pub trait CoreExt: CoreConstructible + Sized {
    fn h(inference_context: &types::Context) -> PairBuilder<Self> {
        PairBuilder::iden(inference_context)
    }

    fn o() -> SelectorBuilder<Self> {
        SelectorBuilder::default().o()
    }

    fn i() -> SelectorBuilder<Self> {
        SelectorBuilder::default().i()
    }

    fn bit(inference_context: &types::Context, bit: bool) -> PairBuilder<Self> {
        match bit {
            false => PairBuilder::unit(inference_context).injl(),
            true => PairBuilder::unit(inference_context).injr(),
        }
    }

    /// Compose a unit with a scribed value.
    ///
    /// ## Infallibility
    ///
    /// `unit` produces the unit value, which is the input of `scribe(v)`.
    ///
    /// ```text
    /// unit      : A → 1
    /// scribe(v) : 1 → B
    /// ---------------------------
    /// comp unit scribe(v) : A → B
    /// ```
    fn unit_scribe(inference_context: &types::Context, value: &simplicity::Value) -> Self {
        Self::comp(
            &Self::unit(inference_context),
            &Self::scribe(inference_context, value),
        )
        .unwrap()
    }

    /// `assertl (take s) cmr` always type checks.
    fn assertl_take(&self, cmr: Cmr) -> Self {
        Self::assertl(&Self::take(self), cmr).unwrap()
    }

    /// `assertl (drop s) cmr` always type checks.
    fn assertl_drop(&self, cmr: Cmr) -> Self {
        Self::assertl(&Self::drop_(self), cmr).unwrap()
    }

    /// `assertr cmr (drop s)` always type checks.
    fn assertr_take(cmr: Cmr, right: &Self) -> Self {
        Self::assertr(cmr, &Self::take(right)).unwrap()
    }

    /// `assertr cmr (take s)` always type checks.
    fn assertr_drop(cmr: Cmr, right: &Self) -> Self {
        Self::assertr(cmr, &Self::drop_(right)).unwrap()
    }

    /// `case false true` always type-checks.
    fn case_false_true(inference_context: &types::Context) -> Self {
        Self::case(
            &Self::bit_false(inference_context),
            &Self::bit_true(inference_context),
        )
        .unwrap()
    }

    /// `case true false` always type-checks.
    fn case_true_false(inference_context: &types::Context) -> Self {
        Self::case(
            &Self::bit_true(inference_context),
            &Self::bit_false(inference_context),
        )
        .unwrap()
    }
}

impl<N: CoreConstructible> CoreExt for N {}

/// Builder of expressions that contain
/// `take`, `drop` and `iden` only.
///
/// These expressions always type-check.
#[derive(Debug, Clone, Hash)]
pub struct SelectorBuilder<P> {
    selection: Vec<bool>,
    program: std::marker::PhantomData<P>,
}

impl<P> Default for SelectorBuilder<P> {
    fn default() -> Self {
        Self {
            selection: Vec::default(),
            program: std::marker::PhantomData,
        }
    }
}

impl<P: CoreExt> SelectorBuilder<P> {
    /// Select the first component '0' of the input pair.
    pub fn o(mut self) -> Self {
        self.selection.push(false);
        self
    }

    /// Select the second component '1' of the input pair.
    pub fn i(mut self) -> Self {
        self.selection.push(true);
        self
    }

    /// Pop the last selection.
    ///
    /// ## Panics
    ///
    /// The stack of selections is empty.
    pub fn pop(mut self) -> Self {
        self.selection.pop().expect("Stack is empty");
        self
    }

    /// Select the current input value.
    pub fn h(self, inference_context: &types::Context) -> PairBuilder<P> {
        let mut expr = PairBuilder::iden(inference_context);
        for bit in self.selection.into_iter().rev() {
            match bit {
                false => expr = expr.take(),
                true => expr = expr.drop_(),
            }
        }
        expr
    }
}

/// Builder of expressions that can be composed in pairs without restriction.
///
/// ## Invariant
///
/// These expressions preserve the following invariant:
/// Their source type is a (nested) product of type variables.
/// The source type contains neither sums nor any concrete types.
#[derive(Debug, Clone, Hash)]
pub struct PairBuilder<P>(P);

impl<P: CoreExt> PairBuilder<P> {
    /// Create the unit expression.
    ///
    /// ## Invariant
    ///
    /// `unit` has a type variable as its source type.
    ///
    /// ```text
    /// ------------
    /// unit : A → 1
    /// ```
    pub fn unit(inference_context: &types::Context) -> Self {
        Self(P::unit(inference_context))
    }

    /// Create the identity expression.
    ///
    /// ## Invariant
    ///
    /// `iden` has a type variable as its source type.
    ///
    /// ```text
    /// ------------
    /// iden : A → A
    /// ```
    pub fn iden(inference_context: &types::Context) -> Self {
        Self(P::iden(inference_context))
    }

    /// Create the fail expression.
    ///
    /// ## Invariant
    ///
    /// `fail` has a type variable as its source type.
    ///
    /// ```text
    /// ------------
    /// fail : A → B
    /// ```
    pub fn fail(inference_context: &types::Context, entropy: FailEntropy) -> Self {
        Self(P::fail(inference_context, entropy))
    }

    /// Left-inject the expression.
    ///
    /// ## Invariant
    ///
    /// By induction, `t` has a nested product of type variables as its source type.
    /// `injl t` has the same source type as `t`.
    /// Therefore, `injl t` has a nested product of type variables as its source type.
    ///
    /// ```text
    /// t : A → B
    /// ------------------
    /// injl t : A → B + C
    /// ```
    pub fn injl(self) -> Self {
        Self(P::injl(&self.0))
    }

    /// Left-inject the expression.
    ///
    /// ## Invariant
    ///
    /// By induction, `t` has a nested product of type variables as its source type.
    /// `injr t` has the same source type as `t`.
    /// Therefore, `injr t` has a nested product of type variables as its source type.
    ///
    /// ```text
    /// t : A → C
    /// ------------------
    /// injr t : A → B + C
    /// ```
    pub fn injr(self) -> Self {
        Self(P::injr(&self.0))
    }

    /// Take the expression.
    ///
    /// ## Invariant
    ///
    /// By induction, `t` has a nested product of type variables as its source type `A`.
    /// `take t` has the product of type `A` and of the type variable `B` as its source type.
    /// Therefore, `take t` has a nested product of type variables as its source type.
    ///
    /// ```text
    /// t : A → C
    /// ------------------
    /// take t : A × B → C
    /// ```
    pub fn take(self) -> Self {
        Self(P::take(&self.0))
    }

    /// Drop the expression.
    ///
    /// ## Invariant
    ///
    /// By induction, `t` has a nested product of type variables as its source type `B`.
    /// `drop t` has the product of the type variable `A` and of type `B` as its source type.
    /// Therefore, `drop t` has a nested product of type variables as its source type.
    ///
    /// ```text
    /// t : B → C
    /// ------------------
    /// drop t : A × B → C
    /// ```
    pub fn drop_(self) -> Self {
        Self(P::drop_(&self.0))
    }

    /// Compose two expressions.
    ///
    /// ## Left-associativity
    ///
    /// ```text
    /// a.comp(b).comp(c) = comp (comp a b) c
    /// a.comp(b.comp(c)) = comp a (comp b c)
    /// ```
    ///
    /// ## Fallibility
    ///
    /// The composition will fail if the target type of the left sub-expression
    /// cannot be unified with the source type of the right sub-expression.
    ///
    /// ## Invariant
    ///
    /// By induction, `s` has a nested product of type variables as its source type.
    /// `comp s t` has the same source type as `s`.
    /// Therefore, `comp s t` has a nested product of type variables as its source type.
    ///
    /// Note that `t` can be **any** Simplicity expression since we don't need its invariant.
    ///
    /// ```text
    /// s : A → B
    /// t : B → C
    /// ----------------
    /// comp s t : A → C
    /// ```
    pub fn comp<Q: std::borrow::Borrow<P>>(self, other: &Q) -> Result<Self, types::Error> {
        P::comp(&self.0, other.borrow()).map(Self)
    }

    /// Pair two expressions.
    ///
    /// ## Left-associativity
    ///
    /// ```text
    /// a.pair(b).pair(c) = pair (pair a b) c
    /// a.pair(b.pair(c)) = pair a (pair b c)
    /// ```
    ///
    /// ## Infallibility
    ///
    /// `pair s t` unifies the source types of `s` and `t`.
    /// Unification fails when there is a mismatch between products, sums or concrete types.
    /// By induction, the source types of `s` and `t` are both nested products of type variables,
    /// which contain neither sums nor concrete types.
    /// Therefore, unification always succeeds.
    ///
    /// ```text
    /// s : A → B
    /// t : A → C
    /// --------------------
    /// pair s t : A → B × C
    /// ```
    ///
    /// ## Invariant
    ///
    ///  By induction, `s` has a nested product of type variables as its source type.
    /// `pair s t` has the same source type as `s`.
    /// Therefore, `pair s t` has a nested product of type variables as its source type.
    pub fn pair(self, other: Self) -> Self {
        Self(P::pair(&self.0, &other.0).unwrap())
    }

    /// Compose a unit with a scribed value.
    ///
    /// ## Invariant
    ///
    /// `unit` has a type variable as its source type.
    /// `comp unit scribe(v)` has the same source type as `unit`.
    /// Therefore, `comp unit scribe(v)` has a nested product of type variables as its source type.
    ///
    /// ```text
    /// unit      : A → 1
    /// scribe(v) : 1 → B
    /// ---------------------------
    /// comp unit scribe(v) : A → B
    /// ```
    pub fn unit_scribe(inference_context: &types::Context, value: &simplicity::Value) -> Self {
        Self(P::unit_scribe(inference_context, value))
    }
}

impl<P: WitnessConstructible<WitnessName>> PairBuilder<P> {
    /// Create the witness expression.
    ///
    /// ## Invariant
    ///
    /// `witness` has a type variable as its source type.
    ///
    /// ```text
    /// ---------------
    /// witness : A → B
    /// ```
    pub fn witness(inference_context: &types::Context, witness: WitnessName) -> Self {
        Self(P::witness(inference_context, witness))
    }
}

impl<P> PairBuilder<P> {
    /// Build the expression.
    pub fn build(self) -> P {
        self.0
    }
}

impl<P> AsRef<P> for PairBuilder<P> {
    fn as_ref(&self) -> &P {
        &self.0
    }
}

impl<P> std::borrow::Borrow<P> for PairBuilder<P> {
    fn borrow(&self) -> &P {
        &self.0
    }
}
