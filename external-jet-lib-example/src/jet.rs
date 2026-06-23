//! Implementation of a custom Simplicity jet family that is compiled into a shared
//! library and loaded into a SimplicityHL compiler at runtime.
//!
//! A *jet* is a named, primitive operation that a Simplicity program can invoke
//! as a single node of its DAG. Conceptually a jet is a "black box": the type
//! checker and the bit machine only know the jet's *interface* (its types,
//! encoding, cost and commitment), while its actual behaviour is fixed by a
//! reference implementation. This crate sits at the meeting point of three
//! layers:
//!
//! # What this module provides
//!
//! [`HappyJet`] is a demonstrative jet family with a single member,
//! [`HappyJet::Verify`]. Implementing [`Jet`] and [`JetHL`] for it is all that is
//! required to inform both the SimplicityHL compiler how to
//! handle the jet. The surrounding crate then re-exports these methods
//! across a C ABI (see the crate root in `lib.rs`) so that a separately
//! compiled SimplicityHL binary can load them from a `.so` / `.dylib` / `.dll`
//! without being rebuilt.

use std::io::Write;

use simplicityhl::{
    jet::{JetHL, SourceJetClassification, TargetJetClassification},
    simplicity::{
        decode::Error,
        decode_bits,
        jet::{type_name::TypeName, Jet},
        BitIter, BitWriter, Cmr, Cost, Error as SimplicityError,
    },
};

/// FFI-safe handle that identifies jet of this library across the dynamic
/// library boundary.
///
/// Trait objects (`Box<dyn JetHL>`) and Rust enums have no stable ABI, so they
/// cannot be passed safely between two independently compiled binaries. Instead,
/// every jet is represented on the wire by a plain integer
/// [`index`](Self::index), and each side reconstructs the real jet from that
/// number.
///
/// The host compiler (`simplicityhl`) defines its *own*
/// `jet::external::ExternalJet` with an identical layout (a single `u64`). The
/// two types are deliberately ABI-compatible: values are passed by copy across
/// the boundary, and each side maps the `index` back to its local representation
/// ([`HappyJet`] here). Keeping the layouts in sync is part of the contract
/// between this library and the loader.
pub struct ExternalJet {
    pub index: u64,
}

/// The jet family defined by this library.
///
/// This every jet the library knows about. To add another jet you would add
/// a variant here, give it a unique [`index`](Self::index), and extend each
/// method of the [`Jet`] and [`JetHL`] implementations below. The single member,
/// [`HappyJet::Verify`], mirrors the standard Simplicity `verify` jet: it consumes
/// one bit and succeeds only if that bit is `1`, which is exactly
/// the primitive that `assert!` lowers to.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum HappyJet {
    Verify,
}

impl HappyJet {
    /// Returns the identifier of this jet.
    ///
    /// The mapping between variants and indices is the ABI contract that lets a
    /// jet cross the library boundary as a bare integer (see [`ExternalJet`]).
    /// Every variant has an index and a given index always means the same jet,
    /// so existing variants must never be renumbered.
    pub fn index(&self) -> u64 {
        match self {
            HappyJet::Verify => 0,
        }
    }

    /// Reconstructs a jet from the index produced by [`index`](Self::index).
    ///
    /// This is the inverse of [`index`](Self::index). It returns [`None`] for an
    /// unknown index, which the FFI layer treats as a fatal contract violation
    /// (the host should only ever hand back indices this library handed out).
    pub fn from_index(index: u64) -> Option<Self> {
        match index {
            0 => Some(HappyJet::Verify),
            _ => None,
        }
    }
}

/// rust-simplicity prt of the jet.
///
/// These methods describe the jet to the Simplicity bit machine itself: its
/// identity, its Simplicity-level types, how it is serialised inside an encoded
/// program, its cost, and how its name is parsed. Everything here is independent
/// of the high-level language.
impl Jet for HappyJet {
    /// Returns the **Commitment Merkle Root** (CMR) of the jet.
    ///
    /// The CMR is a 32-byte tagged hash that is the cryptographic identity of
    /// a Simplicity node. Programs commit to their CMR (for example inside a
    /// Taproot output), so the CMR of every leaf feeds into the identity of
    /// the whole program. For a jet the CMR is a fixed constant defined by the
    /// specification, not something derived at runtime.
    ///
    /// **Importance:** all parties must agree on this exact value. If two
    /// implementations disagree on a jet's CMR they compute different program
    /// identities, and a validator that does not recognise the CMR cannot
    /// execute the jet. The bytes below are therefore hard-coded and must match
    /// the reference definition.
    fn cmr(&self) -> Cmr {
        let bytes = match self {
            HappyJet::Verify => [
                0xcd, 0xca, 0x2a, 0x05, 0xe5, 0x2c, 0xef, 0xa5, 0x9d, 0xc7, 0xa5, 0xb0, 0xda, 0xe2,
                0x20, 0x98, 0xfb, 0x89, 0x6e, 0x39, 0x13, 0xbf, 0xdd, 0x44, 0x6b, 0x59, 0x4e, 0x1f,
                0x92, 0x50, 0x78, 0x3e,
            ],
        };
        Cmr::from_byte_array(bytes)
    }

    /// Returns the **source** (input) type of the jet as a [`TypeName`].
    ///
    /// Because jets are opaque to Simplicity's type-inference engine, their
    /// types must be stated explicitly. A [`TypeName`] is a byte string written
    /// in prefix (Polish) notation where `1` = unit, `2` = a single bit,
    /// `c`/`s`/`i`/`l`/`h` = 8/16/32/64/256-bit words, and `+`/`*` are sum and
    /// product. Here `verify` has source `b"2"`, a single bit — i.e. a `bool`,
    /// since the boolean type is the sum `1 + 1`.
    fn source_ty(&self) -> TypeName {
        let name: &'static [u8] = match self {
            HappyJet::Verify => b"2",
        };

        TypeName(name)
    }

    /// Returns the **target** (output) type of the jet as a [`TypeName`].
    ///
    /// Encoded exactly like [`source_ty`](Self::source_ty). `verify` returns
    /// `b"1"`, the unit type: it produces no data and is invoked purely for its
    /// side effect of asserting that the input bit is `1`.
    fn target_ty(&self) -> TypeName {
        let name: &'static [u8] = match self {
            HappyJet::Verify => b"1",
        };

        TypeName(name)
    }

    /// Serialises the jet into the bit-level encoding of a Simplicity program.
    ///
    /// # Where this fits in the program encoding
    ///
    /// A Simplicity program is serialised as a list of nodes. The node encoder
    /// (rust-simplicity's `bit_encoding::encode::encode_node`) first writes a
    /// short prefix that classifies each node; for a jet that prefix is the two
    /// bits `1` (this is a *jet-or-word*, not a combinator) then `1` (it is a
    /// *jet*, not a constant word). Only *after* those bits does it call this
    /// method, so `encode` is responsible solely for the **jet code**: the bits
    /// that say *which* jet of this library it is. A complete `verify` node on
    /// the wire is therefore `1` `1` followed by the single bit produced here:
    ///
    /// ```text
    /// 1 1 0
    /// │ │ └── jet code from HappyJet::encode (selects `verify`)
    /// │ └──── node is a jet (not a constant word)
    /// └────── node is a jet-or-word (not a combinator)
    /// ```
    ///
    /// # The jet code is a prefix-free tree
    ///
    /// The jets of a family are the leaves of a binary tree, and a jet's code is
    /// the path of `0`/`1` branches from the root down to its leaf. The pair
    /// `(n, len)` passed to `write_bits_be` *is* that path: `len` is the depth
    /// and the low `len` bits of `n` (most-significant first) are the branch
    /// directions. Since no jet's path is a prefix of another's, the decoder can
    /// find where the code ends without a separate length field.
    ///
    /// This library's tree has a **single** leaf, so the path is just the one
    /// bit `0` — hence `(n, len) = (0, 1)`. Real jet sets have many leaves and
    /// thus longer codes (see below).
    ///
    /// The code here **must** stay in lock-step with [`decode`](Self::decode),
    /// which walks the same tree in reverse.
    fn encode(&self, w: &mut BitWriter<&mut dyn Write>) -> std::io::Result<usize> {
        let (n, len) = match self {
            HappyJet::Verify => (0, 1),
        };

        w.write_bits_be(n, len)
    }

    /// Reconstructs a jet from the bit encoding produced by
    /// [`encode`](Self::encode).
    ///
    /// Decoding is the mirror of encoding: starting at the root of the jet tree,
    /// each incoming bit chooses a branch (`0` = first/left, `1` = second/right)
    /// until a leaf is reached. The [`decode_bits!`] macro
    /// builds exactly that decision tree. Here the tree has a single real leaf:
    ///
    /// ```text
    /// root ─┬─ 0 ─> HappyJet::Verify
    ///       └─ 1 ─> (empty, reserved for future jets)
    /// ```
    fn decode<I: Iterator<Item = u8>>(bits: &mut BitIter<I>) -> Result<Self, Error>
    where
        Self: Sized,
    {
        decode_bits!(bits, {
            0 => {HappyJet::Verify},
            1 => {}
        })
    }

    /// Returns the execution **cost** of the jet, in milliweight units.
    ///
    /// Simplicity bounds CPU usage with a cost model: the summed cost of every
    /// executed node must stay within the program's *budget*, which is funded by
    /// the size of the transaction's witness stack. One weight unit is 1000
    /// milliweight, so `from_milliweight(44)` is 0.044 weight units. The value
    /// should reflect the real cost of the operation and match the figure,
    /// otherwise budgets computed by different parties will disagree.
    fn cost(&self) -> Cost {
        match self {
            HappyJet::Verify => Cost::from_milliweight(44),
        }
    }

    /// Parses the textual name of a jet into the corresponding variant.
    ///
    /// This is what resolves the identifier written after `jet::` in SimplicityHL
    /// source (and in Simplicity s-expressions). The name `"verify"` maps to
    /// [`HappyJet::Verify`. It is the inverse of the [`Display`](std::fmt::Display)
    /// implementation.
    fn parse(s: &str) -> Result<Self, SimplicityError>
    where
        Self: Sized,
    {
        match s {
            "verify" => Ok(HappyJet::Verify),
            x => Err(SimplicityError::InvalidJetName(x.to_owned())),
        }
    }
}

/// Renders the jet back to its textual name.
///
/// This is the inverse of [`HappyJet::parse`] and is used in error messages,
/// debug output and any text serialisation of a program. The two must
/// round-trip: `HappyJet::parse(&jet.to_string()) == Ok(jet)`.
impl std::fmt::Display for HappyJet {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            HappyJet::Verify => write!(f, "verify"),
        }
    }
}

/// SimplicityHL (high-level language) view of the jet.
///
/// Where [`Jet`] describes the jet in raw Simplicity terms (bit-level types),
/// [`JetHL`] describes how it appears in SimplicityHL's richer type system. The
/// compiler uses this to type-check call sites such as `jet::verify(x)` and to
/// bind the jet's arguments and result to high-level types.
impl JetHL for HappyJet {
    /// Describes how the Simplicity source type is split into SimplicityHL
    /// argument types.
    ///
    /// For the regular the compiler assumes the input is a balanced product of
    /// equal-width integers and derives each argument type from the total bit
    /// width. `verify` does not fit that mould — its single bit is a *boolean*,
    /// not a 1-bit integer — so we use
    /// [`Custom`](SourceJetClassification::Custom) to state the argument list
    /// explicitly as `[bool]`.
    fn source_jet_classification(&self) -> SourceJetClassification {
        match self {
            HappyJet::Verify => SourceJetClassification::Custom(vec![simplicityhl::jet::bool()]),
        }
    }

    /// Describes the SimplicityHL **return** type of the jet.
    ///
    /// [`Unary`](TargetJetClassification::Unary) asks the compiler to derive a
    /// single value from the target bit width. Because `verify`'s target is unit
    /// (bit width 0), that derivation yields the unit type `()`; the jet is used
    /// for its assertion side-effect rather than a return value. Use
    /// [`Custom`](TargetJetClassification::Custom) when the output is not a plain
    /// integer.
    fn target_jet_classification(&self) -> TargetJetClassification {
        match self {
            HappyJet::Verify => TargetJetClassification::Unary,
        }
    }

    /// Reports whether the jet may be referenced *directly* by name in
    /// SimplicityHL source.
    ///
    /// When this returns `true`, the compiler treats `jet::<name>` as
    /// non-existent at the call site even though it can still be parsed. The
    /// built-in `Core`/`Elements` sets disable their `verify` jet so that users
    /// reach it only through `assert!`. This example leaves it **enabled**, so
    /// both `jet::verify(x)` and `assert!(x)` work, the latter is lowered through
    /// the hinter's `construct_verify`, independently of this flag.
    fn is_disabled(&self) -> bool {
        false
    }

    /// Clones the jet into a fresh `Box<dyn JetHL>`.
    ///
    /// [`JetHL`] is used as a trait object, and trait objects cannot implement
    /// [`Clone`] directly. This method provides the object-safe cloning that
    /// `Box<dyn JetHL>: Clone` forwards to.
    fn clone_box(&self) -> Box<dyn JetHL> {
        Box::new(*self)
    }

    /// Returns the jet as a lower-level [`Jet`] trait object (`&dyn Jet`).
    ///
    /// The compiler needs a `&dyn Jet` to build Simplicity nodes from a
    /// `&dyn JetHL`; this method performs that upcast explicitly.
    fn as_jet(&self) -> &dyn Jet {
        self
    }
}
