//! C-ABI surface of the external jet library.
//!
//! This is the boundary that turns [`HappyJet`] into a runtime *plugin*. The
//! crate is built as a `cdylib`, and every `#[no_mangle]` function below is
//! exported as a symbol that the host SimplicityHL compiler resolves by name
//! (via `dlopen` / `LoadLibraryW`) into its `ExternalJetLib` function-pointer
//! table. At runtime the host calls these symbols to ask the library to describe
//! and construct its jets. We use the `#[no_mangle]` attribute to prevent Rust
//! from changing the symbol names.
//!
//! # The bridging pattern
//!
//! The host speaks in terms of the FFI-safe [`ExternalJet`] handle (an integer
//! index), while all real behaviour lives on [`HappyJet`]. Almost every export
//! therefore follows the same three steps:
//!
//! 1. receive an [`ExternalJet`] (or a name, or a `&dyn Jet`),
//! 2. rebuild the real [`HappyJet`] from it with
//!    [`HappyJet::from_index`], and
//! 3. delegate to the corresponding [`Jet`] or [`JetHL`] method, returning the
//!    result by value.
//!
//! Because the host should only ever pass back indices this library handed out,
//! an unknown index is a fatal ABI violation rather than a recoverable error, so
//! the `from_index(..).expect(..)` calls below intentionally panic.
//!
//! # ABI contract
//!
//! The set of symbol names and their exact signatures must match
//! `ExternalJetLib::load` in the host crate (`src/jet/external.rs`). The loader
//! transmutes each resolved address into a Rust `fn` pointer **without** checking
//! the signature, so any mismatch is undefined behaviour. These functions use the
//! default Rust ABI rather than `extern "C"`, that is sound only because the host
//! and this library are built with the same toolchain and share the exact same
//! `simplicity` / `simplicityhl` types.
//!
//! # Safety
//!
//! Loading and calling this library executes arbitrary native code in the host
//! process. Only load libraries built from trusted, verified sources.

use std::io::Write;

use simplicityhl::{
    jet::{JetHL, SourceJetClassification, TargetJetClassification},
    simplicity::{
        jet::{type_name::TypeName, Jet},
        BitWriter, Cmr, Cost,
    },
};

use crate::jet::{ExternalJet, HappyJet};

/// Jet definitions ([`HappyJet`]) and their [`Jet`]/[`JetHL`] implementations.
pub mod jet;

/// Exports [`HappyJet::cmr`]: the jet's Commitment Merkle Root (its identity).
#[no_mangle]
pub fn cmr(jet: ExternalJet) -> Cmr {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.cmr()
}

/// Exports [`HappyJet::source_ty`]: the jet's Simplicity source (input) type.
#[no_mangle]
pub fn source_ty(jet: ExternalJet) -> TypeName {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.source_ty()
}

/// Exports [`HappyJet::target_ty`]: the jet's Simplicity target (output) type.
#[no_mangle]
pub fn target_ty(jet: ExternalJet) -> TypeName {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.target_ty()
}

/// Exports [`HappyJet::encode`]: serialises the jet into a program's bit stream.
///
/// The host passes its own [`BitWriter`] (the bit-level framing the Simplicity
/// encoding expects) wrapping the underlying byte sink, and this export simply
/// delegates to [`HappyJet::encode`]. The signature must match the
/// `ExternalJetLib::encode` field in the host crate exactly — see the
/// module-level note on the ABI contract.
#[no_mangle]
pub fn encode(jet: ExternalJet, w: &mut BitWriter<&mut dyn Write>) -> std::io::Result<usize> {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.encode(w)
}

/// Exports [`HappyJet::cost`]: the jet's execution cost (in milliweight units).
#[no_mangle]
pub fn cost(jet: ExternalJet) -> Cost {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.cost()
}

/// Exports [`HappyJet::parse`]: resolves a jet name to a handle.
///
/// Unlike most exports this takes a name rather than an [`ExternalJet`]: it is
/// how the host turns the identifier written after `jet::` into a handle. On
/// success the resulting [`HappyJet`] is reduced to its [`ExternalJet`] index for
/// return across the boundary.
#[no_mangle]
pub fn parse(s: &str) -> Result<ExternalJet, simplicityhl::simplicity::Error> {
    HappyJet::parse(s).map(|jet| ExternalJet { index: jet.index() })
}
/// Exports the [`Display`](std::fmt::Display) name of the jet.
#[no_mangle]
pub fn display(jet: ExternalJet) -> String {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.to_string()
}

/// Exports [`JetHL::source_jet_classification`]: how the compiler splits the
/// source type into high-level argument types.
#[no_mangle]
pub fn source_jet_classification(jet: ExternalJet) -> SourceJetClassification {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.source_jet_classification()
}

/// Exports [`JetHL::target_jet_classification`]: the high-level return type of
/// the jet.
#[no_mangle]
pub fn target_jet_classification(jet: ExternalJet) -> TargetJetClassification {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.target_jet_classification()
}

/// Exports [`JetHL::is_disabled`]: whether the jet may be named directly in
/// SimplicityHL source.
#[no_mangle]
pub fn is_disabled(jet: ExternalJet) -> bool {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.is_disabled()
}

/// Constructs the library's `verify` jet handle.
///
/// The host's `ExternalJetHinter::construct_verify` calls this when lowering
/// `assert!`, so this single export is what makes assertions work with the
/// external jet set. It returns the [`ExternalJet`] index of
/// [`HappyJet::Verify`].
#[no_mangle]
pub fn verify() -> ExternalJet {
    let jet = HappyJet::Verify;

    ExternalJet { index: jet.index() }
}

/// Recovers the high-level jet from a bare runtime Simplicity jet.
///
/// Given a type-erased `&dyn Jet`, for example one obtained while inspecting or
/// tracing an already-built program, this attempts to downcast it to
/// [`HappyJet`] and re-box it as a [`JetHL`], re-attaching the high-level
/// behaviour. It returns [`None`] if the jet does not belong to this library.
/// This mirrors the `conjure` method of the built-in jet hinters.
#[no_mangle]
pub fn conjure(jet: &dyn Jet) -> Option<Box<dyn JetHL>> {
    jet.as_any()
        .downcast_ref::<HappyJet>()
        .map(|jet| Box::new(*jet) as Box<dyn JetHL>)
}
