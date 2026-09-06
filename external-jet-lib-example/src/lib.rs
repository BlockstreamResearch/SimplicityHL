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
//! On native targets the set of symbol names and their exact signatures must
//! match `ExternalJetDynamicLib::load` in the host crate
//! (`src/jet/external/dynamic.rs`). The loader transmutes each resolved address
//! into a Rust `fn` pointer **without** checking the signature, so any mismatch
//! is undefined behaviour. These functions use the default Rust ABI rather than
//! `extern "C"`; that is sound only because the host and this library are built
//! with the same toolchain and share the exact same `simplicity` / `simplicityhl`
//! types.
//!
//! On `wasm32` the compiler and this plugin are separate modules with separate
//! linear memories, so any Rust value that carries a pointer (a `String`, a
//! `TypeName`, a classification, ...) cannot be shared directly: the pointer
//! would be read against the wrong memory. Each such entry point is therefore
//! compiled as an `extern "C"` shim with an explicit `(index, out_ptr, cap) ->
//! i32` signature that serialises the value into a caller-owned buffer. These
//! shims must match the imports declared in `src/jet/external/wasm.rs`.
//!
//! # Safety
//!
//! Loading and calling this library executes arbitrary native code in the host
//! process. Only load libraries built from trusted, verified sources.

use std::io::Write;

use simplicityhl::{
    jet::JetHL,
    simplicity::{jet::Jet, BitWriter, Cost},
};
// Types named only in the native (default-ABI) exports; the wasm32 shims use
// the shared byte serialisation instead, so these would be unused there.
#[cfg(not(target_arch = "wasm32"))]
use simplicityhl::{
    jet::{SourceJetClassification, TargetJetClassification},
    simplicity::{jet::type_name::TypeName, Cmr},
};

use crate::jet::{ExternalJet, HappyJet};

/// Jet definitions ([`HappyJet`]) and their [`Jet`]/[`JetHL`] implementations.
pub mod jet;

/// Copy `bytes` into the caller-owned buffer described by `out_ptr`/`cap` (which
/// live in *this* plugin module's memory) and report the value's full length.
///
/// This is the write half of the wasm ptr/len/out ABI: because the compiler and
/// the plugin have separate linear memories, the host bridge, not the compiler,
/// hands us a buffer in our own memory. We copy at most `cap` bytes and always
/// return the total length, so a caller that probed with a small buffer can grow
/// it and call again.
///
/// # Safety
///
/// `out_ptr` must be either null or valid for writes of `cap` bytes.
#[cfg(target_arch = "wasm32")]
unsafe fn write_out(bytes: &[u8], out_ptr: *mut u8, cap: usize) -> i32 {
    let n = bytes.len().min(cap);
    if !out_ptr.is_null() && n > 0 {
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), out_ptr, n);
    }
    bytes.len() as i32
}

/// Exports [`HappyJet::cmr`]: the jet's Commitment Merkle Root (its identity).
#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
pub fn cmr(jet: ExternalJet) -> Cmr {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.cmr()
}

/// wasm32 shim for [`cmr`]: writes the 32-byte CMR into the caller's buffer.
#[cfg(target_arch = "wasm32")]
#[no_mangle]
pub unsafe extern "C" fn cmr(index: u64, out_ptr: *mut u8, cap: usize) -> i32 {
    let jet = HappyJet::from_index(index).expect("invalid jet index");
    write_out(&jet.cmr().to_byte_array(), out_ptr, cap)
}

/// Exports [`HappyJet::source_ty`]: the jet's Simplicity source (input) type.
#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
pub fn source_ty(jet: ExternalJet) -> TypeName {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.source_ty()
}

/// wasm32 shim for [`source_ty`]: writes the type-name bytes into the buffer.
#[cfg(target_arch = "wasm32")]
#[no_mangle]
pub unsafe extern "C" fn source_ty(index: u64, out_ptr: *mut u8, cap: usize) -> i32 {
    let jet = HappyJet::from_index(index).expect("invalid jet index");
    write_out(jet.source_ty().0, out_ptr, cap)
}

/// Exports [`HappyJet::target_ty`]: the jet's Simplicity target (output) type.
#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
pub fn target_ty(jet: ExternalJet) -> TypeName {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.target_ty()
}

/// wasm32 shim for [`target_ty`]: writes the type-name bytes into the buffer.
#[cfg(target_arch = "wasm32")]
#[no_mangle]
pub unsafe extern "C" fn target_ty(index: u64, out_ptr: *mut u8, cap: usize) -> i32 {
    let jet = HappyJet::from_index(index).expect("invalid jet index");
    write_out(jet.target_ty().0, out_ptr, cap)
}

/// Exports [`HappyJet::encode`]: serialises the jet into a program's bit stream.
///
/// The host passes its own [`BitWriter`] (the bit-level framing the Simplicity
/// encoding expects) wrapping the underlying byte sink, and this export simply
/// delegates to [`HappyJet::encode`]. The signature must match the
/// `ExternalJetLib::encode` field in the host crate exactly — see the
/// module-level note on the ABI contract.
#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
pub fn encode(jet: ExternalJet, w: &mut BitWriter<&mut dyn Write>) -> std::io::Result<usize> {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.encode(w)
}

/// wasm32 shim for [`encode`].
///
/// The compiler owns the real [`BitWriter`] (in its memory), which cannot be
/// shared here, so instead we serialise into a local byte buffer, copy the
/// packed bits into the caller's buffer, and return the **bit** count. The
/// compiler replays those bits into its writer. Bytes are MSB-first, exactly as
/// [`BitWriter`] packs them.
#[cfg(target_arch = "wasm32")]
#[no_mangle]
pub unsafe extern "C" fn encode(index: u64, out_ptr: *mut u8, cap: usize) -> i32 {
    let jet = HappyJet::from_index(index).expect("invalid jet index");

    let mut bytes: Vec<u8> = Vec::new();
    let n_bits;
    {
        let sink: &mut dyn Write = &mut bytes;
        let mut w: BitWriter<&mut dyn Write> = BitWriter::new(sink);
        jet.encode(&mut w).expect("encoding to a vec never fails");
        n_bits = w.n_total_written();
        w.flush_all().expect("flushing a vec never fails");
    }

    let n = bytes.len().min(cap);
    if !out_ptr.is_null() && n > 0 {
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), out_ptr, n);
    }
    n_bits as i32
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
#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
pub fn parse(s: &str) -> Result<ExternalJet, simplicityhl::simplicity::Error> {
    HappyJet::parse(s).map(|jet| ExternalJet { index: jet.index() })
}

/// wasm32 shim for the current compiler import signature of `parse`.
#[cfg(target_arch = "wasm32")]
#[no_mangle]
pub unsafe extern "C" fn parse(name_ptr: *const u8, name_len: usize, out: *mut ExternalJet) -> i32 {
    let bytes = std::slice::from_raw_parts(name_ptr, name_len);
    let Ok(name) = std::str::from_utf8(bytes) else {
        return 1;
    };
    let Ok(jet) = HappyJet::parse(name) else {
        return 1;
    };
    std::ptr::write(out, ExternalJet { index: jet.index() });
    0
}
/// Exports the [`Display`](std::fmt::Display) name of the jet.
#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
pub fn display(jet: ExternalJet) -> String {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.to_string()
}

/// wasm32 shim for [`display`]: writes the UTF-8 name into the caller's buffer.
#[cfg(target_arch = "wasm32")]
#[no_mangle]
pub unsafe extern "C" fn display(index: u64, out_ptr: *mut u8, cap: usize) -> i32 {
    let jet = HappyJet::from_index(index).expect("invalid jet index");
    write_out(jet.to_string().as_bytes(), out_ptr, cap)
}

/// Exports [`JetHL::source_jet_classification`]: how the compiler splits the
/// source type into high-level argument types.
#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
pub fn source_jet_classification(jet: ExternalJet) -> SourceJetClassification {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.source_jet_classification()
}

/// wasm32 shim for [`source_jet_classification`].
///
/// The classification carries heap-allocated `AliasedType`s, so it is flattened
/// with the shared [`serialize_source_jet_classification`] wire format before
/// being copied into the caller's buffer.
///
/// [`serialize_source_jet_classification`]: simplicityhl::jet::external::serialize_source_jet_classification
#[cfg(target_arch = "wasm32")]
#[no_mangle]
pub unsafe extern "C" fn source_jet_classification(
    index: u64,
    out_ptr: *mut u8,
    cap: usize,
) -> i32 {
    let jet = HappyJet::from_index(index).expect("invalid jet index");
    let bytes = simplicityhl::jet::external::serialize_source_jet_classification(
        &jet.source_jet_classification(),
    );
    write_out(&bytes, out_ptr, cap)
}

/// Exports [`JetHL::target_jet_classification`]: the high-level return type of
/// the jet.
#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
pub fn target_jet_classification(jet: ExternalJet) -> TargetJetClassification {
    let jet = HappyJet::from_index(jet.index).expect("invalid jet index");

    jet.target_jet_classification()
}

/// wasm32 shim for [`target_jet_classification`], mirroring
/// [`source_jet_classification`]'s serialisation across the memory boundary.
#[cfg(target_arch = "wasm32")]
#[no_mangle]
pub unsafe extern "C" fn target_jet_classification(
    index: u64,
    out_ptr: *mut u8,
    cap: usize,
) -> i32 {
    let jet = HappyJet::from_index(index).expect("invalid jet index");
    let bytes = simplicityhl::jet::external::serialize_target_jet_classification(
        &jet.target_jet_classification(),
    );
    write_out(&bytes, out_ptr, cap)
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
#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
pub fn conjure(jet: &dyn Jet) -> Option<Box<dyn JetHL>> {
    jet.as_any()
        .downcast_ref::<HappyJet>()
        .map(|jet| Box::new(*jet) as Box<dyn JetHL>)
}
