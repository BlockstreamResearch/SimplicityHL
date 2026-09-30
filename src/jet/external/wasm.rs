#![cfg(target_arch = "wasm32")]

use std::collections::HashSet;
use std::io::Write;
use std::sync::{Mutex, OnceLock};

use simplicity::{
    jet::{type_name::TypeName, Jet},
    BitWriter, Cmr, Cost,
};

use crate::jet::{
    external::{
        backend::ExternalJetLib, deserialize_source_jet_classification,
        deserialize_target_jet_classification, ExternalJet, EXTERNAL_JET_ABI_VERSION,
    },
    JetHL, SourceJetClassification, TargetJetClassification,
};

/// External jet backend for `wasm32` builds.
///
/// All methods are imported from the `simplicityhl-plugin` wasm module,
/// which the embedding host (e.g. a browser) provides.
#[derive(Clone, Debug, Default)]
pub struct ExternalJetWasmLib;

static EXTERNAL_JET_WASM_LIB: ExternalJetWasmLib = ExternalJetWasmLib;
static ABI_COMPATIBLE: OnceLock<()> = OnceLock::new();

pub(super) fn external_jet_lib() -> &'static ExternalJetWasmLib {
    ABI_COMPATIBLE.get_or_init(|| {
        let version = unsafe { external_jet_abi_version() };
        assert_eq!(
            version, EXTERNAL_JET_ABI_VERSION,
            "external jet ABI version mismatch"
        );
    });
    &EXTERNAL_JET_WASM_LIB
}

// Imports supplied by the embedder when this wasm module is instantiated.
//
// The `simplicityhl-plugin` module must provide functions with these exact C
// ABI signatures. The imported functions exchange only scalar values and bytes
// in caller-owned buffers; no Rust-layout values cross the module boundary.
#[link(wasm_import_module = "simplicityhl-plugin")]
extern "C" {
    fn external_jet_abi_version() -> u32;
    fn cmr(index: u64, out_ptr: *mut u8, cap: usize) -> i32;
    fn source_ty(index: u64, out_ptr: *mut u8, cap: usize) -> i32;
    fn target_ty(index: u64, out_ptr: *mut u8, cap: usize) -> i32;
    fn encode(index: u64, out_ptr: *mut u8, cap: usize) -> i32;
    fn cost(index: u64, out_ptr: *mut u8, cap: usize) -> i32;
    fn display(index: u64, out_ptr: *mut u8, cap: usize) -> i32;
    fn source_jet_classification(index: u64, out_ptr: *mut u8, cap: usize) -> i32;
    fn target_jet_classification(index: u64, out_ptr: *mut u8, cap: usize) -> i32;

    fn parse(name_ptr: *const u8, name_len: usize, out_index: *mut u64) -> i32;
    fn is_disabled(index: u64) -> i32;
    fn verify() -> u64;
}

/// Call a `(index, out_ptr, cap) -> i32` plugin shim, growing the buffer as
/// needed, and return the exact bytes the plugin produced.
fn read_shim<F: Fn(*mut u8, usize) -> i32>(call: F) -> Option<Vec<u8>> {
    const INITIAL_CAP: usize = 128;
    let mut buf = vec![0u8; INITIAL_CAP];
    let needed = call(buf.as_mut_ptr(), buf.len());
    if needed < 0 {
        return None;
    }
    let needed = usize::try_from(needed).ok()?;
    if needed > buf.len() {
        buf = vec![0u8; needed];
        let again = call(buf.as_mut_ptr(), buf.len());
        if usize::try_from(again).ok()? != needed {
            return None;
        }
    }
    buf.truncate(needed);
    Some(buf)
}

/// Intern plugin-provided [`TypeName`] bytes to obtain the `'static` slice that
/// [`TypeName`] requires.
///
/// The bytes originate in the plugin's memory and are copied into ours on every
/// call, so they are not `'static` on their own. We leak a single copy per
/// distinct byte string (jets expose only a handful of type names) and reuse it
/// forever, which keeps the leak bounded to the set of type names in use.
fn intern_type_name(bytes: &[u8]) -> TypeName {
    static INTERNER: OnceLock<Mutex<HashSet<&'static [u8]>>> = OnceLock::new();
    let interner = INTERNER.get_or_init(|| Mutex::new(HashSet::new()));
    let mut guard = interner.lock().expect("type-name interner poisoned");
    if let Some(existing) = guard.get(bytes) {
        return TypeName(existing);
    }
    let leaked: &'static [u8] = Box::leak(bytes.to_vec().into_boxed_slice());
    guard.insert(leaked);
    TypeName(leaked)
}

impl ExternalJetLib for ExternalJetWasmLib {
    fn cmr(&self, jet: ExternalJet) -> Cmr {
        let mut bytes = [0u8; 32];
        let status = unsafe { cmr(jet.index, bytes.as_mut_ptr(), bytes.len()) };
        assert_eq!(status, 32, "plugin cmr must return exactly 32 bytes");
        Cmr::from_byte_array(bytes)
    }

    fn source_ty(&self, jet: ExternalJet) -> TypeName {
        let bytes = read_shim(|ptr, cap| unsafe { source_ty(jet.index, ptr, cap) })
            .expect("plugin source_ty failed");
        intern_type_name(&bytes)
    }

    fn target_ty(&self, jet: ExternalJet) -> TypeName {
        let bytes = read_shim(|ptr, cap| unsafe { target_ty(jet.index, ptr, cap) })
            .expect("plugin target_ty failed");
        intern_type_name(&bytes)
    }

    fn encode(
        &self,
        jet: ExternalJet,
        w: &mut BitWriter<&mut dyn Write>,
    ) -> std::io::Result<usize> {
        let mut buf = [0u8; 64];
        let n_bits = unsafe { encode(jet.index, buf.as_mut_ptr(), buf.len()) };
        if n_bits < 0 {
            return Err(std::io::Error::other("external jet encode failed"));
        }
        let n_bits = usize::try_from(n_bits).expect("non-negative i32 fits in usize");
        let n_bytes = n_bits.div_ceil(8);
        if n_bytes > buf.len() {
            return Err(std::io::Error::other(
                "external jet encode output exceeds buffer",
            ));
        }
        // Replay the packed, MSB-first bit buffer into the real writer.
        let full = n_bits / 8;
        let rem = n_bits % 8;
        for &byte in &buf[..full] {
            w.write_bits_be(u64::from(byte), 8)?;
        }
        if rem > 0 {
            let last = u64::from(buf[full] >> (8 - rem));
            w.write_bits_be(last, rem)?;
        }
        Ok(n_bits)
    }

    fn cost(&self, jet: ExternalJet) -> Cost {
        let bytes =
            read_shim(|ptr, cap| unsafe { cost(jet.index, ptr, cap) }).expect("plugin cost failed");
        let milliweight = std::str::from_utf8(&bytes)
            .expect("plugin cost returned invalid UTF-8")
            .parse()
            .expect("plugin cost returned an invalid milliweight value");
        Cost::from_milliweight(milliweight)
    }

    fn parse(&self, s: &str) -> Result<ExternalJet, simplicity::Error> {
        let mut index = 0;
        let status = unsafe { parse(s.as_ptr(), s.len(), &mut index) };
        if status == 0 {
            Ok(ExternalJet::new(index))
        } else {
            Err(simplicity::Error::InvalidJetName(s.to_owned()))
        }
    }

    fn display(&self, jet: ExternalJet) -> String {
        let bytes = read_shim(|ptr, cap| unsafe { display(jet.index, ptr, cap) })
            .expect("plugin display failed");
        String::from_utf8(bytes).expect("plugin display returned invalid UTF-8")
    }

    fn source_jet_classification(&self, jet: ExternalJet) -> SourceJetClassification {
        let bytes = read_shim(|ptr, cap| unsafe { source_jet_classification(jet.index, ptr, cap) })
            .expect("plugin source_jet_classification failed");
        deserialize_source_jet_classification(&bytes)
            .expect("plugin returned malformed source jet classification")
    }

    fn target_jet_classification(&self, jet: ExternalJet) -> TargetJetClassification {
        let bytes = read_shim(|ptr, cap| unsafe { target_jet_classification(jet.index, ptr, cap) })
            .expect("plugin target_jet_classification failed");
        deserialize_target_jet_classification(&bytes)
            .expect("plugin returned malformed target jet classification")
    }

    fn is_disabled(&self, jet: ExternalJet) -> bool {
        unsafe { is_disabled(jet.index) != 0 }
    }

    fn verify(&self) -> ExternalJet {
        ExternalJet::new(unsafe { verify() })
    }

    fn conjure(&self, jet: &dyn Jet) -> Option<Box<dyn JetHL>> {
        jet.as_any()
            .downcast_ref::<ExternalJet>()
            .map(|jet| Box::new(*jet) as Box<dyn JetHL>)
    }
}
