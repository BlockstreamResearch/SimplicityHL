//! WebAssembly entrypoint that compiles a tiny program using external jets.
//!
//! This binary is intended to be compiled for `wasm32-unknown-unknown` and
//! instantiated by JavaScript with imports from the plugin wasm module under
//! the import module name `simplicityhl-plugin`.

use simplicityhl::ast::JetHinter;
#[cfg(target_arch = "wasm32")]
use simplicityhl::jet::external::init_external_jet_lib;
use simplicityhl::jet::external::ExternalJetHinter;
use simplicityhl::jet::{SourceJetClassification, TargetJetClassification};
use simplicityhl::simplicity::jet::Jet;
use simplicityhl::simplicity::{BitWriter, Cost};
use simplicityhl::TemplateProgram;
use std::io::Write;
use std::sync::{Mutex, OnceLock};

static LAST_ERROR: OnceLock<Mutex<String>> = OnceLock::new();

fn last_error_store() -> &'static Mutex<String> {
    LAST_ERROR.get_or_init(|| Mutex::new(String::new()))
}

fn set_last_error(msg: impl Into<String>) {
    if let Ok(mut err) = last_error_store().lock() {
        *err = msg.into();
    }
}

fn clear_last_error() {
    set_last_error("");
}

/// Ensure the external jet backend is initialized for this wasm instance.
#[cfg(target_arch = "wasm32")]
fn ensure_external_backend_initialized() -> Result<(), String> {
    match unsafe { init_external_jet_lib() } {
        Ok(()) => Ok(()),
        Err(err) => {
            let msg = err.to_string();
            if msg.contains("already been initialized") {
                Ok(())
            } else {
                Err(msg)
            }
        }
    }
}

#[cfg(not(target_arch = "wasm32"))]
fn ensure_external_backend_initialized() -> Result<(), String> {
    Err("compiler-wasm backend initialization is only supported on wasm32".to_owned())
}

#[no_mangle]
pub extern "C" fn last_error_ptr() -> *const u8 {
    let guard = last_error_store()
        .lock()
        .expect("last error mutex poisoned unexpectedly");
    guard.as_ptr()
}

#[no_mangle]
pub extern "C" fn last_error_len() -> usize {
    let guard = last_error_store()
        .lock()
        .expect("last error mutex poisoned unexpectedly");
    guard.len()
}

/// Compile a program that lowers to the plugin-provided `verify` jet.
///
/// Returns:
/// - `0` on success
/// - `1` if initializing the external jet backend fails
/// - `2` if compilation fails
#[no_mangle]
pub extern "C" fn compile_happyjet() -> i32 {
    clear_last_error();
    if let Err(err) = ensure_external_backend_initialized() {
        set_last_error(format!("failed to initialize external jet backend: {err}"));
        return 1;
    }

    let code = r#"fn main() {
    assert!(true);
}"#;

    match TemplateProgram::new(code, Box::new(ExternalJetHinter::new())) {
        Ok(_) => 0,
        Err(e) => {
            set_last_error(e.to_string());
            2
        }
    }
}

/// Invoke every plugin entry point across the wasm module boundary and
/// validate the results against `HappyJet`'s known values.
#[no_mangle]
pub extern "C" fn probe_external_jet() -> i32 {
    clear_last_error();
    if let Err(err) = ensure_external_backend_initialized() {
        set_last_error(format!("failed to initialize external jet backend: {err}"));
        return 1;
    }

    let hinter = ExternalJetHinter::new();

    // `parse` (bridged): a known name resolves, an unknown name does not.
    let Some(jet) = hinter.parse_jet("verify") else {
        set_last_error("parse_jet(\"verify\") returned None");
        return 1;
    };
    if hinter.parse_jet("no_such_jet").is_some() {
        set_last_error("parse_jet(\"no_such_jet\") unexpectedly returned Some");
        return 2;
    }

    let low: &dyn Jet = jet.as_jet();

    // `cmr` shim: fixed 32-byte identity.
    const EXPECTED_CMR: [u8; 32] = [
        0xcd, 0xca, 0x2a, 0x05, 0xe5, 0x2c, 0xef, 0xa5, 0x9d, 0xc7, 0xa5, 0xb0, 0xda, 0xe2, 0x20,
        0x98, 0xfb, 0x89, 0x6e, 0x39, 0x13, 0xbf, 0xdd, 0x44, 0x6b, 0x59, 0x4e, 0x1f, 0x92, 0x50,
        0x78, 0x3e,
    ];
    if low.cmr().to_byte_array() != EXPECTED_CMR {
        set_last_error("cmr mismatch across module boundary");
        return 3;
    }

    // `source_ty` / `target_ty` shims: Polish-notation type-name bytes.
    if low.source_ty().0 != b"2".as_slice() {
        set_last_error("source_ty mismatch across module boundary");
        return 4;
    }
    if low.target_ty().0 != b"1".as_slice() {
        set_last_error("target_ty mismatch across module boundary");
        return 5;
    }

    // `cost` (scalar): unchanged, but validated for completeness.
    if low.cost() != Cost::from_milliweight(44) {
        set_last_error("cost mismatch across module boundary");
        return 6;
    }

    // `display` shim: the jet's textual name. `dyn Jet: Display`.
    if low.to_string() != "verify" {
        set_last_error(format!("display mismatch: got {:?}", low.to_string()));
        return 7;
    }

    // Classification shims: heap-backed enums serialized through the shared
    // wire format.
    match jet.source_jet_classification() {
        SourceJetClassification::Custom(types)
            if types.len() == 1 && types[0] == simplicityhl::jet::bool() => {}
        other => {
            set_last_error(format!("source classification mismatch: {other:?}"));
            return 8;
        }
    }
    match jet.target_jet_classification() {
        TargetJetClassification::Unary => {}
        other => {
            set_last_error(format!("target classification mismatch: {other:?}"));
            return 9;
        }
    }

    // `is_disabled` (scalar).
    if jet.is_disabled() {
        set_last_error("is_disabled should be false");
        return 10;
    }

    // `encode` shim: the packed jet code, replayed into a real BitWriter.
    let mut encoded: Vec<u8> = Vec::new();
    let n_bits = {
        let sink: &mut dyn Write = &mut encoded;
        let mut writer: BitWriter<&mut dyn Write> = BitWriter::new(sink);
        let Ok(n_bits) = low.encode(&mut writer) else {
            set_last_error("encode failed across module boundary");
            return 11;
        };
        if writer.flush_all().is_err() {
            set_last_error("flushing encoded bits failed");
            return 11;
        }
        n_bits
    };
    // `verify` encodes to the single bit `0`, i.e. one byte `0x00`.
    if n_bits != 1 || encoded != [0u8] {
        set_last_error(format!("encode mismatch: {n_bits} bits, bytes {encoded:?}"));
        return 12;
    }

    0
}

fn main() {}
