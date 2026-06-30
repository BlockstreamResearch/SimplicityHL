//! WebAssembly entrypoint that compiles a tiny program using external jets.
//!
//! This binary is intended to be compiled for `wasm32-unknown-unknown` and
//! instantiated by JavaScript with imports from the plugin wasm module under
//! the import module name `simplicityhl-plugin`.

use simplicityhl::{jet::external::ExternalJetHinter, TemplateProgram};
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
    if unsafe { simplicityhl::jet::external::init_external_jet_lib(None) }.is_err() {
        set_last_error("failed to initialize external jet backend");
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

fn main() {}
