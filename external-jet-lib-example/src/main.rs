//! Minimal *consumer* of the external jet library.
//!
//! This binary plays the role of a host SimplicityHL application that wants to
//! compile programs against a jet set supplied by a *separately compiled* shared
//! library. It demonstrates the full runtime lifecycle: load the library,
//! register it globally, then compile a program whose jets are resolved through
//! it.
//!
//! Run it with the path to the compiled library as the first argument:
//!
//! ```sh
//! cargo run -p external-jet-lib-example --bin external-lib-consumer -- \
//!     target/debug/libexternal_jet_lib_example.dylib
//! ```
//!
//! # Safety
//!
//! [`init_external_jet_lib`](simplicityhl::jet::external::init_external_jet_lib)
//! loads and runs native code from the given path. Only point it at libraries
//! you trust.

use simplicityhl::{jet::external::ExternalJetHinter, TemplateProgram};

/// Loads the external jet library named on the command line and compiles a tiny
/// SimplicityHL program against it.
fn main() {
    // 1. The path to the compiled `.so` / `.dylib` / `.dll` is taken from argv.
    let lib_path = std::env::args().nth(1).expect(
        "Please provide the path to the compiled external jet library as the first argument",
    );

    // 2. `dlopen` the library and resolve all of its `#[no_mangle]` exports into
    //    the process-global `ExternalJetLib` table. This must happen exactly once
    //    and before any program that uses external jets is compiled.
    unsafe {
        simplicityhl::jet::external::init_external_jet_lib(&lib_path)
            .expect("failed to initialize external jet lib");
    }

    let code = r#"fn main() {
    assert!(true);
}"#;

    // 3. Compile the program. `ExternalJetHinter` routes every jet lookup
    //    (`parse_jet`, `construct_verify`, `conjure`) to the loaded library; here
    //    `assert!(true)` is lowered via `construct_verify` to the library's
    //    `verify` jet.
    let _ = TemplateProgram::new(code, Box::new(ExternalJetHinter::new()))
        .expect("failed to compile code with external jets");

    println!("External jets were successfully used to compile:\n{}", code);
}
