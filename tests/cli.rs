use std::path::{Path, PathBuf};
use std::process::Command;

fn repo_path(path: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(path)
}

#[test]
fn cli_dependency_can_use_crate_root() {
    let root = repo_path("functional-tests/valid-test-cases/external-library-uses-crate");
    let main = root.join("main.simf");
    let ext_lib = root.join("ext_lib");
    let dep_arg = format!("{}:ext_lib={}", root.display(), ext_lib.display());

    let output = Command::new(env!("CARGO_BIN_EXE_simc"))
        .arg(main)
        .arg("--dep")
        .arg(dep_arg)
        .output()
        .expect("failed to run simc");

    assert!(
        output.status.success(),
        "simc failed\nstatus: {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}
