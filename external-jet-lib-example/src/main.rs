use simplicityhl::{jet::external::ExternalJetHinter, TemplateProgram};

fn main() {
    let lib_path = std::env::args().nth(1).expect(
        "Please provide the path to the compiled external jet library as the first argument",
    );

    unsafe {
        simplicityhl::jet::external::init_external_jet_lib(&lib_path)
            .expect("failed to initialize external jet lib");
    }

    let code = r#"fn main() {
    assert!(true);
}"#;

    let _ = TemplateProgram::new(code, Box::new(ExternalJetHinter::new()))
        .expect("failed to compile code with external jets");

    println!("External jets were successfully used to compile:\n{}", code);
}
