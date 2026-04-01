#![cfg_attr(fuzzing, no_main)]

#[cfg(any(fuzzing, test))]
fn do_test(data: &[u8]) {
    use arbitrary::Arbitrary;

    use simplicityhl::error::WithContent;
    use simplicityhl::{ast, named, parse, ArbitraryOfType, Arguments};

    let mut u = arbitrary::Unstructured::new(data);
    let parse_program = match parse::Program::arbitrary(&mut u) {
        Ok(x) => x,
        Err(_) => return,
    };
    let ast_program = match ast::Program::analyze(&parse_program) {
        Ok(x) => x,
        Err(_) => return,
    };
    let arguments = match Arguments::arbitrary_of_type(&mut u, ast_program.parameters()) {
        Ok(arguments) => arguments,
        Err(..) => return,
    };
    let simplicity_named_construct = ast_program
        .compile(arguments, false)
        .with_content("")
        .expect("AST should compile with given arguments");
    let _simplicity_commit = named::forget_names(&simplicity_named_construct);
}

#[cfg(fuzzing)]
libfuzzer_sys::fuzz_target!(|data| do_test(data));

#[cfg(not(fuzzing))]
fn main() {}

#[cfg(test)]
mod tests {
    use base64::Engine;

    #[test]
    fn duplicate_crash() {
        let data = base64::prelude::BASE64_STANDARD
            .decode("Cg==")
            .expect("base64 should be valid");
        super::do_test(&data);
    }
}
