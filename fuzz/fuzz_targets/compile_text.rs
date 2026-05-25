#![cfg_attr(fuzzing, no_main)]

/// The PEST parser is slow for inputs with many open brackets.
/// Detect some of these inputs to reject them from the corpus.
///
/// ```text
/// fn n(){ { (s,(( (Ns,(s,(x,(((s,((s,(s,(s,(x,(( {5
/// ```
#[cfg(any(fuzzing, test))]
fn slow_input(program_text: &str) -> bool {
    let mut consecutive_open_brackets = 0;

    for c in program_text.chars() {
        if c == '(' || c == '[' || c == '{' {
            consecutive_open_brackets += 1;
            if consecutive_open_brackets > 3 {
                return true;
            }
        } else if !c.is_whitespace() {
            consecutive_open_brackets = 0;
        }
    }

    false
}

#[cfg(any(fuzzing, test))]
fn do_test(data: &[u8]) -> libfuzzer_sys::Corpus {
    use arbitrary::Arbitrary;
    use libfuzzer_sys::Corpus;
    use simplicityhl::ast::ElementsJetHinter;
    use simplicityhl::{ArbitraryOfType, Arguments};

    let mut u = arbitrary::Unstructured::new(data);

    let program_text = match <String>::arbitrary(&mut u) {
        Ok(x) => x,
        Err(..) => return Corpus::Reject,
    };
    if slow_input(&program_text) {
        return Corpus::Reject;
    }
    let template = match simplicityhl::TemplateProgram::new(
        program_text,
        Box::new(ElementsJetHinter::new()),
    ) {
        Ok(x) => x,
        Err(..) => return Corpus::Keep,
    };
    let arguments = match Arguments::arbitrary_of_type(&mut u, template.parameters()) {
        Ok(arguments) => arguments,
        Err(..) => return Corpus::Reject,
    };
    let _ = template.instantiate(arguments, false);

    Corpus::Keep
}

#[cfg(fuzzing)]
libfuzzer_sys::fuzz_target!(|data: &[u8]| {
    let _ = do_test(data);
});

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
