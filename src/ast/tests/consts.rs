use super::analyze;

#[test]
fn const_with_reported_error_is_not_evaluated() {
    for src in [
        "const A: List<u8, 2> = list![1, 2]; fn main() {}",
        "const A: [u8; 2] = [1, 2, 3]; fn main() { let _: [u8; 2] = A; }",
    ] {
        let err = analyze(src).unwrap_err();
        assert!(err.contains("found something else"), "{err}");
        assert!(!err.contains("found type"), "{err}");
    }
}

#[test]
fn const_of_type_with_broken_alias_is_not_evaluated() {
    let err = analyze(
        "type Bad = Missing;
        const A: List<Option<Bad>, 2> = list![None, None];
        fn main() {}",
    )
    .unwrap_err();
    assert!(err.contains("Missing"), "{err}");
}

#[test]
fn every_binding_rejects_a_constant_name() {
    for src in [
        "const A: u8 = 1;
        fn f(A: u8) {}
        fn main() {}",
        "const A: u8 = 1;
        fn main() {
            let e: Either<u8, u8> = Left(2);
            match e { Left(A: u8) => {}, Right(_: u8) => {} };
        }",
    ] {
        let err = analyze(src).unwrap_err();
        assert!(err.contains("cannot shadow a constant"), "{err}");
    }
}
