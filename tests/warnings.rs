use simplicityhl::warning::WarningName;
use simplicityhl::{TemplateProgram, WarnCategory};

fn warning_names(prog_text: &str) -> Vec<WarningName> {
    TemplateProgram::new(prog_text)
        .expect("Program should compile")
        .warnings()
        .iter()
        .map(|w| w.canonical_name.clone())
        .collect()
}

#[test]
fn unused_variable_warns() {
    let prog = r#"fn main() {
    let (carry, sum): (bool, u8) = jet::add_8(2, 3);
    assert!(jet::eq_8(sum, 5))
}"#;
    let names = warning_names(prog);
    assert_eq!(names.len(), 1);
    assert!(
        matches!(&names[0], WarningName::UnusedVariable(id) if id.as_inner() == "carry"),
        "Expected VariableUnused(carry), got: {:?}",
        names,
    );
}

#[test]
fn used_variable_no_warning() {
    // Both carry and sum are used in the tuple expression.
    let prog = r#"fn main() {
    let (carry, sum): (bool, u8) = jet::add_8(2, 3);
    let _: (bool, u8) = (carry, sum);
}"#;
    assert!(warning_names(prog).is_empty());
}

#[test]
fn underscore_prefix_silences_warning() {
    let prog = r#"fn main() {
    let (_carry, sum): (bool, u8) = jet::add_8(2, 3);
    assert!(jet::eq_8(sum, 5))
}"#;
    assert!(warning_names(prog).is_empty());
}

#[test]
fn ignore_pattern_no_warning() {
    let prog = r#"fn main() {
    let (_, sum): (bool, u8) = jet::add_8(2, 3);
    assert!(jet::eq_8(sum, 5))
}"#;
    assert!(warning_names(prog).is_empty());
}

#[test]
fn multiple_unused_variables_warn() {
    let prog = r#"fn main() {
    let x: u8 = 1;
    let y: u8 = 2;
    assert!(jet::eq_8(0, 0))
}"#;
    let names = warning_names(prog);
    let unused: Vec<&str> = names
        .iter()
        .map(|w| match w {
            WarningName::UnusedVariable(id) => id.as_inner(),
        })
        .collect();
    assert_eq!(
        unused.len(),
        2,
        "Expected 2 unused-variable warnings, got: {unused:?}"
    );
    // Warnings are emitted in source order (sorted by span start).
    assert_eq!(unused, ["x", "y"]);
}

#[test]
fn variable_used_in_nested_block_no_warning() {
    let prog = r#"fn main() {
    let x: u8 = 1;
    let y: u8 = {
        x
    };
    assert!(jet::eq_8(y, 1))
}"#;
    assert!(warning_names(prog).is_empty());
}

#[test]
fn deny_unused_variable_is_error() {
    let prog = r#"fn main() {
    let (carry, sum): (bool, u8) = jet::add_8(2, 3);
    assert!(jet::eq_8(sum, 5))
}"#;
    assert!(
        TemplateProgram::new(prog).unwrap().deny_warnings().is_err(),
        "Expected compilation to fail with --deny-warnings",
    );
}

#[test]
fn unused_match_arm_binding_warns() {
    let prog = r#"fn main() {
    let val: Either<u32, bool> = Left(42);
    match val {
        Left(x: u32) => assert!(jet::eq_32(0, 0)),
        Right(_: bool) => assert!(jet::eq_32(0, 0)),
    }
}"#;
    let names = warning_names(prog);
    assert_eq!(names.len(), 1);
    assert!(
        matches!(&names[0], WarningName::UnusedVariable(id) if id.as_inner() == "x"),
        "Expected VariableUnused(x), got: {:?}",
        names,
    );
}

#[test]
fn used_match_arm_binding_no_warning() {
    let prog = r#"fn main() {
    let val: Either<u32, bool> = Left(42);
    match val {
        Left(x: u32) => assert!(jet::eq_32(x, 42)),
        Right(_: bool) => assert!(jet::eq_32(0, 0)),
    }
}"#;
    assert!(warning_names(prog).is_empty());
}

#[test]
fn underscore_prefix_silences_match_arm_warning() {
    let prog = r#"fn main() {
    let val: Either<u32, bool> = Left(42);
    match val {
        Left(_x: u32) => assert!(jet::eq_32(0, 0)),
        Right(_: bool) => assert!(jet::eq_32(0, 0)),
    }
}"#;
    assert!(warning_names(prog).is_empty());
}

#[test]
fn unused_function_param_warns() {
    let prog = r#"fn always_zero(x: u32) -> u32 {
    0
}

fn main() {
    assert!(jet::eq_32(always_zero(42), 0))
}"#;
    let names = warning_names(prog);
    assert_eq!(names.len(), 1);
    assert!(
        matches!(&names[0], WarningName::UnusedVariable(id) if id.as_inner() == "x"),
        "Expected VariableUnused(x), got: {:?}",
        names,
    );
}

#[test]
fn used_function_param_no_warning() {
    let prog = r#"fn identity(x: u32) -> u32 {
    x
}

fn main() {
    assert!(jet::eq_32(identity(42), 42))
}"#;
    assert!(warning_names(prog).is_empty());
}

#[test]
fn shadowed_outer_variable_unused_warns() {
    // Outer `x` is never referenced; inner `x` shadows it and is used.
    // Only the outer binding should warn.
    let prog = r#"fn main() {
    let x: u8 = 1;
    let y: u8 = {
        let x: u8 = 2;
        x
    };
    assert!(jet::eq_8(y, 2))
}"#;
    let names = warning_names(prog);
    assert_eq!(
        names.len(),
        1,
        "Expected exactly one warning (outer x), got: {names:?}",
    );
    assert!(
        matches!(&names[0], WarningName::UnusedVariable(id) if id.as_inner() == "x"),
        "Expected UnusedVariable(x) for the outer binding, got: {:?}",
        names,
    );
}

#[test]
fn shadowed_inner_variable_unused_warns() {
    // Outer `x` is used as the RHS of the inner binding.
    // Inner `x` is never referenced after being bound, so it should warn.
    let prog = r#"fn main() {
    let x: u8 = 1;
    let y: u8 = {
        let x: u8 = x;
        0
    };
    assert!(jet::eq_8(y, 0))
}"#;
    let names = warning_names(prog);
    assert_eq!(
        names.len(),
        1,
        "Expected exactly one warning (inner x), got: {names:?}",
    );
    assert!(
        matches!(&names[0], WarningName::UnusedVariable(id) if id.as_inner() == "x"),
        "Expected UnusedVariable(x) for the inner binding, got: {:?}",
        names,
    );
}

#[test]
fn outer_variable_used_after_inner_scope_no_warning() {
    // `x` is bound in the outer scope, referenced after an inner block
    // that binds a different name. Neither binding should warn.
    let prog = r#"fn main() {
    let x: u8 = 1;
    let y: u8 = {
        let z: u8 = 2;
        z
    };
    let (_, sum): (bool, u8) = jet::add_8(x, y);
    assert!(jet::eq_8(sum, 3))
}"#;
    assert!(
        warning_names(prog).is_empty(),
        "Expected no warnings when all variables are used",
    );
}

#[test]
fn deny_warning_by_category_is_error() {
    let prog = r#"fn main() {
    let (carry, sum): (bool, u8) = jet::add_8(2, 3);
    assert!(jet::eq_8(sum, 5))
}"#;
    assert!(
        TemplateProgram::new(prog)
            .unwrap()
            .deny_warning(WarnCategory::UnusedVariable)
            .is_err(),
        "deny_warning(UnusedVariable) should fail when there is an unused variable",
    );
}

#[test]
fn allow_warning_by_category_suppresses_it() {
    let prog = r#"fn main() {
    let (carry, sum): (bool, u8) = jet::add_8(2, 3);
    assert!(jet::eq_8(sum, 5))
}"#;
    let template = TemplateProgram::new(prog)
        .unwrap()
        .allow_warning(WarnCategory::UnusedVariable);
    assert!(
        template.warnings().is_empty(),
        "allow_warning(UnusedVariable) should remove the warning",
    );
}
