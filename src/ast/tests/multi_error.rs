use crate::test_utils::assert_errors;

#[test]
fn tuple_elements() {
    assert_errors(
        "fn main() { let pair: (u32, u32) = (x, y); }",
        &["Variable `x` is not defined", "Variable `y` is not defined"],
    );
}

#[test]
fn array_length_and_elements() {
    assert_errors(
        "fn main() { let array: [u32; 3] = [x, y]; }",
        &[
            "Expected expression of type `[u32; 3]`; found something else",
            "Variable `x` is not defined",
            "Variable `y` is not defined",
        ],
    );
}

#[test]
fn call_output_type_and_arguments() {
    assert_errors(
        "fn main() { let sum: bool = jet::add_32(a, b); }",
        &[
            "Expected expression of type `bool`, found type `(bool, u32)`",
            "Variable `a` is not defined",
            "Variable `b` is not defined",
        ],
    );
}

#[test]
fn nested_errors_are_reported_once() {
    assert_errors(
        "fn main() { let pair: (u32, u32) = (jet::add_32(a, 1), b); }",
        &[
            "Expected expression of type `u32`, found type `(bool, u32)`",
            "Variable `a` is not defined",
            "Variable `b` is not defined",
        ],
    );
}

#[test]
fn match_arms() {
    assert_errors(
        "fn main() {
                let input: Either<u32, u32> = Left(1);
                let result: u32 = match input {
                    Left(l: u32) => left_var,
                    Right(r: u32) => right_var,
                };
            }",
        &[
            "Variable `left_var` is not defined",
            "Variable `right_var` is not defined",
        ],
    );
}

#[test]
fn enum_match_misspelled_variants_are_not_reported_as_missing() {
    assert_errors(
        "enum Color { Red, Green, Blue }
            fn main() {
                let c: Color = Color::Red;
                match c {
                    Color::Rd => {},
                    Color::Gren => {},
                    Color::Blue => {},
                }
            }",
        &[
            "Grammar error: variant 'Rd' is not defined in enum 'Color'",
            "Grammar error: variant 'Gren' is not defined in enum 'Color'",
        ],
    );
}

#[test]
fn enum_match_arms() {
    assert_errors(
        "enum Color { Red, Green }
            fn main() {
                let c: Color = Color::Red;
                let n: u32 = match c {
                    Color::Red => x,
                    Color::Green => y,
                };
            }",
        &["Variable `x` is not defined", "Variable `y` is not defined"],
    );
}

#[test]
fn main_visibility_and_inputs() {
    // The body is not analyzed: it could use the parameters,
    // which would only repeat the error about inputs.
    assert_errors(
        "pub fn main(a: u32) -> u32 { undefined }",
        &[
            "Main function cannot be public",
            "Main function takes no input parameters",
        ],
    );
}

#[test]
fn main_visibility_and_body() {
    assert_errors(
        "pub fn main() { let a: u32 = undefined; }",
        &[
            "Main function cannot be public",
            "Variable `undefined` is not defined",
        ],
    );
}

#[test]
fn enum_duplicate_variants() {
    assert_errors(
        "enum Color { Red, Red, Green, Green }
            fn main() {}",
        &[
            "Grammar error: enum 'Color' has duplicate variant name 'Red'",
            "Grammar error: enum 'Color' has duplicate variant name 'Green'",
        ],
    );
}

#[test]
fn enum_payload_types() {
    assert_errors(
        "enum Shape { Circle(Radius), Square(Side) }
            fn main() {}",
        &[
            "Type alias `Radius` is not defined",
            "Type alias `Side` is not defined",
        ],
    );
}

#[test]
fn failed_check_does_not_stop_the_next_statement() {
    assert_errors(
        "fn main() {
                let b: bool = jet::add_32(1, 2);
                let c: u32 = z;
            }",
        &[
            "Expected expression of type `bool`, found type `(bool, u32)`",
            "Variable `z` is not defined",
        ],
    );
}

#[test]
fn every_broken_function_is_reported() {
    assert_errors(
        "fn a() -> u32 { x }
            fn b() -> u32 { y }
            fn main() {}",
        &["Variable `x` is not defined", "Variable `y` is not defined"],
    );
}

#[test]
fn wrong_call_of_function_with_broken_body_is_reported() {
    assert_errors(
        "fn f(a: u32) -> u32 { x }
            fn main() { let y: bool = f(true); }",
        &[
            "Variable `x` is not defined",
            "Expected expression of type `bool`, found type `u32`",
            "Expected expression of type `u32`, found type `bool`",
        ],
    );
}

#[test]
fn function_with_broken_body_can_still_be_folded() {
    assert_errors(
        "fn add(element: u32, acc: u32) -> u32 { x }
            fn main() {
                let array: [u32; 3] = [1, 2, 3];
                let sum: u32 = array_fold::<add, 3>(array, 0);
            }",
        &["Variable `x` is not defined"],
    );
}

#[test]
fn function_with_broken_body_can_still_be_imported() {
    assert_errors(
        "mod m { pub fn f() -> u32 { x } }
            use crate::m::f;
            fn main() { let y: u32 = f(); }",
        &["Variable `x` is not defined"],
    );
}

#[test]
fn broken_function_in_module_does_not_stop_the_next_item() {
    assert_errors(
        "mod m { fn f() -> u32 { x } }
            fn g() -> u32 { y }
            fn main() {}",
        &["Variable `x` is not defined", "Variable `y` is not defined"],
    );
}

#[test]
fn broken_main_does_not_stop_the_next_item() {
    assert_errors(
        "fn main() { let a: u32 = x; }
            fn g() -> u32 { y }",
        &["Variable `x` is not defined", "Variable `y` is not defined"],
    );
}

#[test]
fn missing_main_is_reported_with_other_errors() {
    assert_errors(
        "fn f() -> u32 { x }",
        &["Main function is required", "Variable `x` is not defined"],
    );
}

#[test]
fn broken_main_in_module_does_not_stop_the_next_item() {
    assert_errors(
        "mod entry { fn main() { let x: u32 = missing; } }
            fn later() -> u32 { later_missing }",
        &[
            "Variable `missing` is not defined",
            "Variable `later_missing` is not defined",
        ],
    );
}

#[test]
fn broken_main_in_nested_module_does_not_stop_the_next_item() {
    assert_errors(
        "mod outer {
                mod inner { fn main() { let x: u32 = missing; } }
                fn sibling() -> u32 { sibling_missing }
            }
            fn later() -> u32 { later_missing }",
        &[
            "Variable `missing` is not defined",
            "Variable `sibling_missing` is not defined",
            "Variable `later_missing` is not defined",
        ],
    );
}

#[test]
fn undefined_types_are_reported_once() {
    assert_errors(
        "type Alias = Missing;
            fn f(a: Alias) -> Alias { a }
            fn g(a: Undefined) -> Unknown { a }
            fn h() -> u32 { y }

            fn main() { let x: u32 = f(1); }",
        &[
            "Type alias `Missing` is not defined",
            "Type alias `Undefined` is not defined",
            "Type alias `Unknown` is not defined",
            "Variable `y` is not defined",
        ],
    );
}

#[test]
fn broken_parameter_does_not_hide_other_errors() {
    assert_errors(
        "fn f(a: Missing, b: u32) -> u32 { b }
            fn main() {
                let t: bool = true;
                let y: u32 = f((1, x), t);
            }",
        &[
            "Type alias `Missing` is not defined",
            "Variable `x` is not defined",
            "Expected expression of type `u32`, found type `bool`",
        ],
    );
}

#[test]
fn broken_enum_payload_does_not_hide_the_enum() {
    assert_errors(
        "enum E { A(Missing), B }
            fn main() {
                let e: E = E::B;
                let n: u32 = match e {
                    E::A(a: u32) => a,
                    E::B => x,
                };
            }",
        &[
            "Type alias `Missing` is not defined",
            "Variable `x` is not defined",
        ],
    );
}

#[test]
fn parameter_ignores_uses_of_broken_types() {
    assert_errors(
        "type Alias = Missing;
            fn main() {
                let a: Alias = param::X;
                let b: u32 = param::X;
                let c: bool = param::X;
            }",
        &[
            "Type alias `Missing` is not defined",
            "Expected expression of type `u32`, found type `bool`",
        ],
    );
}

#[test]
fn cast_of_enum_with_broken_payload() {
    assert_errors(
        "enum E { A(Missing), B }
            enum F { A(u8), B }
            fn different(e: E) -> F { <E>::into(e) }
            fn same(e: E) -> Option<E> { <Option<E>>::into(Some(e)) }

            fn main() {}",
        &[
            "Type alias `Missing` is not defined",
            "Cannot cast values of type `E` as values of type `F`",
        ],
    );
}

#[test]
fn constant_of_broken_type_is_rejected() {
    use crate::parse::{self, ParseFromStr};
    use crate::types::{ResolvedType, TypeConstructible};

    let never = ResolvedType::never();
    let option_never = ResolvedType::option(never.clone());

    for (source, ty) in [
        ("5", never),
        ("5", option_never.clone()),
        ("[None, None]", ResolvedType::array(option_never, 3)),
    ] {
        let parsed = parse::Expression::parse_from_str(source).expect("value parses");
        assert!(crate::ast::Expression::analyze_const(&parsed, &ty).is_err());
    }
}

#[test]
fn construction_through_broken_enum_alias() {
    assert_errors(
        "type Bad = Missing;
            enum Color { Red, Green }

            fn unknown_variant() -> Color { Bad::Blue }
            fn payload_count() -> Color { Bad::Red(x) }
            fn mixed_arms(c: Color) {
                match c {
                    Color::Red => {},
                    Bad::Green => {}
                }
            }

            fn main() {}",
        &[
            "Type alias `Missing` is not defined",
            "Variable `x` is not defined",
            "Grammar error: all match arms must use the same enum; expected 'Color', found 'Bad'",
        ],
    );
}

#[test]
fn errors_mentioning_broken_types_are_not_reported() {
    assert_errors(
        "type Alias = Missing;
            fn f(a: (Alias, u32)) {}
            fn g() { f(1) }
            fn main() { let x: Option<Alias> = 5; }",
        &["Type alias `Missing` is not defined"],
    );
}

/// Aliases like `type A1 = (A0, A0);` up to `A{depth}`, whose resolved types share their parts.
fn shared_aliases(name: &str, leaf: &str, depth: usize) -> String {
    let mut source = format!("type {name}0 = {leaf};\n");
    for i in 1..=depth {
        source += &format!("type {name}{i} = ({name}{0}, {name}{0});\n", i - 1);
    }
    source
}

#[test]
fn shared_types_are_fast() {
    let source = shared_aliases("A", "u8", 64)
        + &shared_aliases("B", "Missing", 64)
        + &shared_aliases("C", "u8", 64)
        + "enum E { V(Unknown) }\n"
        + &shared_aliases("G", "E", 64)
        + &shared_aliases("H", "E", 64)
        + "fn cast(a: A64) -> B64 { <A64>::into(a) }
            fn enum_cast(g: G64) -> H64 { <G64>::into(g) }

            fn main() {
                let b: B64 = param::X;
                let a: A64 = param::X;
                let c: C64 = param::X;
            }";

    assert_errors(
        &source,
        &[
            "Type alias `Missing` is not defined",
            "Type alias `Unknown` is not defined",
        ],
    );
}

#[test]
fn builtins_accept_broken_types() {
    assert_errors(
        "type Alias = Missing;
            fn cast() -> u32 { <Alias>::into(x) }
            fn add(element: Alias, acc: u32) -> u32 { acc }
            fn fold(array: [Alias; 2]) -> u32 { array_fold::<add, 2>(array, 0) }
            fn step(acc: u32, context: (), counter: Alias) -> Either<u32, u32> { Right(acc) }
            fn looped() -> Either<u32, u32> { for_while::<step>(0, ()) }
            fn hash(tuple: (Alias,)) -> u256 { raw_hash::<(Alias,)>(tuple) }

            fn main() { let z: u32 = y; }",
        &[
            "Type alias `Missing` is not defined",
            "Variable `x` is not defined",
            "Variable `y` is not defined",
        ],
    );
}

#[test]
fn broken_statement_does_not_stop_the_block() {
    assert_errors(
        "fn f() -> u32 {
                let a: u32 = x;
                let b: u32 = {
                    let c: u32 = y;
                    z
                };
                w
            }
            fn main() {}",
        &[
            "Variable `x` is not defined",
            "Variable `y` is not defined",
            "Variable `z` is not defined",
            "Variable `w` is not defined",
        ],
    );
}

#[test]
fn broken_let_still_defines_its_variables() {
    assert_errors(
        "fn main() {
                let a: u32 = x;
                let b: Missing = 1;
                let (c, d): u32 = 5;
                let e: (u32, Missing) = (y, 2);
                let uses: (u32, u32, u32, u32) = (a, b, c, d);
                let wrong: bool = a;
            }",
        &[
            "Variable `x` is not defined",
            "Type alias `Missing` is not defined",
            "Expected expression of type `u32`; found something else",
            "Type alias `Missing` is not defined",
            "Variable `y` is not defined",
            "Expected expression of type `bool`, found type `u32`",
        ],
    );
}

#[test]
fn broken_use_does_not_stop_the_analysis() {
    assert_errors(
        "mod m {
                pub fn f() -> u32 { 1 }
            }

            use crate::m::{f, Missing};
            use crate::nowhere::g;

            fn h() -> u32 { x }

            fn main() {
                let a: u32 = f();
                let b: Missing = 1;
                let c: u32 = g();
                let d: bool = a;
            }",
        &[
            "Item `Missing` could not be found",
            "Module `nowhere` not found",
            "Variable `x` is not defined",
            "Expected expression of type `bool`, found type `u32`",
        ],
    );
}

#[test]
fn private_import_is_still_checked() {
    assert_errors(
        "mod m {
                type Secret = u16;
                
                mod inner {
                    pub type Word = u8;
                }
            }

            use crate::m::Secret;
            use crate::m::inner::Word;

            fn main() {
                let s: Secret = 1;
                let w: Word = 2;
                let t: bool = s;
                let u: bool = w;
            }",
        &[
            "Item `Secret` is private",
            "Module `inner` is private",
            "Expected expression of type `bool`, found type `u16`",
            "Expected expression of type `bool`, found type `u8`",
        ],
    );
}
