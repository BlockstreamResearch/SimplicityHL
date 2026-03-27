mod helpers {
    use crate::error::ErrorCollector;
    use crate::parse::{ParseFromStrWithErrors, Program};
    use std::sync::Arc;

    pub fn collect_parse_errors(input: &str) -> String {
        let mut error_handler = ErrorCollector::new(Arc::from(input));
        let parsed = Program::parse_from_str_with_errors(input, &mut error_handler);
        assert!(parsed.is_none(), "program unexpectedly parsed successfully");
        ErrorCollector::to_string(&error_handler)
    }

    pub fn normalize_generated_payload_names(input: &str) -> String {
        let mut out = String::with_capacity(input.len());
        let bytes = input.as_bytes();
        let mut i = 0;
        let needle = b"__match_payload_";

        while i < bytes.len() {
            if bytes[i..].starts_with(needle) {
                out.push_str("__match_payload_<id>");
                i += needle.len();
                while i < bytes.len() {
                    let ch = bytes[i] as char;
                    if ch.is_ascii_alphanumeric() || ch == '_' {
                        i += 1;
                    } else {
                        break;
                    }
                }
            } else {
                out.push(bytes[i] as char);
                i += 1;
            }
        }

        out
    }
}

mod parsing {
    use crate::parse::{ParseFromStr, Program};

    #[test]
    fn test_parse_two_arm_either_match_still_works() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(x: u8) => x,
                Right(y: u16) => 0,
            }
        }
    "#;

        Program::parse_from_str(input).expect("two-arm either match should still parse");
    }

    #[test]
    fn test_parse_option_match_still_works() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                None => 0,
                Some(x: u8) => x,
            }
        }
    "#;

        Program::parse_from_str(input).expect("option match should still parse");
    }

    #[test]
    fn test_parse_bool_match_still_works() {
        let input = r#"
        fn main() -> u8 {
            match true {
                false => 0,
                true => 1,
            }
        }
    "#;

        Program::parse_from_str(input).expect("bool match should still parse");
    }
}

mod binary_tree_match {
    use crate::parse::{
        ExpressionInner, Item, MatchPattern, ParseFromStr, Program, SingleExpressionInner,
    };

    #[test]
    fn test_parse_simple_two_arm_match_shape() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(x: u8) => x,
                Right(y: u8) => y,
            }
        }
    "#;

        let program = Program::parse_from_str(input).expect("program should parse");

        let Item::Function(function) = &program.items()[0] else {
            panic!("expected function");
        };

        let ExpressionInner::Block(_, Some(body)) = function.body().inner() else {
            panic!("expected block");
        };

        let ExpressionInner::Single(single) = body.inner() else {
            panic!("expected single expression");
        };

        let SingleExpressionInner::Match(outer) = single.inner() else {
            panic!("expected outer match");
        };

        assert!(matches!(outer.left().pattern(), MatchPattern::Left(_, _)));
        assert!(matches!(outer.right().pattern(), MatchPattern::Right(_, _)));
    }

    #[test]
    fn test_nested_four_arm_match_to_binary_tree() {
        let input = r#"
        fn main() -> u8 {
            match witness::thingy {
                Left(Left(x: u8)) => x,
                Left(Right(y: u8)) => y,
                Right(Left((a, b): (u8, u256))) => a,
                Right(Right(s: Signature)) => 0,
            }
        }
    "#;

        let program = Program::parse_from_str(input).expect("program should parse");

        let Item::Function(function) = &program.items()[0] else {
            panic!("expected function");
        };

        let ExpressionInner::Block(_, Some(body)) = function.body().inner() else {
            panic!("expected block body");
        };

        let ExpressionInner::Single(single) = body.inner() else {
            panic!("expected single expression body");
        };

        let SingleExpressionInner::Match(outer) = single.inner() else {
            panic!("expected outer match");
        };

        assert!(matches!(outer.left().pattern(), MatchPattern::Left(_, _)));
        assert!(matches!(outer.right().pattern(), MatchPattern::Right(_, _)));

        match outer.left().expression().inner() {
            ExpressionInner::Single(left_single) => {
                assert!(matches!(
                    left_single.inner(),
                    SingleExpressionInner::Match(_)
                ));
            }
            _ => panic!("expected nested left match"),
        }

        match outer.right().expression().inner() {
            ExpressionInner::Single(right_single) => {
                assert!(matches!(
                    right_single.inner(),
                    SingleExpressionInner::Match(_)
                ));
            }
            _ => panic!("expected nested right match"),
        }
    }

    #[test]
    fn test_parse_nested_option_either_match_to_binary_tree() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                None => 0,
                Some(Left(a: u8)) => a,
                Some(Right(b: u8)) => b,
            }
        }
    "#;

        let program = Program::parse_from_str(input).expect("program should parse");

        let Item::Function(function) = &program.items()[0] else {
            panic!("expected function");
        };

        let ExpressionInner::Block(_, Some(body)) = function.body().inner() else {
            panic!("expected block body");
        };

        let ExpressionInner::Single(single) = body.inner() else {
            panic!("expected single expression body");
        };

        let SingleExpressionInner::Match(outer) = single.inner() else {
            panic!("expected outer match");
        };

        assert!(matches!(outer.left().pattern(), MatchPattern::None));
        assert!(matches!(outer.right().pattern(), MatchPattern::Some(_, _)));

        match outer.right().expression().inner() {
            ExpressionInner::Single(right_single) => {
                assert!(matches!(
                    right_single.inner(),
                    SingleExpressionInner::Match(_)
                ));
            }
            _ => panic!("expected nested some match"),
        }
    }

    #[test]
    fn test_parse_three_level_nested_match_recursively() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(Left(Left(a: u8))) => a,
                Left(Left(Right(b: u8))) => b,
                Left(Right(c: u8)) => c,
                Right(d: u8) => d,
            }
        }
    "#;

        let program = Program::parse_from_str(input).expect("program should parse");

        let Item::Function(function) = &program.items()[0] else {
            panic!("expected function");
        };
        let ExpressionInner::Block(_, Some(body)) = function.body().inner() else {
            panic!("expected block");
        };
        let ExpressionInner::Single(single) = body.inner() else {
            panic!("expected single");
        };
        let SingleExpressionInner::Match(outer) = single.inner() else {
            panic!("expected outer match");
        };

        match outer.left().expression().inner() {
            ExpressionInner::Single(left_single) => {
                let SingleExpressionInner::Match(inner) = left_single.inner() else {
                    panic!("expected first nested match");
                };
                match inner.left().expression().inner() {
                    ExpressionInner::Single(inner_left_single) => {
                        assert!(matches!(
                            inner_left_single.inner(),
                            SingleExpressionInner::Match(_)
                        ));
                    }
                    _ => panic!("expected second nested match"),
                }
            }
            _ => panic!("expected nested match on outer left"),
        }
    }

    #[test]
    fn test_nested_match_scrutinee_types_are_preserved() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                None => 0,
                Some(Left(a: u8)) => a,
                Some(Right(b: u16)) => 0,
            }
        }
    "#;

        let program = Program::parse_from_str(input).expect("program should parse");
        let Item::Function(function) = &program.items()[0] else {
            panic!("expected function");
        };
        let ExpressionInner::Block(_, Some(body)) = function.body().inner() else {
            panic!("expected block");
        };
        let ExpressionInner::Single(single) = body.inner() else {
            panic!("expected single");
        };
        let SingleExpressionInner::Match(outer) = single.inner() else {
            panic!("expected outer match");
        };

        assert_eq!(
            outer.scrutinee_type().to_string(),
            "Option<Either<u8, u16>>"
        );

        let ExpressionInner::Single(right_single) = outer.right().expression().inner() else {
            panic!("expected nested some match");
        };
        let SingleExpressionInner::Match(inner) = right_single.inner() else {
            panic!("expected inner match");
        };
        assert_eq!(inner.scrutinee_type().to_string(), "Either<u8, u16>");
    }
}

mod duplicates {
    use crate::parse::test::helpers::collect_parse_errors;

    #[test]
    fn test_reject_duplicate_true_arm() {
        let input = r#"
        fn main() -> u8 {
            match true {
                false => 0,
                true => 1,
                true => 2,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Duplicate match arm") || err.contains("Duplicate true arm"));
    }

    #[test]
    fn test_reject_duplicate_nested_path() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(Right(a: u8)) => a,
                Left(Right(b: u8)) => b,
                Right(c: u8) => c,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Duplicate match arm"));
    }

    #[test]
    fn test_reject_duplicate_nested_path_later_arm() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(Right(a: u8)) => a,
                Left(Right(b: u8)) => b,
                Right(c: u8) => c,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Duplicate match arm"));
        assert!(err.contains("Left(Right(b: u8)) => b"));
    }

    #[test]
    fn test_reject_duplicate_left_arm() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(a: u8) => a,
                Left(b: u8) => b,
                Right(c: u8) => c,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Duplicate match arm"));
        assert!(err.contains("Left(b: u8) => b"));
    }

    #[test]
    fn test_reject_duplicate_right_arm() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
            Left(a: u8) => a,
            Right(b: u8) => b,
            Right(c: u8) => c,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Duplicate match arm"));
        assert!(err.contains("Right(c: u8) => c"));
    }

    #[test]
    fn test_reject_duplicate_some_bind_arm() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                None => 0,
                Some(a: u8) => a,
                Some(b: u8) => b,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Duplicate match arm"));
        assert!(err.contains("Some(b: u8) => b"));
    }
    #[test]
    fn test_reject_duplicate_none_later_arm() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                None => 0,
                None => 1,
                Some(x: u8) => x,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Duplicate match arm"));
        assert!(err.contains("None => 1"));
    }

    #[test]
    fn test_reject_duplicate_true_later_arm() {
        let input = r#"
        fn main() -> u8 {
            match true {
                false => 0,
                true => 1,
                true => 2,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Duplicate match arm"));
        assert!(err.contains("true => 2"));
    }

    #[test]
    fn test_reject_duplicate_left_bind_and_ignore_arm() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(_: u8) => 0,
                Left(a: u8) => a,
                Right(b: u8) => b,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Duplicate match arm") || err.contains("unreachable"));
        assert!(err.contains("Left(a: u8) => a"));
    }

    #[test]
    fn test_reject_duplicate_some_ignore_and_bind_arm() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                None => 0,
                Some(_: u8) => 1,
                Some(a: u8) => a,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Duplicate match arm") || err.contains("unreachable"));
        assert!(err.contains("Some(a: u8) => a"));
    }

    #[test]
    fn test_reject_duplicate_false_arm_later_arm() {
        let input = r#"
        fn main() -> u8 {
            match true {
                false => 0,
                false => 1,
                true => 2,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Duplicate match arm"));
        assert!(err.contains("false => 1"));
    }

    #[test]
    fn test_reject_duplicate_three_level_path() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(Left(Left(a: u8))) => a,
                Left(Left(Left(b: u8))) => b,
                Left(Right(c: u8)) => c,
                Right(d: u8) => d,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Duplicate match arm"));
        assert!(err.contains("Left(Left(Left(b: u8))) => b"));
    }

    #[test]
    fn test_reject_duplicate_bool_arm() {
        let input = r#"
        fn main() -> u8 {
            match true {
                false => 0,
                false => 1,
                true => 2,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Duplicate match arm") || err.contains("Duplicate false arm"));
    }

    #[test]
    fn test_reject_duplicate_none_arm() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                None => 0,
                None => 1,
                Some(x: u8) => x,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Duplicate match arm") || err.contains("Duplicate None arm"));
    }
}

mod syntax {
    use crate::parse::test::helpers::collect_parse_errors;
    use crate::parse::{ParseFromStr, Program};

    #[test]
    fn test_block_arms_do_not_require_trailing_commas() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(a: u8) => { a }
                Right(b: u8) => { b }
            }
        }
    "#;

        Program::parse_from_str(input)
            .expect("block match arms should parse without trailing commas");
    }

    #[test]
    fn test_non_block_arm_requires_trailing_comma() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(a: u8) => a
                Right(b: u8) => b,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Missing ',' after a match arm that isn't block expression"));
    }

    #[test]
    fn test_block_first_arm_without_comma_and_non_block_second_arm_with_comma() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(a: u8) => { a }
                Right(b: u8) => b,
            }
        }
    "#;

        Program::parse_from_str(input).expect("mixed block/non-block arm formatting should parse");
    }
}

mod constructor_overlap {
    use crate::parse::test::helpers::collect_parse_errors;
    #[test]
    fn test_reject_specific_constructor_overlap() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(Left(a: u8)) => a,
                Left(v: Either<u8, u8>) => 0,
                Right(b: u8) => b,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Overlapping match arms in constructor branch"));
    }

    #[test]
    fn test_reject_specific_some_constructor_overlap() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                None => 0,
                Some(v: Either<u8, u8>) => 1,
                Some(Left(a: u8)) => a,
                Some(Right(b: u8)) => b,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("unreachable"));
        assert!(err.contains("covered by a previous arm"));
    }
    #[test]
    fn test_reject_specific_constructor_overlap_on_right_branch() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(a: u8) => a,
                Right(Left(b: u8)) => b,
                Right(v: Either<u8, u8>) => 0,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Overlapping match arms in constructor branch"));
    }

    #[test]
    fn test_reject_specific_constructor_overlap_on_right_branch_alternate() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(a: u8) => a,
                Right(v: Either<u8, u8>) => 0,
                Right(Left(b: u8)) => b,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("unreachable"));
        assert!(err.contains("Right(Left(b: u8)) => b"));
    }
}

mod exhaustiveness {
    use crate::parse::test::helpers::collect_parse_errors;

    #[test]
    fn test_reject_non_exhaustive_either_match() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(a: u8) => a,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Non-exhaustive Either match: missing Right branch"));
    }

    #[test]
    fn test_reject_non_exhaustive_nested_either_match() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(Left(a: u8)) => a,
                Right(b: u8) => b,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Non-exhaustive Either match: missing Right branch"));
    }

    #[test]
    fn test_reject_non_exhaustive_option_match() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Some(a: u8) => a,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Non-exhaustive Option match: missing None"));
    }

    #[test]
    fn test_reject_non_exhaustive_bool_match() {
        let input = r#"
        fn main() -> u8 {
            match true {
                true => 1,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Non-exhaustive bool match: missing false"));
    }
    #[test]
    fn test_reject_non_exhaustive_nested_option_match() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                None => 0,
                Some(Left(a: u8)) => a,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Non-exhaustive Either match: missing Right branch"));
    }

    #[test]
    fn test_reject_non_exhaustive_nested_option_some() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                None => 0,
                Some(Some(a: u8)) => a,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Non-exhaustive Option match: missing None"));
    }

    #[test]
    fn test_reject_non_exhaustive_nested_option_left_arm() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(Some(a: u8)) => a,
                Right(b: u8) => b,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Non-exhaustive Option match: missing None"));
    }
    #[test]
    fn test_reject_non_exhaustive_three_level_nested_either() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(Left(Left(a: u8))) => a,
                Left(Left(Right(b: u8))) => b,
                Right(c: u8) => c,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Non-exhaustive Either match: missing Right branch"));
    }
}

mod usefulness {
    use crate::parse::test::helpers::collect_parse_errors;
    #[test]
    fn test_reject_specific_either_unreachable() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(v: Either<u8, u8>) => 0,
                Left(Left(a: u8)) => a,
                Right(b: u8) => b,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("unreachable"));
        assert!(err.contains("Left(Left(a: u8)) => a"));
    }
    #[test]
    fn test_reject_overlapping_nested_and_terminal_arm() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(v: Either<u8, u8>) => 0,
                Left(Right(a: u8)) => a,
                Right(b: u8) => b,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("unreachable"));
        assert!(err.contains("covered by a previous arm"));
    }

    #[test]
    fn test_reject_overlapping_nested_and_terminal_arm_later_arm() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(v: Either<u8, u8>) => 0,
                Left(Right(a: u8)) => a,
                Right(b: u8) => b,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("unreachable"));
        assert!(err.contains("Left(Right(a: u8)) => a"));
    }
    #[test]
    fn test_reject_some_wildcard_with_specific_nested_some_arms() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                None => 0,
                Some(v: Either<u8, u8>) => 1,
                Some(Left(a: u8)) => a,
                Some(Right(b: u8)) => b,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(
            err.contains("unreachable")
                || err.contains("Overlapping match arms in constructor branch")
        );
    }

    #[test]
    fn test_reject_some_wildcard_with_specific_nested_some_arms_later_arm() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                None => 0,
                Some(v: Either<u8, u8>) => 1,
                Some(Left(a: u8)) => a,
                Some(Right(b: u8)) => b,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Some(Left(a: u8)) => a") || err.contains("Some(Right(b: u8)) => b"));
    }
}

mod formatting {
    use crate::parse::test::helpers::normalize_generated_payload_names;
    use crate::parse::{ParseFromStr, Program};

    #[test]
    fn test_formatting_snapshot_for_nested_match() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                None => 0,
                Some(Left(a: u8)) => a,
                Some(Right(b: u8)) => b,
            }
        }
    "#;

        let program = Program::parse_from_str(input).expect("program should parse");
        let rendered = normalize_generated_payload_names(&program.to_string());

        assert!(rendered.contains("match witness::x"));
        assert!(rendered.contains("Some(__match_payload_<id>: Either<u8, u8>)"));
        assert!(rendered.contains("match __match_payload_<id>"));
    }
    #[test]
    fn test_formatting_snapshot_for_four_arm_either_match() {
        let input = r#"
        fn main() -> u8 {
            match witness::thingy {
                Left(Left(x: u8)) => x,
                Left(Right(y: u8)) => y,
                Right(Left(a: u8)) => a,
                Right(Right(b: u8)) => b,
            }
        }
    "#;

        let program = Program::parse_from_str(input).expect("program should parse");
        let rendered = normalize_generated_payload_names(&program.to_string());

        assert!(rendered.contains("match witness::thingy"));
        assert!(rendered.contains("Left(__match_payload_<id>: Either<u8, u8>)"));
        assert!(rendered.contains("Right(__match_payload_<id>: Either<u8, u8>)"));
        assert!(rendered.matches("match __match_payload_<id>").count() >= 2);
    }

    #[test]
    fn test_formatting_snapshot_for_three_level_match() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(Left(Left(a: u8))) => a,
                Left(Left(Right(b: u8))) => b,
                Left(Right(c: u8)) => c,
                Right(d: u8) => d,
            }
        }
    "#;

        let program = Program::parse_from_str(input).expect("program should parse");
        let rendered = normalize_generated_payload_names(&program.to_string());

        assert!(rendered.contains("match witness::x"));
        assert!(rendered.matches("match __match_payload_<id>").count() >= 2);
    }
}

mod wildcards {
    use crate::parse::{ParseFromStr, Program};

    #[test]
    fn test_parse_nested_wildcard_on_both_outer_either_branches() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(v: Either<u8, u8>) => 0,
                Right(w: Either<u8, u8>) => 1,
            }
        }
    "#;

        Program::parse_from_str(input).expect("wildcard outer either branches should parse");
    }

    #[test]
    fn test_parse_nested_ignore_patterns() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(Left(_: u8)) => 0,
                Left(Right(_: u8)) => 1,
                Right(_: u8) => 2,
            }
        }
    "#;

        Program::parse_from_str(input).expect("nested ignore patterns should parse");
    }
}

mod invalid_patterns {
    use crate::parse::test::helpers::collect_parse_errors;

    #[test]
    fn test_reject_mixed_match_families() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(a: u8) => a,
                Some(b: u8) => b,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(
            err.contains("Incompatible")
                || err.contains("incompatible")
                || err.contains("Left")
                || err.contains("Some")
        );
    }

    #[test]
    fn test_reject_invalid_top_level_bare_arm() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                a: u8 => a,
                Right(b: u8) => b,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Top-level match arms must start with"));
    }

    #[test]
    fn test_reject_unexpected_terminal_pattern_under_constructor() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                None => 0,
                Some(None) => 1,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Unexpected terminal pattern under constructor"));
    }

    #[test]
    fn test_reject_malformed_terminal_under_constructor() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                None => 0,
                Some(Left(None)) => 1,
                Some(Right(v: Option<u8>)) => 2,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Unexpected terminal pattern under constructor"));
    }

    #[test]
    fn test_reject_nested_bool_as_unexpected_terminal_left_arm() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(true) => 1,
                Right(b: u8) => b,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Unexpected terminal pattern under constructor"));
    }

    #[test]
    fn test_reject_nested_bool_as_unexpected_terminal_left_arm_alternate() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                Left(false) => 0,
                Left(true) => 1,
                Right(b: u8) => b,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(err.contains("Unexpected terminal pattern under constructor"));
    }

    #[test]
    fn test_reject_constructor_family_nested_mismatch() {
        let input = r#"
        fn main() -> u8 {
            match witness::x {
                None => 0,
                Some(Left(a: u8)) => a,
                Some(true) => 1,
            }
        }
    "#;

        let err = collect_parse_errors(input);
        assert!(
            err.contains("Mixed match families")
                || err.contains("Incompatible")
                || err.contains("Unexpected terminal pattern under constructor")
        );
    }
}
