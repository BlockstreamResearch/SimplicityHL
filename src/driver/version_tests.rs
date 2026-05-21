use crate::driver::tests::setup_graph_raw;

macro_rules! version_test {
    ($name:ident, $expect_success:expr, $expected_err:expr, $( $path:expr => $content:expr ),+ $(,)?) => {
        #[test]
        fn $name() {
            let v = env!("CARGO_PKG_VERSION");
            let files: Vec<(&str, String)> = vec![
                $( ($path, $content.replace("{v}", v)) ),+
            ];

            let refs: Vec<(&str, &str)> = files.iter().map(|(p, c)| (*p, c.as_str())).collect();
            let (graph_opt, _, _ws, handler) = setup_graph_raw(refs);

            if $expect_success {
                assert!(graph_opt.is_some() && !handler.has_errors(),
                    "Scenario failed unexpectedly. Errors:\n{}", handler);
            } else {
                assert!(graph_opt.is_none() || handler.has_errors(),
                    "Scenario succeeded when it should have failed.");
                let expected_err: Option<&str> = $expected_err;
                if let Some(err) = expected_err {
                    assert!(handler.to_string().contains(err),
                        "Expected error containing '{}' but got:\n{}", err, handler);
                }
            }
        }
    };
}

version_test!(
    exact_match_all, true, None,
    "main.simf" => "#![compiler_version(\"={v}\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"={v}\")]\npub fn foo() {}"
);

version_test!(
    caret_match_all, true, None,
    "main.simf" => "#![compiler_version(\"^{v}\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"^{v}\")]\npub fn foo() {}"
);

version_test!(
    tilde_match_all, true, None,
    "main.simf" => "#![compiler_version(\"~{v}\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"~{v}\")]\npub fn foo() {}"
);

version_test!(
    range_gt_match_all, true, None,
    "main.simf" => "#![compiler_version(\">0.1.0\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\">0.1.0\")]\npub fn foo() {}"
);

version_test!(
    range_gte_match_all, true, None,
    "main.simf" => "#![compiler_version(\">=0.1.0\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\">=0.1.0\")]\npub fn foo() {}"
);

version_test!(
    star_match_all, true, None,
    "main.simf" => "#![compiler_version(\"*\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"*\")]\npub fn foo() {}"
);

version_test!(
    mixed_valid_operators, true, None,
    "main.simf" => "#![compiler_version(\"^{v}\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"={v}\")]\nuse crate::B::foo;\npub fn foo() {}",
    "libs/lib/B.simf" => "#![compiler_version(\">0.1.0\")]\nuse crate::C::foo;\npub fn foo() {}",
    "libs/lib/C.simf" => "#![compiler_version(\"*\")]\npub fn foo() {}"
);

version_test!(
    main_exact_lib_float, true, None,
    "main.simf" => "#![compiler_version(\"={v}\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\">=0.1.0\")]\npub fn foo() {}"
);

version_test!(
    main_float_lib_exact, true, None,
    "main.simf" => "#![compiler_version(\">=0.1.0\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"={v}\")]\npub fn foo() {}"
);

version_test!(
    main_too_old_fails, false, Some("Compiler too old"),
    "main.simf" => "#![compiler_version(\">99.0.0\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"={v}\")]\npub fn foo() {}"
);

version_test!(
    lib_too_old_fails, false, Some("Compiler too old"),
    "main.simf" => "#![compiler_version(\"={v}\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\">99.0.0\")]\npub fn foo() {}"
);

version_test!(
    main_contract_too_old_fails, false, Some("Contract too old"),
    "main.simf" => "#![compiler_version(\"<0.0.1\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"={v}\")]\npub fn foo() {}"
);

version_test!(
    lib_contract_too_old_fails, false, Some("Contract too old"),
    "main.simf" => "#![compiler_version(\"={v}\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"<0.0.1\")]\npub fn foo() {}"
);

version_test!(
    main_exact_mismatch_fails, false, Some("Exact version mismatch"),
    "main.simf" => "#![compiler_version(\"=0.0.1\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"={v}\")]\npub fn foo() {}"
);

version_test!(
    lib_exact_mismatch_fails, false, Some("Exact version mismatch"),
    "main.simf" => "#![compiler_version(\"={v}\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"=0.0.1\")]\npub fn foo() {}"
);

version_test!(
    deep_chain_success, true, None,
    "main.simf" => "#![compiler_version(\">0.1.0\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\">0.1.0\")]\nuse crate::B::foo;\npub fn foo() {}",
    "libs/lib/B.simf" => "#![compiler_version(\">0.1.0\")]\nuse crate::C::foo;\npub fn foo() {}",
    "libs/lib/C.simf" => "#![compiler_version(\">0.1.0\")]\nuse crate::D::foo;\npub fn foo() {}",
    "libs/lib/D.simf" => "#![compiler_version(\">0.1.0\")]\npub fn foo() {}"
);

version_test!(
    deep_chain_fail_at_leaf, false, Some("Compiler too old"),
    "main.simf" => "#![compiler_version(\">0.1.0\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\">0.1.0\")]\nuse crate::B::foo;\npub fn foo() {}",
    "libs/lib/B.simf" => "#![compiler_version(\">0.1.0\")]\nuse crate::C::foo;\npub fn foo() {}",
    "libs/lib/C.simf" => "#![compiler_version(\">0.1.0\")]\nuse crate::D::foo;\npub fn foo() {}",
    "libs/lib/D.simf" => "#![compiler_version(\">99.0.0\")]\npub fn foo() {}"
);

version_test!(
    diamond_dependency_success, true, None,
    "main.simf" => "#![compiler_version(\"={v}\")]\nuse lib::A::foo; use lib::B::bar;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"={v}\")]\nuse crate::C::baz;\npub fn foo() {}",
    "libs/lib/B.simf" => "#![compiler_version(\"={v}\")]\nuse crate::C::baz;\npub fn bar() {}",
    "libs/lib/C.simf" => "#![compiler_version(\"={v}\")]\npub fn baz() {}"
);

version_test!(
    diamond_dependency_fail_at_c, false, Some("Contract too old"),
    "main.simf" => "#![compiler_version(\"={v}\")]\nuse lib::A::foo; use lib::B::bar;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"={v}\")]\nuse crate::C::baz;\npub fn foo() {}",
    "libs/lib/B.simf" => "#![compiler_version(\"={v}\")]\nuse crate::C::baz;\npub fn bar() {}",
    "libs/lib/C.simf" => "#![compiler_version(\"<0.0.1\")]\npub fn baz() {}"
);

version_test!(
    crate_import_success, true, None,
    "main.simf" => "#![compiler_version(\"={v}\")]\nuse crate::Utils::helper;\nfn main() {}",
    "Utils.simf" => "#![compiler_version(\"={v}\")]\npub fn helper() {}"
);

version_test!(
    crate_import_fail, false, Some("Exact version mismatch"),
    "main.simf" => "#![compiler_version(\"={v}\")]\nuse crate::Utils::helper;\nfn main() {}",
    "Utils.simf" => "#![compiler_version(\"=0.0.1\")]\npub fn helper() {}"
);

version_test!(
    lib_crate_import_success, true, None,
    "main.simf" => "#![compiler_version(\"={v}\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"={v}\")]\nuse crate::B::foo;\npub fn foo() {}",
    "libs/lib/B.simf" => "#![compiler_version(\"={v}\")]\npub fn foo() {}"
);

version_test!(
    lib_crate_import_fail, false, Some("Compiler too old"),
    "main.simf" => "#![compiler_version(\"={v}\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"={v}\")]\nuse crate::B::foo;\npub fn foo() {}",
    "libs/lib/B.simf" => "#![compiler_version(\">99.0.0\")]\npub fn foo() {}"
);

version_test!(
    invalid_syntax_main, false, Some("Invalid version syntax"),
    "main.simf" => "#![compiler_version(\"foo\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"={v}\")]\npub fn foo() {}"
);

version_test!(
    invalid_syntax_lib, false, Some("Invalid version syntax"),
    "main.simf" => "#![compiler_version(\"={v}\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"bar\")]\npub fn foo() {}"
);

version_test!(
    multiple_ranges_success, true, None,
    "main.simf" => "#![compiler_version(\">=0.1.0, <99.0.0\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"={v}\")]\npub fn foo() {}"
);

version_test!(
    multiple_ranges_fail, false, Some("too old"),
    "main.simf" => "#![compiler_version(\">=0.1.0, <0.2.0\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"={v}\")]\npub fn foo() {}"
);

version_test!(
    whitespace_in_version, true, None,
    "main.simf" => "#![compiler_version(\"  >= 0.1.0  \")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"={v}\")]\npub fn foo() {}"
);

version_test!(
    caret_zero_minor_fail, false, Some("Contract too old"),
    "main.simf" => "#![compiler_version(\"^0.0.1\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"={v}\")]\npub fn foo() {}"
);

version_test!(
    large_project_mix_success, true, None,
    "main.simf" => "#![compiler_version(\">0.1.0\")]\nuse lib::A::a;\nuse crate::B::b;\nfn main() {}",
    "B.simf" => "#![compiler_version(\"={v}\")]\npub fn b() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"*\")]\nuse crate::C::c;\npub fn a() {}",
    "libs/lib/C.simf" => "#![compiler_version(\"~{v}\")]\nuse crate::D::d;\npub fn c() {}",
    "libs/lib/D.simf" => "#![compiler_version(\">0.0.0\")]\npub fn d() {}"
);

version_test!(
    mixed_dependent_ranges_success, true, None,
    "main.simf" => "#![compiler_version(\"={v}\")]\nuse lib::A::foo; use lib::B::bar;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"<99.0.0\")]\npub fn foo() {}",
    "libs/lib/B.simf" => "#![compiler_version(\">0.1.0\")]\npub fn bar() {}"
);

version_test!(
    mixed_dependent_ranges_fail_less_than_v, false, Some("Contract too old"),
    "main.simf" => "#![compiler_version(\"={v}\")]\nuse lib::A::foo; use lib::B::bar;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"<{v}\")]\npub fn foo() {}",
    "libs/lib/B.simf" => "#![compiler_version(\">0.1.0\")]\npub fn bar() {}"
);

version_test!(
    mixed_dependent_ranges_fail_greater_than_v, false, Some("Compiler too old"),
    "main.simf" => "#![compiler_version(\"={v}\")]\nuse lib::A::foo; use lib::B::bar;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"<99.0.0\")]\npub fn foo() {}",
    "libs/lib/B.simf" => "#![compiler_version(\">{v}\")]\npub fn bar() {}"
);

version_test!(
    mixed_dependent_ranges_both_fail, false, Some("too old"),
    "main.simf" => "#![compiler_version(\"={v}\")]\nuse lib::A::foo; use lib::B::bar;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"<{v}\")]\npub fn foo() {}",
    "libs/lib/B.simf" => "#![compiler_version(\">{v}\")]\npub fn bar() {}"
);

version_test!(
    chained_mixed_dependent_ranges_success, true, None,
    "main.simf" => "#![compiler_version(\"={v}\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"<99.0.0\")]\nuse crate::B::foo;\npub fn foo() {}",
    "libs/lib/B.simf" => "#![compiler_version(\">0.1.0\")]\npub fn foo() {}"
);

version_test!(
    chained_mixed_dependent_ranges_fail, false, Some("Compiler too old"),
    "main.simf" => "#![compiler_version(\"={v}\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"<99.0.0\")]\nuse crate::B::foo;\npub fn foo() {}",
    "libs/lib/B.simf" => "#![compiler_version(\">{v}\")]\npub fn foo() {}"
);

version_test!(
    logical_or_unsupported_syntax, false, Some("Invalid version syntax"),
    "main.simf" => "#![compiler_version(\"<0.1.0 || ={v}\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"={v}\")]\npub fn foo() {}"
);

version_test!(
    prerelease_tag_mismatch_across_bases, false, Some("Contract too old"),
    "main.simf" => "#![compiler_version(\">=0.1.0-alpha.1\")]\nfn main() {}"
);

version_test!(
    missing_version_attribute, false, Some("Missing compiler version"),
    "main.simf" => "// NO_INJECT\nfn main() {}"
);

version_test!(
    build_metadata_success, true, None,
    "main.simf" => "#![compiler_version(\">=0.1.0+build.2023\")]\nfn main() {}"
);

version_test!(
    empty_version_string, false, Some("Invalid version syntax"),
    "main.simf" => "#![compiler_version(\"\")]\nfn main() {}"
);

version_test!(
    malformed_attribute_no_quotes, false, Some("Expected"),
    "main.simf" => "#![compiler_version(={v})]\nfn main() {}"
);

version_test!(
    malformed_attribute_wrong_name, false, Some("Expected"),
    "main.simf" => "#![version(\"={v}\")]\nfn main() {}"
);

version_test!(
    circular_dependency_version_success, true, None,
    "main.simf" => "#![compiler_version(\"={v}\")]\nuse lib::A::a;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"={v}\")]\nuse crate::B::b;\npub fn a() {}",
    "libs/lib/B.simf" => "#![compiler_version(\"={v}\")]\nuse crate::A::a;\npub fn b() {}"
);

version_test!(
    multiple_directives_same_file_fails, false, Some("Expected"),
    "main.simf" => "#![compiler_version(\"={v}\")]\n#![compiler_version(\"={v}\")]\nfn main() {}"
);

version_test!(
    caret_zero_minor_fails_on_newer_compiler, false, Some("Contract too old"),
    "main.simf" => "#![compiler_version(\"^0.1.2\")]\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"={v}\")]\npub fn foo() {}"
);

version_test!(
    invalid_leading_zeros_fails, false, Some("Invalid version syntax"),
    "main.simf" => "#![compiler_version(\"=01.0.0\")]\nfn main() {}"
);

version_test!(
    invalid_empty_prerelease_segment_fails, false, Some("Invalid version syntax"),
    "main.simf" => "#![compiler_version(\"=1.0.0-alpha..1\")]\nfn main() {}"
);

version_test!(
    invalid_characters_in_version_fails, false, Some("Invalid version syntax"),
    "main.simf" => "#![compiler_version(\"=1.0.0-alpha!+build\")]\nfn main() {}"
);

version_test!(
    wildcard_x_minor_patch, true, None,
    "main.simf" => "#![compiler_version(\"0.x.x\")]\nfn main() {}"
);

version_test!(
    wildcard_x_major, true, None,
    "main.simf" => "#![compiler_version(\"X\")]\nfn main() {}"
);

version_test!(
    heavy_whitespace_and_tabs_success, true, None,
    "main.simf" => "#![compiler_version(\"  >=  0.0.1  ,  <  99.0.0  \")]\nfn main() {}"
);

version_test!(
    unreferenced_file_with_invalid_version_ignored, true, None,
    "main.simf" => "#![compiler_version(\"={v}\")]\nuse lib::A::foo;\nfn main() {}",
    "libs/lib/A.simf" => "#![compiler_version(\"={v}\")]\npub fn foo() {}",
    "libs/lib/B.simf" => "#![compiler_version(\">99.0.0\")]\npub fn unused() {}"
);

version_test!(
    incompatible_fallback, false, Some("Incompatible version"),
    "main.simf" => "#![compiler_version(\"~99\")]\nfn main() {}"
);

version_test!(
    bare_version_exact_mismatch_fallback, false, Some("Exact version mismatch"),
    "main.simf" => "#![compiler_version(\"0.0.1\")]\nfn main() {}"
);

version_test!(
    missing_version_with_comments, false, Some("Missing compiler version"),
    "main.simf" => "// NO_INJECT\n/* Some initial block comment */\nfn main() {}"
);

version_test!(
    missing_version_type_alias_first, false, Some("Missing compiler version"),
    "main.simf" => "// NO_INJECT\npub type MyType = u32;\nfn main() {}"
);

version_test!(
    missing_version_empty_file, false, Some("Missing compiler version"),
    "main.simf" => "// NO_INJECT"
);
