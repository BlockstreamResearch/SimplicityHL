#[cfg(feature = "fmt")]
mod lossless_test {
    use simplicityhl::lexer::{lex_lossless, FmtTokens};

    fn get_input(input_file: &str) -> String {
        use std::fs;
        use std::path::Path;

        let tests_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
        let input_path = tests_dir.join(input_file);
        fs::read_to_string(&input_path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", input_path.display()))
    }

    fn assert_lossless_fixture(input_file: &str) {
        const DEFAULT_FILE_ID: usize = 0;

        let original_input = get_input(input_file);

        let (tokens, diagnostics) = lex_lossless(DEFAULT_FILE_ID, &original_input, 0);
        assert!(
            diagnostics.is_empty(),
            "Diagnostic errors aren't empty: {diagnostics:?}"
        );
        let tokens = tokens.expect("lossless lexing succeeds");
        let restored_input = restore_input_by_tokens(&tokens);
        assert_eq!(
            restored_input, original_input,
            "lossless tokens must reproduce the input"
        );
    }

    fn restore_input_by_tokens(tokens: &FmtTokens<'_>) -> String {
        let mut buf = String::new();

        let mut prev_span_end = None;
        for (t, s) in tokens {
            match prev_span_end {
                None => {
                    let _ = prev_span_end.insert(s.end);
                }
                Some(x) => {
                    assert_eq!(x, s.start);
                    let _ = prev_span_end.insert(s.end);
                }
            }
            buf.push_str(&t.to_string());
        }
        buf
    }

    macro_rules! test_lex_coverage {
    ($($lossless_name:ident: $input:literal,)+) => {
        $(
            #[test]
            fn $lossless_name() {
                assert_lossless_fixture($input);
            }
        )+
    };
}

    test_lex_coverage! {
        array_fold_2n_lossless: "array_fold_2n.simf",
        array_fold_lossless: "array_fold.simf",
        cat_lossless: "cat.simf",
        ctv_lossless: "ctv.simf",
        escrow_with_delay_lossless: "escrow_with_delay.simf",
        hash_loop_lossless: "hash_loop.simf",
        hodl_vault_lossless: "hodl_vault.simf",
        htlc_lossless: "htlc.simf",
        last_will_lossless: "last_will.simf",
        modules_lossless: "modules.simf",
        non_interactive_fee_bump_lossless: "non_interactive_fee_bump.simf",
        p2ms_lossless: "p2ms.simf",
        p2pk_lossless: "p2pk.simf",
        p2pkh_lossless: "p2pkh.simf",
        pattern_matching_lossless: "pattern_matching.simf",
        presigned_vault_lossless: "presigned_vault.simf",
        reveal_collision_lossless: "reveal_collision.simf",
        reveal_fix_point_lossless: "reveal_fix_point.simf",
        sighash_all_anyonecanpay_lossless: "sighash_all_anyonecanpay.simf",
        sighash_all_anyprevout_lossless: "sighash_all_anyprevout.simf",
        sighash_all_anyprevoutanyscript_lossless: "sighash_all_anyprevoutanyscript.simf",
        sighash_none_lossless: "sighash_none.simf",
        sighash_single_lossless: "sighash_single.simf",
        transfer_with_timeout_lossless: "transfer_with_timeout.simf",
        local_crate_main_lossless: "local_crate/main.simf",
        local_crate_math_lossless: "local_crate/math.simf",
        simple_multidep_hashes_lossless: "simple_multidep/crypto/hashes.simf",
        simple_multidep_arithmetic_lossless: "simple_multidep/math/arithmetic.simf",
        simple_multidep_flattened_lossless: "simple_multidep/flattened.simf",
        simple_multidep_main_lossless: "simple_multidep/main.simf",
        single_dep_flattened_lossless: "single_dep/flattened.simf",
        single_dep_main_lossless: "single_dep/main.simf",
        single_dep_funcs_lossless: "single_dep/temp/funcs.simf",
        single_dep_utils_lossless: "single_dep/temp/constants/utils.simf",
        multiple_deps_main_lossless: "multiple_deps/main.simf",
        multiple_deps_flattened_lossless: "multiple_deps/flattened.simf",
        multiple_deps_simple_op_lossless: "multiple_deps/math/simple_op.simf",
        multiple_deps_build_root_lossless: "multiple_deps/merkle/build_root.simf",
    }
}
