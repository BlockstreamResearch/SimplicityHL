//! Tests for the `chain!` expression (`-Z chain`).
//!
//! `chain!` is pure sugar, so the desugared program is an oracle: it already
//! compiles, and its CMR is the exact answer. Semantic coverage is therefore
//! differential (`assert_same_cmr`) rather than a restatement of each step.
//!
//! CMR equality cannot see *where* a chain reports a problem, and a chain that
//! blames the wrong line defeats the point of the feature, so `diagnostics`
//! pins spans separately.

use simplicityhl::ast::ElementsJetHinter;
use simplicityhl::error::Diagnostic;
use simplicityhl::error::Location;
use simplicityhl::parse::{ParseFromStr, Program};
use simplicityhl::{Arguments, CompiledProgram, TemplateAst, UnstableFeature, UnstableFeatures};

fn chain_enabled() -> UnstableFeatures {
    UnstableFeatures::new([UnstableFeature::Chain])
}

fn compile(source: &str, features: UnstableFeatures) -> Result<CompiledProgram, String> {
    CompiledProgram::new_with_unstable(
        source,
        &features,
        Arguments::default(),
        false,
        Box::new(ElementsJetHinter::new()),
    )
}

/// Compile with `chain!` enabled, expecting success.
fn cmr_of(source: &str) -> String {
    compile(source, chain_enabled())
        .unwrap_or_else(|error| panic!("program should compile:\n{error}\n\nsource:\n{source}"))
        .commit()
        .cmr()
        .to_string()
}

/// Compile with `chain!` enabled, expecting failure, and return the rendered
/// diagnostics.
fn error_of(source: &str) -> String {
    match compile(source, chain_enabled()) {
        Ok(_) => panic!("program should not compile:\n{source}"),
        Err(error) => error,
    }
}

/// The message, 1-based source line, and help text of a program's first error.
///
/// Reads the diagnostic rather than its rendered text: the string form of a
/// compile failure carries neither position nor help, which is what these tests
/// are about.
fn first_error_at(source: &str) -> (String, usize, Option<String>) {
    let diagnostics = TemplateAst::new_with_unstable(
        source,
        &chain_enabled(),
        Box::new(ElementsJetHinter::new()),
    )
    .err()
    .unwrap_or_else(|| panic!("program should not compile:\n{source}"));

    let diagnostic = diagnostics
        .diagnostics()
        .iter()
        .find(|d: &&Diagnostic| matches!(d.location(), Location::Code(_)))
        .unwrap_or_else(|| panic!("expected a diagnostic anchored in the source:\n{source}"));

    let Location::Code(span) = diagnostic.location() else {
        unreachable!("filtered above")
    };
    let line = source[..span.start].lines().count().max(1);
    let help = diagnostic.help().as_ref().map(ToString::to_string);
    (diagnostic.error().to_string(), line, help)
}

/// The oracle: a chain and its desugaring must compile to the same Simplicity.
///
/// The reference is the `let` chain in the same *position*. Where the chain is
/// a sub-expression, that means a block: a chain is an expression, so it opens
/// a scope its hole does not outlive.
fn assert_same_cmr(chain_source: &str, block_source: &str) {
    assert_eq!(
        cmr_of(chain_source),
        cmr_of(block_source),
        "chain and its desugaring should compile to the same program"
    );
}

const TAIL: &str = r#"
    let pk: Pubkey = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798;
    jet::bip_0340_verify((pk, msg), witness::SIG);
}"#;

mod lowering {
    use super::*;

    /// The motivating case: `examples/sighash_all_anyonecanpay.simf`, eleven
    /// `Ctx8` steps ending in a `u256`.
    #[test]
    fn sighash_all_anyonecanpay_matches_its_desugaring() {
        let chain = format!(
            r#"fn main() {{
    let msg: u256 = chain!(ctx = jet::sha_256_ctx_8_init(),
        jet::sha_256_ctx_8_add_32(ctx, jet::genesis_block_hash()),
        jet::sha_256_ctx_8_add_32(ctx, jet::genesis_block_hash()),
        jet::sha_256_ctx_8_add_4(ctx, jet::version()),
        jet::sha_256_ctx_8_add_4(ctx, jet::lock_time()),
        jet::sha_256_ctx_8_add_32(ctx, jet::tap_env_hash()),
        jet::sha_256_ctx_8_add_32(ctx, unwrap(jet::input_hash(jet::current_index()))),
        jet::sha_256_ctx_8_add_32(ctx, unwrap(jet::input_utxo_hash(jet::current_index()))),
        jet::sha_256_ctx_8_add_32(ctx, jet::outputs_hash()),
        jet::sha_256_ctx_8_add_32(ctx, jet::issuances_hash()),
        jet::sha_256_ctx_8_add_32(ctx, jet::output_surjection_proofs_hash()),
        jet::sha_256_ctx_8_finalize(ctx));
{TAIL}"#
        );
        let block = format!(
            r#"fn main() {{
    let msg: u256 = {{
        let ctx: Ctx8 = jet::sha_256_ctx_8_init();
        let ctx: Ctx8 = jet::sha_256_ctx_8_add_32(ctx, jet::genesis_block_hash());
        let ctx: Ctx8 = jet::sha_256_ctx_8_add_32(ctx, jet::genesis_block_hash());
        let ctx: Ctx8 = jet::sha_256_ctx_8_add_4(ctx, jet::version());
        let ctx: Ctx8 = jet::sha_256_ctx_8_add_4(ctx, jet::lock_time());
        let ctx: Ctx8 = jet::sha_256_ctx_8_add_32(ctx, jet::tap_env_hash());
        let ctx: Ctx8 = jet::sha_256_ctx_8_add_32(ctx, unwrap(jet::input_hash(jet::current_index())));
        let ctx: Ctx8 = jet::sha_256_ctx_8_add_32(ctx, unwrap(jet::input_utxo_hash(jet::current_index())));
        let ctx: Ctx8 = jet::sha_256_ctx_8_add_32(ctx, jet::outputs_hash());
        let ctx: Ctx8 = jet::sha_256_ctx_8_add_32(ctx, jet::issuances_hash());
        let ctx: Ctx8 = jet::sha_256_ctx_8_add_32(ctx, jet::output_surjection_proofs_hash());
        jet::sha_256_ctx_8_finalize(ctx)
    }};
{TAIL}"#
        );
        assert_same_cmr(&chain, &block);
    }

    /// Six modes, one pipeline with different segments, each threading
    /// `u256 -> Ctx8 -> ... -> u256`. No annotations: every step is a
    /// custom-function call, so each hole type is read off a signature.
    const MODES: &str = r#"
fn tag() -> u256 {
    0x0e8e05b1734bb78560eec1e2153340c5da8a5d7dc936253996d70aeacc26923a
}
fn mode_ctx(tag: u256) -> Ctx8 {
    let ctx: Ctx8 = jet::sha_256_ctx_8_init();
    let ctx: Ctx8 = jet::sha_256_ctx_8_add_32(ctx, tag);
    jet::sha_256_ctx_8_add_32(ctx, tag)
}
fn add_common(ctx: Ctx8) -> Ctx8 {
    let ctx: Ctx8 = jet::sha_256_ctx_8_add_4(ctx, jet::version());
    jet::sha_256_ctx_8_add_4(ctx, jet::lock_time())
}
fn add_all_inputs(ctx: Ctx8) -> Ctx8 {
    let ctx: Ctx8 = jet::sha_256_ctx_8_add_32(ctx, jet::inputs_hash());
    jet::sha_256_ctx_8_add_32(ctx, jet::input_utxos_hash())
}
fn add_all_outputs(ctx: Ctx8) -> Ctx8 {
    jet::sha_256_ctx_8_add_32(ctx, jet::outputs_hash())
}
fn finish(ctx: Ctx8) -> u256 {
    jet::sha_256_ctx_8_finalize(ctx)
}
"#;

    #[test]
    fn multi_type_chain_needs_no_annotations() {
        let chain = format!(
            r#"{MODES}
fn main() {{
    let msg: u256 = chain!(x = tag(),
        mode_ctx(x),
        add_common(x),
        add_all_inputs(x),
        add_all_outputs(x),
        finish(x));
{TAIL}"#
        );
        let block = format!(
            r#"{MODES}
fn main() {{
    let msg: u256 = {{
        let x: u256 = tag();
        let x: Ctx8 = mode_ctx(x);
        let x: Ctx8 = add_common(x);
        let x: Ctx8 = add_all_inputs(x);
        let x: Ctx8 = add_all_outputs(x);
        finish(x)
    }};
{TAIL}"#
        );
        assert_same_cmr(&chain, &block);
    }

    /// Dropping a segment is a removed line, not a change of nesting depth.
    /// Each mode must still match its own desugaring.
    #[test]
    fn omitting_a_segment_matches_its_desugaring() {
        let chain = format!(
            r#"{MODES}
fn main() {{
    let msg: u256 = chain!(x = tag(),
        mode_ctx(x),
        add_common(x),
        add_all_inputs(x),
        finish(x));
{TAIL}"#
        );
        let block = format!(
            r#"{MODES}
fn main() {{
    let msg: u256 = {{
        let x: u256 = tag();
        let x: Ctx8 = mode_ctx(x);
        let x: Ctx8 = add_common(x);
        let x: Ctx8 = add_all_inputs(x);
        finish(x)
    }};
{TAIL}"#
        );
        assert_same_cmr(&chain, &block);
    }

    /// An annotated step must lower to exactly the `let` it stands for.
    #[test]
    fn annotated_step_matches_its_desugaring() {
        let chain = format!(
            r#"fn main() {{
    let msg: u256 = chain!(ctx = jet::sha_256_ctx_8_init(),
        ctx: Ctx8 = dbg!(jet::sha_256_ctx_8_add_32(ctx, jet::genesis_block_hash())),
        jet::sha_256_ctx_8_finalize(ctx));
{TAIL}"#
        );
        let block = format!(
            r#"fn main() {{
    let msg: u256 = {{
        let ctx: Ctx8 = jet::sha_256_ctx_8_init();
        let ctx: Ctx8 = dbg!(jet::sha_256_ctx_8_add_32(ctx, jet::genesis_block_hash()));
        jet::sha_256_ctx_8_finalize(ctx)
    }};
{TAIL}"#
        );
        assert_same_cmr(&chain, &block);
    }

    /// The last step is typed by the chain's surroundings, so a context-typed
    /// call is fine there though it would need annotating anywhere earlier.
    #[test]
    fn context_typed_call_is_allowed_as_the_final_step() {
        let source = format!(
            r#"fn main() {{
    let msg: u256 = chain!(ctx = jet::sha_256_ctx_8_init(),
        jet::sha_256_ctx_8_add_32(ctx, jet::genesis_block_hash()),
        dbg!(jet::sha_256_ctx_8_finalize(ctx)));
{TAIL}"#
        );
        let _ = cmr_of(&source);
    }

    /// The warning in `examples/chain_sighash_modes.simf`: a chain equals the
    /// `let` chain in its place, but not the nested-call form, because binding
    /// a value materializes it. The `let` form differs from nested too, which
    /// is what makes that pre-existing rather than a cost of `chain!`.
    ///
    /// Pinned because it is invisible in the source and lands in the address.
    #[test]
    fn chain_equals_the_let_form_but_not_the_nested_form() {
        const HELPERS: &str = r#"
fn tag() -> u256 {
    0x0e8e05b1734bb78560eec1e2153340c5da8a5d7dc936253996d70aeacc26923a
}
fn mode_ctx(tag: u256) -> Ctx8 {
    let ctx: Ctx8 = jet::sha_256_ctx_8_init();
    jet::sha_256_ctx_8_add_32(ctx, tag)
}
fn add_common(ctx: Ctx8) -> Ctx8 {
    jet::sha_256_ctx_8_add_4(ctx, jet::version())
}
fn add_all_outputs(ctx: Ctx8) -> Ctx8 {
    jet::sha_256_ctx_8_add_32(ctx, jet::outputs_hash())
}
fn finish(ctx: Ctx8) -> u256 {
    jet::sha_256_ctx_8_finalize(ctx)
}
fn digest() -> u256 {
"#;
        // `main` comes last: a function must be defined before it is called.
        const MAIN: &str = r#"
}
fn main() {
    let msg: u256 = digest();
    assert!(jet::eq_256(msg, msg));
}"#;

        let program = |body: &str| format!("{HELPERS}    {body}{MAIN}");
        let chain =
            program("chain!(x = tag(), mode_ctx(x), add_common(x), add_all_outputs(x), finish(x))");
        let lets = program(
            "let x: u256 = tag();
    let x: Ctx8 = mode_ctx(x);
    let x: Ctx8 = add_common(x);
    let x: Ctx8 = add_all_outputs(x);
    finish(x)",
        );
        let nested = program("finish(add_all_outputs(add_common(mode_ctx(tag()))))");

        assert_eq!(
            cmr_of(&chain),
            cmr_of(&lets),
            "a chain should compile to the `let` chain written in its place"
        );
        assert_ne!(
            cmr_of(&chain),
            cmr_of(&nested),
            "binding a value changes the program, so a chain cannot match the nested form -- \
             if this ever starts matching, the warning in examples/chain_sighash_modes.simf \
             and the CHANGELOG are stale"
        );
        assert_ne!(
            cmr_of(&lets),
            cmr_of(&nested),
            "the nested form differs from the bound form with no chain involved, which is what \
             makes that difference pre-existing behaviour rather than a cost of `chain!`"
        );
    }

    /// A function must be defined before it is called, in chains as anywhere
    /// else. Pinned because a chain resolves callees a second time, to read
    /// their output types, and could have diverged.
    #[test]
    fn a_step_cannot_call_a_function_defined_later() {
        const HELPERS: &str = r#"
fn seed() -> Ctx8 { jet::sha_256_ctx_8_init() }
fn finish(ctx: Ctx8) -> u256 { jet::sha_256_ctx_8_finalize(ctx) }
"#;
        let chain = "fn main() {\n    let msg: u256 = chain!(ctx = seed(), finish(ctx));\n    assert!(jet::eq_256(msg, msg));\n}";
        let block = "fn main() {\n    let msg: u256 = { let ctx: Ctx8 = seed(); finish(ctx) };\n    assert!(jet::eq_256(msg, msg));\n}";

        for source in [chain, block] {
            assert!(
                error_of(&format!("{source}{HELPERS}")).contains("was called but not defined"),
                "a forward reference should be rejected the same way in both forms"
            );
        }

        // Defined first, both forms compile and agree.
        assert_same_cmr(&format!("{HELPERS}{chain}"), &format!("{HELPERS}{block}"));
    }

    /// A chain opens a scope, so an outer binding of the same name survives it
    /// untouched. Compare against the block that makes the shadowing explicit.
    #[test]
    fn hole_shadows_an_outer_binding_without_disturbing_it() {
        let chain = r#"fn main() {
    let ctx: u32 = 7;
    let sum: u32 = chain!(ctx = jet::sha_256_ctx_8_init(),
        jet::sha_256_ctx_8_add_4(ctx, 1),
        jet::sha_256_ctx_8_add_4(ctx, 2),
        4);
    let (_, total): (bool, u32) = jet::add_32(ctx, sum);
    assert!(jet::eq_32(total, 11));
}"#;
        let block = r#"fn main() {
    let ctx: u32 = 7;
    let sum: u32 = {
        let ctx: Ctx8 = jet::sha_256_ctx_8_init();
        let ctx: Ctx8 = jet::sha_256_ctx_8_add_4(ctx, 1);
        let ctx: Ctx8 = jet::sha_256_ctx_8_add_4(ctx, 2);
        4
    };
    let (_, total): (bool, u32) = jet::add_32(ctx, sum);
    assert!(jet::eq_32(total, 11));
}"#;
        assert_same_cmr(chain, block);
    }
}

mod diagnostics {
    use super::*;

    /// The property CMR equality cannot check: a broken step is blamed on its
    /// own line. Walked across every interior position, because a lowering that
    /// reported the chain's span would still pass every test above.
    #[test]
    fn a_broken_step_is_blamed_on_its_own_line() {
        // `jet::version()` is a u32 where a u256 is wanted, so whichever step
        // holds it is the one that fails to type-check.
        const GOOD: &str = "jet::sha_256_ctx_8_add_32(ctx, jet::outputs_hash()),";
        const BAD: &str = "jet::sha_256_ctx_8_add_32(ctx, jet::version()),";

        let interior = 4;
        for broken in 0..interior {
            let steps: Vec<&str> = (0..interior)
                .map(|i| if i == broken { BAD } else { GOOD })
                .collect();
            let source = format!(
                "fn main() {{\n    let msg: u256 = chain!(ctx = jet::sha_256_ctx_8_init(),\n        {}\n        jet::sha_256_ctx_8_finalize(ctx));\n{TAIL}",
                steps.join("\n        ")
            );

            // The seed sits on line 2, so interior step `i` is on line 3 + i.
            let expected_line = 3 + broken;
            let (message, line, _) = first_error_at(&source);
            assert_eq!(
                line, expected_line,
                "breaking step {broken} should be blamed on line {expected_line}, not {line} ({message})"
            );
        }
    }

    #[test]
    fn an_uninferable_step_names_the_obstacle_and_suggests_an_annotation() {
        let source = format!(
            r#"fn main() {{
    let msg: u256 = chain!(ctx = jet::sha_256_ctx_8_init(),
        dbg!(jet::sha_256_ctx_8_add_32(ctx, jet::genesis_block_hash())),
        jet::sha_256_ctx_8_finalize(ctx));
{TAIL}"#
        );
        let (message, line, help) = first_error_at(&source);
        assert!(
            message.contains("takes its type from its surroundings"),
            "{message}"
        );
        assert_eq!(line, 3, "should blame the `dbg!` step, not line {line}");
        assert_eq!(
            help.as_deref(),
            Some("annotate the step, as in `ctx: <Type> = ...`"),
            "the message should name the fix, and name it with the chain's own hole"
        );
    }

    #[test]
    fn a_step_that_is_not_a_call_says_so() {
        let source = format!(
            r#"fn main() {{
    let msg: u256 = chain!(ctx = jet::sha_256_ctx_8_init(),
        (ctx, ctx),
        jet::sha_256_ctx_8_finalize(ctx));
{TAIL}"#
        );
        assert!(
            error_of(&source).contains("this step is not a call"),
            "{}",
            error_of(&source)
        );
    }

    #[test]
    fn rejected_shapes() {
        let cases = [
            (
                "chain!(ctx = jet::sha_256_ctx_8_init())",
                "needs a seed and at least one step",
            ),
            (
                "chain!(jet::sha_256_ctx_8_init(), jet::sha_256_ctx_8_finalize(ctx))",
                "first step of a `chain!` must bind the hole",
            ),
            (
                "chain!(ctx = jet::sha_256_ctx_8_init(), other: Ctx8 = jet::sha_256_ctx_8_add_32(ctx, jet::outputs_hash()), jet::sha_256_ctx_8_finalize(ctx))",
                "cannot rebind `other`",
            ),
            (
                "chain!(ctx = jet::sha_256_ctx_8_init(), jet::sha_256_ctx_8_add_32(ctx, jet::outputs_hash()), ctx: u256 = jet::sha_256_ctx_8_finalize(ctx))",
                "binding the hole there has no effect",
            ),
        ];

        for (chain, expected) in cases {
            let source = format!("fn main() {{\n    let msg: u256 = {chain};\n{TAIL}");
            let error = error_of(&source);
            assert!(
                error.contains(expected),
                "expected {expected:?} in:\n{error}\n\nsource:\n{source}"
            );
        }
    }

    /// A trailing comma is ordinary punctuation, not an empty final step.
    #[test]
    fn a_trailing_comma_is_accepted() {
        let source = format!(
            r#"fn main() {{
    let msg: u256 = chain!(ctx = jet::sha_256_ctx_8_init(),
        jet::sha_256_ctx_8_add_32(ctx, jet::outputs_hash()),
        jet::sha_256_ctx_8_finalize(ctx),);
{TAIL}"#
        );
        let _ = cmr_of(&source);
    }
}

mod gating {
    use super::*;

    #[test]
    fn chain_requires_its_unstable_feature() {
        let source = format!(
            r#"fn main() {{
    let msg: u256 = chain!(ctx = jet::sha_256_ctx_8_init(),
        jet::sha_256_ctx_8_finalize(ctx));
{TAIL}"#
        );
        let error = compile(&source, UnstableFeatures::none())
            .expect_err("chain! should be gated behind -Z chain");
        assert!(error.contains("chain"), "{error}");
    }
}

mod round_trip {
    use super::*;

    /// `Display` must produce something that parses back to the same tree. The
    /// fuzz target for this (`display_parse_tree`) is disabled, so the chain
    /// arms of `ExprTree` have no other coverage.
    #[test]
    fn display_round_trips_through_the_parser() {
        let sources = [
            // bare steps
            r#"fn main() {
    let msg: u256 = chain!(ctx = jet::sha_256_ctx_8_init(), jet::sha_256_ctx_8_finalize(ctx));
}"#,
            // an annotated interior step, and an untyped seed binding
            r#"fn main() {
    let msg: u256 = chain!(ctx = jet::sha_256_ctx_8_init(), ctx: Ctx8 = dbg!(jet::sha_256_ctx_8_add_32(ctx, jet::outputs_hash())), jet::sha_256_ctx_8_finalize(ctx));
}"#,
            // a typed seed binding
            r#"fn main() {
    let msg: u256 = chain!(ctx: Ctx8 = jet::sha_256_ctx_8_init(), jet::sha_256_ctx_8_add_32(ctx, jet::outputs_hash()), jet::sha_256_ctx_8_finalize(ctx));
}"#,
            // nested: a chain as an argument to another chain's step
            r#"fn main() {
    let msg: u256 = chain!(ctx = jet::sha_256_ctx_8_init(), jet::sha_256_ctx_8_add_32(ctx, chain!(inner = jet::sha_256_ctx_8_init(), jet::sha_256_ctx_8_finalize(inner))), jet::sha_256_ctx_8_finalize(ctx));
}"#,
        ];

        for source in sources {
            let parsed = Program::parse_from_str(source)
                .unwrap_or_else(|e| panic!("should parse:\n{source}\n{e:?}"));
            let printed = parsed.to_string();
            let reparsed = Program::parse_from_str(printed.as_str())
                .unwrap_or_else(|e| panic!("Display output should parse:\n{printed}\n{e:?}"));
            assert_eq!(
                parsed, reparsed,
                "Display output should parse to the original program:\n{printed}"
            );
        }
    }
}
