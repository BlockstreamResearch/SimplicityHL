//! Checks that parse time grows linearly, not exponentially, with nesting depth.
//!
//! A combinator parser can silently parse the same sub-tree more than once. It
//! happens wherever two alternatives can both begin at the current token and the
//! choice between them is only settled after the whole sub-tree has been consumed:
//! the first alternative parses the sub-tree, fails on whatever follows it,
//! backtracks and throws that work away, and the second alternative parses the very
//! same sub-tree again. One such spot doubles the work for every level of nesting,
//! which is exponential in nesting depth.
//!
//! So this measures each nesting construct in the grammar directly: it parses inputs
//! that nest one construct to increasing depths, and reports how the cost grows.
//! Linear parsing gives a growth factor near 1; a construct that is parsed twice per
//! level gives one near 4 across the two levels between samples.
//!
//! Run it with:
//!
//! ```text
//! cargo test --test parser_scaling -- --ignored --nocapture
//! ```
//!
//! It is ignored by default because it times the parser, and timings are too noisy
//! to gate CI on. Treat it as an instrument to reach for when touching the grammar,
//! and add a case whenever the grammar grows a new way to nest.

use simplicityhl::error::DiagnosticManager;
use simplicityhl::parse::{self, ParseFromStrWithErrors};
use simplicityhl::UnstableFeatures;

/// Nesting depths to sample.
///
/// The ceiling is kept low so that a parser with an exponential construct still
/// finishes and reports rather than appearing to hang: at a doubling per level it
/// needs about a second for the deepest of these, and four times that for every two
/// further levels.
const DEPTHS: [usize; 5] = [8, 10, 12, 14, 16];

/// Fastest of this many parses is taken for each depth, to shed scheduler noise.
const REPEATS: u32 = 3;

/// Largest tolerated ratio between the deepest and the shallowest sample.
///
/// Linear parsing predicts about 2, since the deepest input is twice the size of
/// the shallowest. Parsing one construct twice per level predicts 2^8 = 256. The
/// bound sits between the two with roughly an order of magnitude of room on either
/// side, so neither a slow machine nor a fast one can turn one verdict into the
/// other.
const MAX_RATIO: f64 = 20.0;

/// A way for the grammar to nest, and how to write one `depth` levels deep.
struct Construct {
    name: &'static str,
    /// Builds a program whose only deep nesting is `depth` levels of this construct.
    build: fn(usize) -> String,
}

/// One entry per recursive parser in the grammar.
const CONSTRUCTS: &[Construct] = &[
    // Expressions nest through blocks and through parentheses, and each level holds
    // exactly one element that carries no `;`, which is the shape whose statement
    // and final-expression readings both start at the same token.
    Construct {
        name: "blocks",
        build: |depth| wrap_expression(&"{".repeat(depth), &"}".repeat(depth)),
    },
    Construct {
        name: "parentheses",
        build: |depth| wrap_expression(&"(".repeat(depth), &")".repeat(depth)),
    },
    // Types have their own recursive parser, and three ways to nest.
    Construct {
        name: "option types",
        build: |depth| wrap_type(&"Option<".repeat(depth), &">".repeat(depth)),
    },
    Construct {
        name: "tuple types",
        build: |depth| wrap_type(&"(".repeat(depth), &",)".repeat(depth)),
    },
    Construct {
        name: "array types",
        build: |depth| wrap_type(&"[".repeat(depth), &"; 1]".repeat(depth)),
    },
];

/// A program whose only deep nesting is `open`/`close` around an expression.
fn wrap_expression(open: &str, close: &str) -> String {
    format!("fn main() {{\n    let x: u32 = {open}0{close};\n    assert!(jet::eq_32(x, 0));\n}}")
}

/// A program whose only deep nesting is `open`/`close` around a type.
fn wrap_type(open: &str, close: &str) -> String {
    format!("fn main() {{\n    let x: {open}u8{close} = witness::W;\n}}")
}

/// Parse `input`, asserting it is accepted, and return the fastest of [`REPEATS`] runs.
fn time_parse(input: &str, name: &str) -> std::time::Duration {
    (0..REPEATS)
        .map(|_| {
            let start = std::time::Instant::now();
            let mut diagnostics = DiagnosticManager::new();
            let parsed = parse::Program::parse_from_str_with_errors(
                0,
                input,
                &UnstableFeatures::all(),
                &mut diagnostics,
            );
            let elapsed = start.elapsed();
            assert!(
                parsed.is_some(),
                "the {name} case must parse, so that this measures parsing and not \
                 how fast the grammar rejects it"
            );
            elapsed
        })
        .min()
        .expect("REPEATS is not zero")
}

/// Time one construct across [`DEPTHS`], printing a row per depth, and return the
/// ratio between the deepest and the shallowest sample.
fn measure(construct: &Construct) -> f64 {
    println!("  {}", construct.name);

    let mut timings: Vec<std::time::Duration> = Vec::new();
    for depth in DEPTHS {
        let elapsed = time_parse(&(construct.build)(depth), construct.name);
        let growth = timings.last().map_or_else(
            || "-".to_string(),
            |previous| format!("{:.2}x", elapsed.as_secs_f64() / previous.as_secs_f64()),
        );
        println!("    depth {depth:>3}  {elapsed:>9.2?}  {growth:>6}");
        timings.push(elapsed);
    }

    let shallowest = timings.first().expect("DEPTHS is not empty").as_secs_f64();
    let deepest = timings.last().expect("DEPTHS is not empty").as_secs_f64();
    deepest / shallowest
}

#[test]
fn parsing_scales_linearly_with_nesting_depth() {
    let first_depth = DEPTHS.first().expect("DEPTHS is not empty");
    let last_depth = DEPTHS.last().expect("DEPTHS is not empty");

    println!();
    println!("  nesting construct, time per depth, and growth across two levels");
    println!();

    // Every construct is measured before anything is asserted, so that a failure
    // reports the whole table: which constructs scale and which do not is what
    // points at the offending rule.
    let ratios: Vec<(&str, f64)> = CONSTRUCTS
        .iter()
        .map(|construct| (construct.name, measure(construct)))
        .collect();

    println!();
    println!("  depth {last_depth} against depth {first_depth} (linear is about 2x, doubling per level is about 256x)");
    for (name, ratio) in &ratios {
        let verdict = if *ratio < MAX_RATIO {
            "ok"
        } else {
            "TOO STEEP"
        };
        println!("    {name:<14} {ratio:>8.1}x  {verdict}");
    }
    println!();

    let too_steep: Vec<&str> = ratios
        .iter()
        .filter(|(_, ratio)| *ratio >= MAX_RATIO)
        .map(|(name, _)| *name)
        .collect();

    assert!(
        too_steep.is_empty(),
        "parse time grows faster than linearly in the nesting depth of: {}. \
         Something in the grammar parses one of these constructs more than once per \
         level, most likely two alternatives that both start at the same token and \
         are only told apart after the whole sub-tree has been consumed.",
        too_steep.join(", ")
    );
}
