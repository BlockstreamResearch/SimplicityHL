use std::collections::HashSet;

use simplicity::dag::{DagLike, InternalSharing};
use simplicity::hashes::sha256;
use simplicity::jet::CoreEnv;
use simplicity::node::Inner;

use crate::ast::CoreJetHinter;
use crate::debug::TrackedCallName;
use crate::tracker::DefaultTracker;
use crate::value::ValueConstructible;
use crate::{
    Arguments, TemplateAst, TemplateProgramWitness, Value, WitnessNameToValueMap, WitnessValues,
};

#[test]
fn repeated_function_calls_preserve_sharing() {
    let depth = 12;
    let mut source = String::from("fn f0(x: u32) -> u32 { x }\n");
    for n in 1..=depth {
        source.push_str(&format!(
            "fn f{n}(x: u32) -> u32 {{ f{p}(f{p}(x)) }}\n",
            p = n - 1
        ));
    }
    source.push_str(&format!(
        "fn main() {{ assert!(jet::eq_32(f{depth}(1), 1)); }}"
    ));
    let template = TemplateAst::new(source, Box::new(CoreJetHinter)).unwrap();

    for debug in [false, true] {
        let compiled = template.instantiate(Arguments::default(), debug).unwrap();
        // Count retained nodes instead of timing: recompiling at every call
        // expands this small call graph into thousands of duplicate nodes.
        assert!(
            compiled
                .commit()
                .as_ref()
                .post_order_iter::<InternalSharing>()
                .count()
                <= 16 * depth + 64
        );
    }
}

#[test]
fn shared_bodies_preserve_call_kinds_and_encoding() {
    let source = r#"
fn sum(x: u32, acc: u32) -> u32 {
    let (_, next): (bool, u32) = jet::add_32(x, acc);
    next
}
fn step(acc: u32, stop: u8, counter: u8) -> Either<u32, u32> {
    let next: u32 = sum(1, acc);
    match jet::eq_8(counter, stop) {
        true => Left(next),
        false => Right(next),
    }
}
fn main() {
    assert!(jet::eq_32(sum(2, 3), 5));
    assert!(jet::eq_32(sum(4, 5), 9));
    assert!(jet::eq_32(fold::<sum, 4>(list![1, 2, 3], 0), 6));
    assert!(jet::eq_32(fold::<sum, 8>(list![4, 5], 1), 10));
    assert!(jet::eq_32(array_fold::<sum, 3>([1, 2, 3], 4), 10));
    assert!(jet::eq_32(array_fold::<sum, 1>([7], 8), 15));
    assert!(jet::eq_32(unwrap_left::<u32>(step(0, 0, 0)), 1));
    assert!(jet::eq_32(unwrap_left::<u32>(for_while::<step>(0, 2)), 3));
    assert!(jet::eq_32(unwrap_left::<u32>(for_while::<step>(4, 0)), 5));
}
"#;
    let template = TemplateAst::new(source, Box::new(CoreJetHinter)).unwrap();
    // Recorded before body caching. Sharing must preserve the wire encoding,
    // including debug commitments, across ordinary calls, folds, and loops.
    let hashes = [
        "2683a658d2f86fd6412d96cb5e46b14e24a9434968446a5ea651863c14454abc",
        "1d207d98ab4142978bcb97590a98459b918ffc5dc6ae5040bd389ba23f973403",
    ];
    for (debug, expected) in [false, true].into_iter().zip(hashes) {
        let compiled = template.instantiate(Arguments::default(), debug).unwrap();
        assert_eq!(
            sha256::Hash::hash(&compiled.commit().to_vec_without_witness()).to_string(),
            expected
        );
        compiled
            .satisfy(WitnessValues::default())
            .unwrap()
            .redeem()
            .prune(&CoreEnv::new())
            .unwrap();
    }
}

#[test]
fn body_cache_preserves_compilation_settings_and_debug_identity() {
    let source = r#"
mod left {
    pub fn check(x: u32) -> u32 {
        let _: u32 = dbg!(x);
        assert!(jet::le_32(x, param::LIMIT));
        x
    }
}
mod right {
    pub fn check(x: u32) -> u32 {
        let _: u32 = dbg!(x);
        assert!(jet::le_32(x, param::LIMIT));
        x
    }
}
use crate::left::check as check_left;
use crate::right::check as check_right;
fn main() {
    let x: u32 = witness::X;
    assert!(jet::eq_32(check_left(x), x));
    assert!(jet::eq_32(check_left(x), x));
    assert!(jet::eq_32(check_right(x), x));
}
"#;
    let template = TemplateAst::new_with_unstable(
        source,
        &crate::UnstableFeatures::all(),
        Box::new(CoreJetHinter),
    )
    .unwrap();
    for limit in [7, 42] {
        for debug in [false, true] {
            let arguments = Arguments::from_map(std::collections::HashMap::from([(
                TemplateProgramWitness::parameter_from_str("LIMIT"),
                Value::u32(limit),
            )]));
            let compiled = template.instantiate(arguments, debug).unwrap();
            let debug_cmrs: HashSet<_> = compiled
                .commit()
                .as_ref()
                .post_order_iter::<InternalSharing>()
                .filter_map(|item| match item.node.inner() {
                    Inner::AssertL(_, cmr)
                        if compiled.debug_symbols().get(cmr).is_some_and(|call| {
                            matches!(call.name(), TrackedCallName::Debug(_))
                        }) =>
                    {
                        Some(*cmr)
                    }
                    _ => None,
                })
                .collect();
            // Equal bodies at different declarations retain distinct debug spans.
            assert_eq!(debug_cmrs.len(), if debug { 2 } else { 0 });

            let witnesses = WitnessValues::from_map(std::collections::HashMap::from([(
                TemplateProgramWitness::witness_from_str("X"),
                Value::u32(limit),
            )]));
            let satisfied = compiled.satisfy(witnesses).unwrap();
            let mut values = Vec::new();
            let mut tracker =
                DefaultTracker::build(satisfied.debug_symbols(), Box::new(CoreJetHinter))
                    .with_debug_sink(|_, value| values.push(value.clone()));
            satisfied
                .redeem()
                .prune_with_tracker(&CoreEnv::new(), &mut tracker)
                .unwrap();
            drop(tracker);
            assert_eq!(values, vec![Value::u32(limit); if debug { 3 } else { 0 }]);
        }
    }
}
