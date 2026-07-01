use std::cell::RefCell;
use std::rc::Rc;

use simplicityhl::ast::CoreJetHinter;
use simplicityhl::simplicity::jet::CoreEnv;
use simplicityhl::str::WitnessName;
use simplicityhl::tracker::DefaultTracker;
use simplicityhl::value::{Value, ValueConstructible};
use simplicityhl::{Arguments, TemplateProgram, UnstableFeatures, WitnessValues};

const CORE_PROGRAM: &str = r#"fn main() {
    let (_, sum): (bool, u32) = jet::add_32(10, 20);
    assert!(jet::eq_32(sum, 30));
}"#;

fn satisfied_core_program() -> simplicityhl::SatisfiedProgram {
    TemplateProgram::new(CORE_PROGRAM, Box::new(CoreJetHinter::new()))
        .unwrap()
        .instantiate(Arguments::default(), true)
        .unwrap()
        .satisfy(WitnessValues::default())
        .unwrap()
}

#[test]
fn core_program_prunes_without_tracker() {
    let satisfied = satisfied_core_program();
    satisfied.redeem().prune(&CoreEnv::new()).unwrap();
}

#[test]
fn core_program_should_not_panic_with_core_tracker() {
    let satisfied = satisfied_core_program();
    let mut tracker =
        DefaultTracker::build(satisfied.debug_symbols(), Box::new(CoreJetHinter::new()));

    satisfied
        .redeem()
        .prune_with_tracker(&CoreEnv::new(), &mut tracker)
        .unwrap();
}

#[test]
fn core_enum_match_compiles_for_core_target() {
    // Regression: the enum-match desugaring must resolve its equality jet from the active
    // jet set. When compiling for the Core target, hardcoding an Elements jet would produce
    // a jet/target mismatch at commit time. Compiling all the way to a satisfied, pruned
    // program proves the desugared `eq_8` is a Core jet.
    const SRC: &str = r#"
        enum Coin { Heads = 1, Tails = 2 }
        fn main() {
            match witness::C {
                Coin::Heads => assert!(jet::eq_32(0, 0)),
                Coin::Tails => assert!(jet::eq_32(0, 0)),
            }
        }
    "#;

    let mut map = std::collections::HashMap::new();
    map.insert(WitnessName::from_str_unchecked("C"), Value::u8(1));

    let satisfied = TemplateProgram::new_with_unstable(
        SRC,
        &UnstableFeatures::all(),
        Box::new(CoreJetHinter::new()),
    )
    .unwrap()
    .instantiate(Arguments::default(), true)
    .unwrap()
    .satisfy(WitnessValues::from(map))
    .unwrap();

    satisfied.redeem().prune(&CoreEnv::new()).unwrap();
}

#[test]
fn core_program_traces_core_jets() {
    let satisfied = satisfied_core_program();
    let traced_jets = Rc::new(RefCell::new(Vec::new()));
    let traced_jets_clone = traced_jets.clone();
    let mut tracker =
        DefaultTracker::build(satisfied.debug_symbols(), Box::new(CoreJetHinter::new()))
            .with_jet_trace_sink(move |jet, _args, _result| {
                traced_jets_clone.borrow_mut().push(jet.to_string());
            });

    satisfied
        .redeem()
        .prune_with_tracker(&CoreEnv::new(), &mut tracker)
        .unwrap();

    assert!(
        traced_jets.borrow().iter().any(|jet| jet == "add_32"),
        "expected add_32 to be traced as a Core jet"
    );
}
