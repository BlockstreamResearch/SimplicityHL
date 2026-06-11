use std::cell::RefCell;
use std::rc::Rc;

use simplicityhl::ast::CoreJetHinter;
use simplicityhl::simplicity::jet::CoreEnv;
use simplicityhl::tracker::DefaultTracker;
use simplicityhl::{Arguments, TemplateProgram, WitnessValues};

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
