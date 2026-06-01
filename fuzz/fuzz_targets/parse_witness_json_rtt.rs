#![cfg_attr(fuzzing, no_main)]

#[cfg(fuzzing)]
fn do_test(witness_values: simplicityhl::WitnessValues) {
    let witness_text = serde_json::to_string(&witness_values)
        .expect("Witness map should be convertible into JSON");
    let parsed_witness_text =
        serde_json::from_str(&witness_text).expect("Witness JSON should be parseable");
    assert_eq!(
        witness_values, parsed_witness_text,
        "Witness JSON should parse to original witness map"
    );
}

#[cfg(not(fuzzing))]
fn main() {}

#[cfg(fuzzing)]
libfuzzer_sys::fuzz_target!(|data: simplicityhl::WitnessValues| do_test(data));
