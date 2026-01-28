use simplicityhl_macros::*;

include_simf!(
    "/Users/ikripaka/Documents/Work_dl/SimplicityHL-copy/macros/examples/source_simf/options.simf"
);

fn main() -> Result<(), String> {
    let original_witness = derived_options::OptionsWitness {
        path: simplicityhl::either::Either::Right(simplicityhl::either::Either::Left((
            true, 100, 200,
        ))),
    };

    let witness_values = original_witness.build_witness();

    let recovered_witness = derived_options::OptionsWitness::from_witness(&witness_values)?;
    assert_eq!(original_witness, recovered_witness);

    Ok(())
}
