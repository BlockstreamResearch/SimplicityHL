use macros::*;

include_simf!("examples/source_simf/options2.simf");

fn main() -> Result<(), String> {
    println!("Testing roundtrip conversion for witness values...\n");

    // Create a witness struct with test data
    let original_witness = options2::build_witness::Options2Witness {
        path: simplicityhl::either::Either::Right(simplicityhl::either::Either::Left((
            true, 100, 200,
        ))),
    };

    println!("Original witness: {:?}\n", original_witness);

    // Convert to WitnessValues
    let witness_values = original_witness.build_witness();
    println!("Built WitnessValues successfully");

    // Convert back to struct
    let recovered_witness =
        options2::build_witness::Options2Witness::from_witness(&witness_values)?;
    println!("Recovered witness: {:?}\n", recovered_witness);

    println!("✓ Roundtrip test passed!");
    Ok(())
}
