use base64::display::Base64Display;
use base64::engine::general_purpose::STANDARD;
use clap::{Arg, ArgAction, Command};

use simplicityhl::{Arguments, CompiledProgram};
use std::env;

// Directly returning Result<(), String> prints the error using Debug
// Add indirection via run() to print errors using Display
fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let command = {
        Command::new(env!("CARGO_BIN_NAME"))
            .about(
                "\
                Compile the given SimplicityHL program and print the resulting Simplicity base64 string.\n\
                If a SimplicityHL witness is provided, then use it to satisfy the program (requires \
                feature 'serde' to be enabled).\
                ",
            )
            .arg(
                Arg::new("prog_file")
                    .required(true)
                    .value_name("PROGRAM_FILE")
                    .action(ArgAction::Set)
                    .help("SimplicityHL program file to build"),
            )
    };

    #[cfg(feature = "serde")]
    let command = {
        command.arg(
            Arg::new("wit_file")
                .value_name("WITNESS_FILE")
                .action(ArgAction::Set)
                .help("File containing the witness data"),
        )
    };

    let matches = {
        command
            .arg(
                Arg::new("debug")
                    .long("debug")
                    .action(ArgAction::SetTrue)
                    .help("Include debug symbols in the output"),
            )
            .get_matches()
    };

    let prog_file = matches.get_one::<String>("prog_file").unwrap();
    let prog_path = std::path::Path::new(prog_file);
    let prog_text = std::fs::read_to_string(prog_path).map_err(|e| e.to_string())?;
    let include_debug_symbols = matches.get_flag("debug");

    let compiled = CompiledProgram::new(prog_text, Arguments::default(), include_debug_symbols)?;

    #[cfg(feature = "serde")]
    let witness_opt = {
        matches
            .get_one::<String>("wit_file")
            .map(|wit_file| -> Result<simplicityhl::WitnessValues, String> {
                let wit_path = std::path::Path::new(wit_file);
                let wit_text = std::fs::read_to_string(wit_path).map_err(|e| e.to_string())?;
                let witness =
                    serde_json::from_str::<simplicityhl::WitnessValues>(&wit_text).unwrap();
                Ok(witness)
            })
            .transpose()?
    };
    #[cfg(not(feature = "serde"))]
    let witness_opt: Option<simplicityhl::WitnessValues> = None;

    if let Some(witness) = witness_opt {
        let satisfied = compiled.satisfy(witness)?;
        let (program_bytes, witness_bytes) = satisfied.redeem().to_vec_with_witness();
        println!(
            "Program:\n{}",
            Base64Display::new(&program_bytes, &STANDARD)
        );
        println!(
            "Witness:\n{}",
            Base64Display::new(&witness_bytes, &STANDARD)
        );
    } else {
        let program_bytes = compiled.commit().to_vec_without_witness();
        println!(
            "Program:\n{}",
            Base64Display::new(&program_bytes, &STANDARD)
        );
    }

    Ok(())
}
