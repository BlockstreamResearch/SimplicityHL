use base64::display::Base64Display;
use base64::engine::general_purpose::STANDARD;
use clap::{Arg, ArgAction, Command};
use anyhow::Context;

use simfony::{Arguments, CompiledProgram};
use std::env;

fn main() -> anyhow::Result<()> {
    let command = {
        Command::new(env!("CARGO_BIN_NAME"))
        .about(
            "\
            Compile the given Simfony program and print the resulting Simplicity base64 string.\n\
            If a Simfony witness is provided, then use it to satisfy the program (requires \
            feature 'serde' to be enabled).\
            "
        )
        .arg(
            Arg::new("prog_file")
            .required(true)
            .value_name("PROGRAM_FILE")
            .action(ArgAction::Set)
            .help("Simfony program file to build")
        )
    };

    #[cfg(feature = "serde")]
    let command = {
        command.arg(
            Arg::new("wit_file")
            .value_name("WITNESS_FILE")
            .action(ArgAction::Set)
            .help("File containing the witness data")
        )
    };

    let matches = {
        command
        .arg(
            Arg::new("debug")
            .long("debug")
            .action(ArgAction::SetTrue)
            .help("Include debug symbols in the output")
        )
        .get_matches()
    };

    let prog_file = matches.get_one::<String>("prog_file").unwrap();
    let prog_path = std::path::Path::new(prog_file);
    let prog_text = {
        std::fs::read_to_string(prog_path)
        .with_context(|| format!("Failed to read {}", prog_path.display()))?
    };
    let include_debug_symbols = matches.get_flag("debug");

    let compiled = CompiledProgram::new(prog_text, Arguments::default(), include_debug_symbols)?;

    #[cfg(feature = "serde")]
    let witness_opt = {
        matches
        .get_one::<String>("wit_file")
        .map(|wit_file| -> anyhow::Result<simfony::WitnessValues> {
            let wit_path = std::path::Path::new(wit_file);
            let wit_text = {
                std::fs::read_to_string(wit_path)
                .with_context(|| format!("Failed to read {}", wit_path.display()))?
            };
            let witness = {
                serde_json::from_str::<simfony::WitnessValues>(&wit_text)
                .with_context(|| format!("Failed to parse file {}", wit_path.display()))?
            };
            Ok(witness)
        })
        .transpose()?
    };
    #[cfg(not(feature = "serde"))]
    let witness_opt: Option<simfony::WitnessValues> = None;

    if let Some(witness) = witness_opt {
        let satisfied = compiled.satisfy(witness)?;
        let (program_bytes, witness_bytes) = satisfied.redeem().encode_to_vec();
        println!(
            "Program:\n{}",
            Base64Display::new(&program_bytes, &STANDARD)
        );
        println!(
            "Witness:\n{}",
            Base64Display::new(&witness_bytes, &STANDARD)
        );
    } else {
        let program_bytes = compiled.commit().encode_to_vec();
        println!(
            "Program:\n{}",
            Base64Display::new(&program_bytes, &STANDARD)
        );
    }

    Ok(())
}

