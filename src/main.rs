use base64::display::Base64Display;
use base64::engine::general_purpose::STANDARD;
use clap::{Arg, ArgAction, Command};

use simplicityhl::{AbiMeta, CompiledProgram, DependencyMap, SourceName};
use std::{env, fmt, sync::Arc};

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
/// The compilation output.
struct Output {
    /// Simplicity program result, base64 encoded.
    program: String,
    /// Simplicity witness result, base64 encoded, if the .wit file was provided.
    witness: Option<String>,
    /// Simplicity program ABI metadata to the program which the user provides.
    abi_meta: Option<AbiMeta>,
}

impl fmt::Display for Output {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Program:\n{}", self.program)?;
        if let Some(witness) = &self.witness {
            writeln!(f, "Witness:\n{}", witness)?;
        }
        if let Some(witness) = &self.abi_meta {
            writeln!(f, "ABI meta:\n{:?}", witness)?;
        }
        Ok(())
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
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
            .arg(
                Arg::new("dependencies")
                    .long("dep")
                    .value_name("[CONTEXT:]ALIAS=PATH")
                    .action(ArgAction::Append)
                    .help("Link a dependency, optionally scoped to a specific module (e.g., --dep ./libs/merkle:math=./libs/math)"),
            )
            .arg(
                Arg::new("wit_file")
                    .long("wit")
                    .short('w')
                    .value_name("WITNESS_FILE")
                    .action(ArgAction::Set)
                    .help("File containing the witness data"),
            )
            .arg(
                Arg::new("args_file")
                    .long("args")
                    .short('a')
                    .value_name("ARGUMENTS_FILE")
                    .action(ArgAction::Set)
                    .help("File containing the arguments data"),
            )
            .arg(
                Arg::new("debug")
                    .long("debug")
                    .action(ArgAction::SetTrue)
                    .help("Include debug symbols in the output"),
            )
            .arg(
                Arg::new("json")
                    .long("json")
                    .action(ArgAction::SetTrue)
                    .help("Output in JSON"),
            )
            .arg(
                Arg::new("abi")
                    .long("abi")
                    .action(ArgAction::SetTrue)
                    .help("Additional ABI .simf contract types"),
            )
    };

    let matches = command.get_matches();

    let prog_file = matches.get_one::<String>("prog_file").unwrap();
    let main_path = std::fs::canonicalize(prog_file).unwrap_or_else(|_| {
        panic!("Failed to find the program file: '{}'", prog_file);
    });
    let main_path = main_path.as_path();
    let prog_text = std::fs::read_to_string(main_path).map_err(|e| e.to_string())?;
    let include_debug_symbols = matches.get_flag("debug");
    let output_json = matches.get_flag("json");
    let abi_param = matches.get_flag("abi");

    #[cfg(feature = "serde")]
    let args_opt: simplicityhl::Arguments = match matches.get_one::<String>("args_file") {
        None => simplicityhl::Arguments::default(),
        Some(args_file) => {
            let args_path = std::path::Path::new(&args_file);
            let args_text = std::fs::read_to_string(args_path).map_err(|e| e.to_string())?;
            serde_json::from_str::<simplicityhl::Arguments>(&args_text)?
        }
    };
    #[cfg(not(feature = "serde"))]
    let args_opt: simplicityhl::Arguments = if matches.contains_id("args_file") {
        return Err(
            "Program was compiled without the 'serde' feature and cannot process .args files."
                .into(),
        );
    } else {
        simplicityhl::Arguments::default()
    };

    let lib_args = matches
        .get_many::<String>("dependencies")
        .unwrap_or_default();

    let mut libraries = DependencyMap::new();

    for arg in lib_args {
        // Split by '=' to separate the target path
        let (left_side, path_str) = arg.split_once('=').unwrap_or_else(|| {
            eprintln!(
                "Error: Library argument must be in format [CONTEXT:]ALIAS=PATH, got '{arg}'"
            );
            std::process::exit(1);
        });

        // Split by ':' to check for a specific context
        let (context_path, alias) = if let Some((ctx_str, alias_str)) = left_side.split_once(':') {
            // Specific context provided (e.g., merkle:base_math=...)
            // We convert it to PathBuf so it shares the same type as main_path
            (std::path::Path::new(ctx_str), alias_str)
        } else {
            // No context provided (e.g., math=...). Bind it to the main file!
            (main_path, left_side)
        };

        // Insert and handle the potential io::Error!
        // We convert path_str to PathBuf so it maches the tyep of context_path
        if let Err(e) = libraries.insert(
            context_path,
            alias.to_string(),
            std::path::Path::new(path_str),
        ) {
            eprintln!("Error: {e}");
            std::process::exit(1);
        }
    }

    let compiled = match CompiledProgram::new(
        SourceName::Real(Arc::from(main_path)),
        Arc::from(libraries),
        prog_text,
        args_opt,
        include_debug_symbols,
    ) {
        Ok(program) => program,
        Err(e) => {
            eprintln!("{}", e);
            std::process::exit(1);
        }
    };

    #[cfg(feature = "serde")]
    let witness_opt = matches
        .get_one::<String>("wit_file")
        .map(|wit_file| -> Result<simplicityhl::WitnessValues, String> {
            let wit_path = std::path::Path::new(wit_file);
            let wit_text = std::fs::read_to_string(wit_path).map_err(|e| e.to_string())?;
            let witness = serde_json::from_str::<simplicityhl::WitnessValues>(&wit_text).unwrap();
            Ok(witness)
        })
        .transpose()?;
    #[cfg(not(feature = "serde"))]
    let witness_opt = if matches.contains_id("wit_file") {
        return Err(
            "Program was compiled without the 'serde' feature and cannot process .wit files."
                .into(),
        );
    } else {
        None
    };

    let (program_bytes, witness_bytes) = match witness_opt {
        Some(witness) => {
            let satisfied = compiled.satisfy(witness)?;
            let (program_bytes, witness_bytes) = satisfied.redeem().to_vec_with_witness();
            (program_bytes, Some(witness_bytes))
        }
        None => {
            let program_bytes = compiled.commit().to_vec_without_witness();
            (program_bytes, None)
        }
    };

    let abi_opt = if abi_param {
        Some(compiled.generate_abi_meta()?)
    } else {
        None
    };

    let output = Output {
        program: Base64Display::new(&program_bytes, &STANDARD).to_string(),
        witness: witness_bytes.map(|bytes| Base64Display::new(&bytes, &STANDARD).to_string()),
        abi_meta: abi_opt,
    };

    if output_json {
        #[cfg(not(feature = "serde"))]
        return Err(
            "Program was compiled without the 'serde' feature and cannot output JSON.".into(),
        );
        #[cfg(feature = "serde")]
        println!("{}", serde_json::to_string(&output)?);
    } else {
        println!("{}", output);
    }

    Ok(())
}
