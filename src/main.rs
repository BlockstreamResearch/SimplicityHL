use base64::display::Base64Display;
use base64::engine::general_purpose::STANDARD;
use clap::{Arg, ArgAction, Command};

use simplicityhl::ast::{CoreJetHinter, ElementsJetHinter, JetHinter};
use simplicityhl::error::should_color;
#[cfg(feature = "external-jets")]
use simplicityhl::jet::external::{init_external_jet_lib, ExternalJetHinter};
use simplicityhl::version::SimcDirective;
use simplicityhl::{
    resolution::DependencyMapBuilder, source::CanonPath, source::CanonSourceFile, AbiMeta,
    TemplateAst,
};
use simplicityhl::{UnstableFeature, UnstableFeatures};
use std::path::Path;
use std::str::FromStr;
use std::{env, fmt, io};

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
/// The compilation output.
struct Output {
    /// Simplicity program result, base64 encoded.
    program: String,
    /// Simplicity witness result, base64 encoded, if the .wit file was provided.
    witness: Option<String>,
    /// Simplicity program ABI metadata to the program which the user provides.
    abi_meta: Option<AbiMeta>,
    /// Commitment Merkle Root (CMR) of the program, hex encoded.
    cmr: String,
    /// Version of the compiler that produced this output. Different compiler
    /// versions can produce different CMRs from the same source, so the version
    /// travels with the artifact as metadata (it is not part of the program).
    compiler_version: &'static str,
    /// Compilation target used to select the jet set. Different targets can
    /// produce different CMRs from the same source and compiler version.
    target: String,
}

impl fmt::Display for Output {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Program:\n{}", self.program)?;
        writeln!(f, "CMR:\n{}", self.cmr)?;
        writeln!(f, "Compiler version:\n{}", self.compiler_version)?;
        writeln!(f, "Target:\n{}", self.target)?;
        if let Some(witness) = &self.witness {
            writeln!(f, "Witness:\n{}", witness)?;
        }
        if let Some(witness) = &self.abi_meta {
            writeln!(f, "ABI meta:\n{:?}", witness)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
enum Target {
    Elements,
    Core,
    #[cfg(feature = "external-jets")]
    External(String),
}

struct TargetParseError(String);

impl fmt::Debug for TargetParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for TargetParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for TargetParseError {}

const TARGET_HELP: &str = "Target platform for compilation: elements, core, or external:<path> (external targets require the 'external-jets' feature)";

impl fmt::Display for Target {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Target::Elements => f.write_str("elements"),
            Target::Core => f.write_str("core"),
            #[cfg(feature = "external-jets")]
            Target::External(path) => write!(f, "external:{path}"),
        }
    }
}

impl Target {
    #[allow(clippy::unnecessary_wraps)]
    fn jet_hinter(&self) -> Result<Box<dyn JetHinter>, Box<dyn std::error::Error>> {
        match self {
            Target::Elements => Ok(Box::new(ElementsJetHinter::new())),
            Target::Core => Ok(Box::new(CoreJetHinter::new())),
            #[cfg(feature = "external-jets")]
            Target::External(path) => {
                // SAFETY: `path` was canonicalized and verified to be a regular file while
                // parsing the target argument.
                //
                // The user MUST trust the library to implement the external jet ABI.
                //
                // Initialization verifies that every required symbol exists.
                unsafe {
                    init_external_jet_lib(path)?;
                }

                Ok(Box::new(ExternalJetHinter::new()))
            }
        }
    }
}

impl FromStr for Target {
    type Err = TargetParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Some(path) = s.strip_prefix("external:") {
            #[cfg(feature = "external-jets")]
            {
                return validate_external_jet_lib_path(path).map(Target::External);
            }

            #[cfg(not(feature = "external-jets"))]
            {
                let _ = path;
                return Err(TargetParseError(
                    "External targets require a compiler built with the 'external-jets' feature"
                        .to_string(),
                ));
            }
        }

        match s {
            "elements" => Ok(Target::Elements),
            "core" => Ok(Target::Core),
            _ => Err(TargetParseError(format!(
                "Unknown target: {}. Use one of: elements, core, external:<path>",
                s
            ))),
        }
    }
}

#[cfg(feature = "external-jets")]
fn validate_external_jet_lib_path(path: &str) -> Result<String, TargetParseError> {
    if path.is_empty() {
        return Err(TargetParseError(
            "Invalid target: external target path cannot be empty".to_string(),
        ));
    }

    let canonical_path = std::fs::canonicalize(path).map_err(|error| {
        TargetParseError(format!(
            "Invalid external target path '{}': {error}",
            Path::new(path).display()
        ))
    })?;

    if !canonical_path.is_file() {
        return Err(TargetParseError(format!(
            "Invalid external target path '{}': path is not a regular file",
            canonical_path.display()
        )));
    }

    canonical_path
        .into_os_string()
        .into_string()
        .map_err(|path| {
            TargetParseError(format!(
                "Invalid external target path '{}': path is not valid UTF-8",
                Path::new(&path).display()
            ))
        })
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
                Arg::new("project_root")
                    .long("project-root")
                    .value_name("PROJECT_ROOT")
                    .action(ArgAction::Set)
                    .help(
                        "Project root for resolving `crate::` imports (defaults to the entry file's directory)",
                    ),
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
            .arg(
                Arg::new("unstable_features")
                    .long("unstable-feature")
                    .short('Z')
                    .value_name("FEATURE")
                    .action(ArgAction::Append)
                    .value_parser(clap::value_parser!(UnstableFeature))
                    .help(simplicityhl::UnstableFeature::help_message()),
            )
            .arg(
                Arg::new("target")
                    .long("target")
                    .short('t')
                    .value_name("TARGET")
                    .default_value("elements")
                    .action(ArgAction::Set)
                    .value_parser(clap::value_parser!(Target))
                    .help(TARGET_HELP),
            )
    };

    let matches = command.get_matches();

    let prog_file = matches.get_one::<String>("prog_file").unwrap();
    let main_path = CanonPath::canonicalize(Path::new(prog_file))?;
    let main_text = std::fs::read_to_string(main_path.as_path()).map_err(|e| e.to_string())?;
    // Entry file only; deps are still version-checked in the driver, just not warned.
    if let Some(warning) = SimcDirective::missing_warning(&main_text) {
        eprintln!("Warning: {warning}");
    }
    let include_debug_symbols = matches.get_flag("debug");
    let output_json = matches.get_flag("json");
    let abi_param = matches.get_flag("abi");

    let unstable_features = matches
        .get_many::<UnstableFeature>("unstable_features")
        .map_or_else(UnstableFeatures::none, |features| {
            UnstableFeatures::new(features.copied())
        });

    // Argument values are resolved against the program's parameter types,
    // so the file is parsed here and resolved once the template is built.
    #[cfg(feature = "serde")]
    let unresolved_args: Option<simplicityhl::UnresolvedValues> =
        match matches.get_one::<String>("args_file") {
            None => None,
            Some(args_file) => {
                let args_path = Path::new(&args_file);
                let args_text = std::fs::read_to_string(args_path).map_err(|e| e.to_string())?;
                Some(serde_json::from_str(&args_text)?)
            }
        };
    #[cfg(not(feature = "serde"))]
    if matches.contains_id("args_file") {
        return Err(
            "Program was compiled without the 'serde' feature and cannot process .args files."
                .into(),
        );
    }

    let target = matches
        .get_one::<Target>("target")
        .expect("target argument should have a default value");

    let dep_args = matches
        .get_many::<String>("dependencies")
        .unwrap_or_default();

    let canon_root = match matches.get_one::<String>("project_root") {
        Some(project_root) => CanonPath::canonicalize(Path::new(project_root))?,
        None => main_path
            .as_path()
            .parent()
            .and_then(|p| CanonPath::canonicalize(p).ok())
            .ok_or("Failed to determine project root directory from entry file")?,
    };

    if !main_path.starts_with(&canon_root) {
        return Err(format!(
            "Entry file '{}' is outside project root '{}'",
            main_path.as_path().display(),
            canon_root.as_path().display()
        )
        .into());
    }

    let mut builder = DependencyMapBuilder::new();

    for arg in dep_args {
        let (left_side, path_str) = arg.split_once('=').unwrap_or_else(|| {
            eprintln!(
                "Error: Library argument must be in format [CONTEXT:]ALIAS=PATH, got '{arg}'"
            );
            std::process::exit(1);
        });

        // Use the right most `:` because on Windows, there might be a drive letter, e.g. C:\
        let (context_path, alias) = if let Some((ctx_str, alias_str)) = left_side.rsplit_once(':') {
            // Specific context provided (e.g., merkle:base_math=...)
            // We convert it to PathBuf so it shares the same type as main_path
            let canon_path = CanonPath::canonicalize(Path::new(ctx_str))?;
            (canon_path, alias_str)
        } else {
            // No context provided (e.g., math=...). Bind it to the workspace root!
            (canon_root.clone(), left_side)
        };

        let target_path = CanonPath::canonicalize(Path::new(path_str))?;
        builder.add_dependency(context_path, alias.to_string(), target_path);
    }

    let dependencies = match builder.build(canon_root.clone()) {
        Ok(map) => map,
        Err(e) => {
            eprintln!("Error: {e}");
            std::process::exit(1);
        }
    };

    let source = CanonSourceFile::new(main_path.clone(), std::sync::Arc::from(main_text));
    let template = match TemplateAst::new_with_dep(
        source,
        &dependencies,
        &unstable_features,
        target.jet_hinter()?,
    ) {
        Ok(program) => program,
        Err(diags) => {
            let stderr = io::stderr();
            let with_color = should_color(&stderr);
            let mut lock = stderr.lock();

            diags
                .render(with_color, &mut lock)
                .expect("writing to stderr");
            std::process::exit(1);
        }
    };

    #[cfg(feature = "serde")]
    let args_opt: simplicityhl::Arguments = match unresolved_args {
        None => simplicityhl::Arguments::default(),
        Some(unresolved) => unresolved.resolve(template.parameters())?,
    };
    #[cfg(not(feature = "serde"))]
    let args_opt = simplicityhl::Arguments::default();

    let compiled = match template.instantiate(args_opt, include_debug_symbols) {
        Ok(program) => program,
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(1);
        }
    };

    #[cfg(feature = "serde")]
    let witness_opt = matches
        .get_one::<String>("wit_file")
        .map(|wit_file| -> Result<simplicityhl::WitnessValues, String> {
            let wit_path = Path::new(wit_file);
            let wit_text = std::fs::read_to_string(wit_path).map_err(|e| e.to_string())?;
            let unresolved = serde_json::from_str::<simplicityhl::UnresolvedValues>(&wit_text)
                .map_err(|e| e.to_string())?;
            unresolved.resolve(compiled.witness_types())
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
            let satisfied = match compiled.satisfy(witness) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("{e}");
                    std::process::exit(1);
                }
            };
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

    let cmr_hex = compiled.commit().cmr().to_string();
    let output = Output {
        program: Base64Display::new(&program_bytes, &STANDARD).to_string(),
        witness: witness_bytes.map(|bytes| Base64Display::new(&bytes, &STANDARD).to_string()),
        abi_meta: abi_opt,
        cmr: cmr_hex,
        compiler_version: compiled.compiler_version(),
        target: target.to_string(),
    };

    if output_json {
        #[cfg(not(feature = "serde"))]
        {
            return Err(
                "Program was compiled without the 'serde' feature and cannot output JSON.".into(),
            );
        }

        #[cfg(feature = "serde")]
        {
            println!("{}", serde_json::to_string(&output)?);
            return Ok(());
        }
    }

    println!("{}", output);

    Ok(())
}
