use std::fs::{self, File};
use std::io;
use std::path::PathBuf;

use clap::{Arg, Command};
use serde::Serialize;

use simplicityhl::docs::jet;
use simplicityhl::docs::jet::JetInfo;
use simplicityhl::simplicity::jet::{Elements, Jet};
use simplicityhl::types::TypeDeconstructible;

#[derive(Serialize)]
struct JetObject {
    pub haskell_name: String,
    pub simplicityhl_name: String,
    pub section: String,
    pub input_type: String,
    pub output_type: String,
    pub description: String,
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub deprecated: bool,
}

/// Write a SimplicityHL jet as a Rust function to the sink.
fn write_jet<W: io::Write>(jet: Elements, w: &mut W) -> io::Result<()> {
    for line in jet.documentation().lines() {
        match line.is_empty() {
            true => writeln!(w, "///")?,
            false => writeln!(w, "/// {line}")?,
        }
    }
    writeln!(w, "///")?;
    writeln!(w, "/// ## Cost")?;
    writeln!(w, "///")?;
    writeln!(w, "/// {} mWU _(milli weight units)_", jet.cost())?;
    write!(w, "pub fn {jet}(")?;
    let parameters = simplicityhl::jet::source_type(jet);
    for (i, ty) in parameters.iter().enumerate() {
        let identifier = (b'a' + i as u8) as char;
        if i == parameters.len() - 1 {
            write!(w, "{identifier}: {ty}")?;
        } else {
            write!(w, "{identifier}: {ty}, ")?;
        }
    }
    let target = simplicityhl::jet::target_type(jet);
    match target.is_unit() {
        true => writeln!(w, ") {{")?,
        false => writeln!(w, ") -> {} {{", simplicityhl::jet::target_type(jet))?,
    }

    writeln!(w, "    todo!()")?;
    writeln!(w, "}}")
}

/// Write a category of jets as a Rust module to the sink.
fn write_module<W: io::Write>(category: jet::Category, w: &mut W) -> io::Result<()> {
    writeln!(w, "/* This file has been automatically generated. */")?;
    writeln!(w)?;
    writeln!(w, "{}", category.documentation())?;
    writeln!(w)?;
    writeln!(w, "#![allow(unused)]")?;
    writeln!(w, "#![allow(clippy::complexity)]")?;
    writeln!(w)?;
    writeln!(w, "use super::*;")?;

    for jet in category.iter().copied() {
        writeln!(w)?;
        write_jet(jet, w)?;
    }

    Ok(())
}

/// Generate Rust modules divided by category.
fn generate_modules(out_dir: PathBuf) -> Result<(), Box<dyn std::error::Error>> {
    fs::create_dir_all(&out_dir)?;

    for category in jet::Category::ALL {
        let file_name = format!("{category}.rs");
        let file_path = out_dir.join(file_name);
        let mut file = File::create(&file_path)?;
        write_module(category, &mut file)?;
    }

    println!(
        "Successfully generated Rust modules in: {}",
        out_dir.display()
    );
    Ok(())
}

/// Generate JSON file with jet documentation.
fn generate_docs(output_path: PathBuf) -> Result<(), Box<dyn std::error::Error>> {
    let generated_elements: Vec<JetObject> = jet::Category::ALL
        .into_iter()
        .flat_map(|category| {
            let section_name = category.to_pretty_string();

            category
                .iter()
                .map(move |&jet| JetObject {
                    haskell_name: format!("{:?}", jet),
                    simplicityhl_name: jet.to_string(),
                    section: section_name.clone(),
                    input_type: simplicityhl::jet::source_type(jet)
                        .iter()
                        .map(|ty| ty.to_string())
                        .collect::<Vec<_>>()
                        .join(", "),
                    output_type: simplicityhl::jet::target_type(jet).to_string(),
                    description: jet.documentation().to_string(),
                    deprecated: jet.is_deprecated(),
                })
                .collect::<Vec<_>>()
        })
        .collect();

    let json_string = serde_json::to_string_pretty(&generated_elements)?
        // Replacing Rust documentation links to render normally in MarkDown.
        .replace("[`", "`")
        .replace("`]", "`");

    fs::write(&output_path, json_string)?;

    println!("Successfully wrote JSON data to: {}", output_path.display());

    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let matches = Command::new("simplicityhl-gen")
        .about("Generates SimplicityHL Rust modules and JSON documentation for jets")
        .subcommand_required(true)
        .arg_required_else_help(true)
        .subcommand(
            Command::new("modules")
                .about("Generates SimplicityHL jets as Rust modules")
                .arg(
                    Arg::new("out_dir")
                        .short('o')
                        .long("out-dir")
                        .default_value(".")
                        .help("Optional directory to output the .rs files (defaults to current directory)"),
                ),
        )
        .subcommand(
            Command::new("docs")
                .about("Generates SimplicityHL documentation for jets as a JSON file")
                .arg(
                    Arg::new("output_path")
                        .required(true)
                        .help("Path to write the JSON documentation file"),
                ),
        )
        .get_matches();

    match matches.subcommand() {
        Some(("modules", sub_matches)) => {
            let out_dir = sub_matches.get_one::<String>("out_dir").unwrap();
            generate_modules(PathBuf::from(out_dir))?;
        }
        Some(("docs", sub_matches)) => {
            let output_path = sub_matches.get_one::<String>("output_path").unwrap();
            generate_docs(PathBuf::from(output_path))?;
        }
        _ => unreachable!("Exhausted list of subcommands and subcommand_required is true"),
    }

    Ok(())
}
