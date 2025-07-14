use std::fs::File;
use std::io;

use simfony::simplicity::jet::{Elements, Jet};
use simfony::types::TypeDeconstructible;

mod jet;

/// Write a SimplicityHL jet as a Rust function to the sink.
fn write_jet<W: io::Write>(jet: Elements, w: &mut W) -> io::Result<()> {
    for line in jet::documentation(jet).lines() {
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
    let parameters = simfony::jet::source_type(jet);
    for (i, ty) in parameters.iter().enumerate() {
        let identifier = (b'a' + i as u8) as char;
        if i == parameters.len() - 1 {
            write!(w, "{identifier}: {ty}")?;
        } else {
            write!(w, "{identifier}: {ty}, ")?;
        }
    }
    let target = simfony::jet::target_type(jet);
    match target.is_unit() {
        true => writeln!(w, ") {{")?,
        false => writeln!(w, ") -> {} {{", simfony::jet::target_type(jet))?,
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

    for jet in category.iter().cloned() {
        writeln!(w)?;
        write_jet(jet, w)?;
    }

    Ok(())
}

fn main() -> io::Result<()> {
    for category in jet::Category::ALL {
        let file_name = format!("{category}.rs");
        let mut file = File::create(file_name)?;
        write_module(category, &mut file)?;
    }

    Ok(())
}
