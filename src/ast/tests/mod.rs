mod consts;
mod enums;
#[cfg(feature = "fmt")]
mod literals;
mod modules;
mod multi_error;
mod scope_resolution;

use crate::ast::{ElementsJetHinter, Program};
use crate::driver::tests::setup_graph;
use crate::TemplateAst;

pub(super) fn analyze(src: &str) -> Result<(), String> {
    TemplateAst::new_with_unstable(
        src,
        &crate::UnstableFeatures::all(),
        Box::new(ElementsJetHinter::new()),
    )
    .map(|_| ())
    .map_err(|e| e.to_string())
}

pub(super) fn analyze_multifile(files: Vec<(&str, &str)>) -> Result<(), String> {
    let (graph, _ids, _dir, mut diagnostics) = setup_graph(files);

    let Some(driver_program) = graph.linearize_and_assemble(&mut diagnostics) else {
        return Err(diagnostics.render_to_string());
    };

    match Program::analyze(
        &driver_program,
        Box::new(ElementsJetHinter),
        &mut diagnostics,
    ) {
        Some(_) => Ok(()),
        None => Err(diagnostics
            .diagnostics()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n")),
    }
}
