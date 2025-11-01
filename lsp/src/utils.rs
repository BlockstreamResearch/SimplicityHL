use std::num::NonZeroUsize;

use miniscript::iter::TreeLike;

use crate::error::LspError;
use ropey::Rope;
use simplicityhl::parse;
use tower_lsp_server::lsp_types;

fn position_le(a: &simplicityhl::error::Position, b: &simplicityhl::error::Position) -> bool {
    (a.line < b.line) || (a.line == b.line && a.col <= b.col)
}

fn position_ge(a: &simplicityhl::error::Position, b: &simplicityhl::error::Position) -> bool {
    (a.line > b.line) || (a.line == b.line && a.col >= b.col)
}

pub fn span_contains(a: &simplicityhl::error::Span, b: &simplicityhl::error::Span) -> bool {
    position_le(&a.start, &b.start) && position_ge(&a.end, &b.end)
}

/// Convert [`simplicityhl::error::Span`] to [`tower_lsp_server::lsp_types::Position`]
///
/// Converting is required because `simplicityhl::error::Span` using their own versions of `Position`,
/// which contains non-zero column and line, so they are always starts with one.
/// `Position` required for diagnostic starts with zero
pub fn span_to_positions(
    span: &simplicityhl::error::Span,
) -> Result<(lsp_types::Position, lsp_types::Position), LspError> {
    let start_line = u32::try_from(span.start.line.get())?;
    let start_col = u32::try_from(span.start.col.get())?;
    let end_line = u32::try_from(span.end.line.get())?;
    let end_col = u32::try_from(span.end.col.get())?;

    Ok((
        lsp_types::Position {
            line: start_line - 1,
            character: start_col - 1,
        },
        lsp_types::Position {
            line: end_line - 1,
            character: end_col - 1,
        },
    ))
}

/// Convert [`tower_lsp_server::lsp_types::Position`] to [`simplicityhl::error::Span`]
///
/// Useful when [`tower_lsp_server::lsp_types::Position`] represents some singular point.
pub fn position_to_span(
    position: lsp_types::Position,
) -> Result<simplicityhl::error::Span, LspError> {
    let start_line = NonZeroUsize::try_from((position.line + 1) as usize)?;
    let start_col = NonZeroUsize::try_from((position.character + 1) as usize)?;

    Ok(simplicityhl::error::Span {
        start: simplicityhl::error::Position {
            line: start_line,
            col: start_col,
        },
        end: simplicityhl::error::Position {
            line: start_line,
            col: start_col,
        },
    })
}

/// Get document comments, using lines above given line index. Only used to
/// get documentation for custom functions.
pub fn get_comments_from_lines(line: u32, rope: &Rope) -> String {
    let mut lines = Vec::new();

    if line == 0 {
        return String::new();
    }

    for i in (0..line).rev() {
        let Some(rope_slice) = rope.get_line(i as usize) else {
            break;
        };
        let text = rope_slice.to_string();

        if text.starts_with("///") {
            let doc = text
                .strip_prefix("///")
                .unwrap_or("")
                .trim_end()
                .to_string();
            lines.push(doc);
        } else {
            break;
        }
    }

    lines.reverse();

    let mut result = String::new();
    let mut prev_line_was_text = false;

    for line in lines {
        let trimmed = line.trim();

        let is_md_block = trimmed.is_empty()
            || trimmed.starts_with('#')
            || trimmed.starts_with('-')
            || trimmed.starts_with('*')
            || trimmed.starts_with('>')
            || trimmed.starts_with("```")
            || trimmed.starts_with("    ");

        if result.is_empty() {
            result.push_str(trimmed);
        } else if prev_line_was_text && !is_md_block {
            result.push(' ');
            result.push_str(trimmed);
        } else {
            result.push('\n');
            result.push_str(trimmed);
        }

        prev_line_was_text = !trimmed.is_empty() && !is_md_block;
    }

    result
}

/// Find [`simplicityhl::parse::Call`] which contains given [`simplicityhl::error::Span`], which also have minimal Span.
pub fn find_related_call<'a>(
    functions: &'a [&'a parse::Function],
    token_span: simplicityhl::error::Span,
) -> Result<Option<&'a simplicityhl::parse::Call>, LspError> {
    let func = functions
        .iter()
        .find(|func| span_contains(func.span(), &token_span))
        .ok_or(LspError::CallNotFound(
            "Span of the call is not inside function.".into(),
        ))?;

    let call = parse::ExprTree::Expression(func.body())
        .pre_order_iter()
        .filter_map(|expr| {
            if let parse::ExprTree::Call(call) = expr {
                // Only include if call span can be obtained
                get_call_span(call).ok().map(|span| (call, span))
            } else {
                None
            }
        })
        .filter(|(_, span)| span_contains(span, &token_span))
        .map(|(call, _)| call)
        .last();

    Ok(call)
}

pub fn get_call_span(
    call: &simplicityhl::parse::Call,
) -> Result<simplicityhl::error::Span, LspError> {
    let length = call.name().to_string().len();

    let end_column = usize::from(call.span().start.col) + length;

    Ok(simplicityhl::error::Span {
        start: call.span().start,
        end: simplicityhl::error::Position {
            line: call.span().start.line,
            col: NonZeroUsize::try_from(end_column)?,
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use ropey::Rope;

    #[test]
    fn test_get_comments_from_lines() {
        let text = Rope::from_str("/// This is a test.\n/// It has two lines.\nfn func() {}");
        let result = get_comments_from_lines(2, &text);
        assert_eq!(result, "This is a test. It has two lines.");

        let text = Rope::from_str("/// # Title\n/// - Point one\n/// - Point two\nfn func() {}");
        let result = get_comments_from_lines(3, &text);
        assert_eq!(result, "# Title\n- Point one\n- Point two");

        let text = Rope::from_str(
            "/// This is not part of the doc \n\n/// This is part of the doc\nfn func() {}",
        );
        let result = get_comments_from_lines(3, &text);
        assert_eq!(result, "This is part of the doc");

        let text = Rope::from_str("fn func() {}");
        let result = get_comments_from_lines(0, &text);
        assert_eq!(result, "");
    }
}
