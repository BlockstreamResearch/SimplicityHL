use ropey::Rope;
use serde_json::Value;

use std::collections::HashMap;
use std::str::FromStr;
use std::sync::Arc;
use tokio::sync::RwLock;

use tower_lsp_server::jsonrpc::Result;
use tower_lsp_server::lsp_types::{
    CompletionOptions, CompletionParams, CompletionResponse, Diagnostic,
    DidChangeConfigurationParams, DidChangeTextDocumentParams, DidChangeWatchedFilesParams,
    DidChangeWorkspaceFoldersParams, DidCloseTextDocumentParams, DidOpenTextDocumentParams,
    DidSaveTextDocumentParams, ExecuteCommandParams, GotoDefinitionParams, GotoDefinitionResponse,
    Hover, HoverParams, HoverProviderCapability, InitializeParams, InitializeResult,
    InitializedParams, Location, MarkupContent, MarkupKind, MessageType, OneOf, Range,
    ReferenceParams, SaveOptions, SemanticTokensParams, SemanticTokensResult, ServerCapabilities,
    TextDocumentSyncCapability, TextDocumentSyncKind, TextDocumentSyncOptions,
    TextDocumentSyncSaveOptions, Uri, WorkDoneProgressOptions, WorkspaceFoldersServerCapabilities,
    WorkspaceServerCapabilities,
};
use tower_lsp_server::{Client, LanguageServer};

use simplicityhl::{
    ast,
    error::{RichError, WithFile},
    parse,
    parse::ParseFromStr,
};

use crate::completion::{self, CompletionProvider};
use crate::error::LspError;
use crate::function::Functions;
use crate::utils::{
    find_all_references, find_function_name_range, find_related_call, get_call_span,
    get_comments_from_lines, position_to_span, span_contains, span_to_positions,
};

#[derive(Debug)]
struct Document {
    functions: Functions,
    text: Rope,
}

#[derive(Debug)]
pub struct Backend {
    client: Client,

    document_map: Arc<RwLock<HashMap<Uri, Document>>>,

    completion_provider: CompletionProvider,
}

struct TextDocumentItem<'a> {
    uri: Uri,
    text: &'a str,
    version: Option<i32>,
}

impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            server_info: None,
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Options(
                    TextDocumentSyncOptions {
                        open_close: Some(true),
                        change: Some(TextDocumentSyncKind::FULL),
                        save: Some(TextDocumentSyncSaveOptions::SaveOptions(SaveOptions {
                            include_text: Some(true),
                        })),
                        ..Default::default()
                    },
                )),
                completion_provider: Some(CompletionOptions {
                    resolve_provider: Some(false),
                    trigger_characters: Some(vec![":".to_string(), "<".to_string()]),
                    work_done_progress_options: WorkDoneProgressOptions::default(),
                    all_commit_characters: None,
                    completion_item: None,
                }),
                workspace: Some(WorkspaceServerCapabilities {
                    workspace_folders: Some(WorkspaceFoldersServerCapabilities {
                        supported: Some(true),
                        change_notifications: Some(OneOf::Left(true)),
                    }),
                    file_operations: None,
                }),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                definition_provider: Some(OneOf::Left(true)),
                references_provider: Some(OneOf::Left(true)),
                ..ServerCapabilities::default()
            },
        })
    }

    async fn initialized(&self, _: InitializedParams) {}

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_change_workspace_folders(&self, _: DidChangeWorkspaceFoldersParams) {}

    async fn did_change_configuration(&self, _: DidChangeConfigurationParams) {}

    async fn did_change_watched_files(&self, _: DidChangeWatchedFilesParams) {}

    async fn execute_command(&self, _: ExecuteCommandParams) -> Result<Option<Value>> {
        Ok(None)
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        self.on_change(TextDocumentItem {
            uri: params.text_document.uri,
            text: &params.text_document.text,
            version: Some(params.text_document.version),
        })
        .await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        self.on_change(TextDocumentItem {
            text: &params.content_changes[0].text,
            uri: params.text_document.uri,
            version: Some(params.text_document.version),
        })
        .await;
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        if let Some(text) = params.text {
            self.on_change(TextDocumentItem {
                uri: params.text_document.uri,
                text: &text,
                version: None,
            })
            .await;
        }
    }

    async fn did_close(&self, _: DidCloseTextDocumentParams) {}

    async fn semantic_tokens_full(
        &self,
        _: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
        Ok(None)
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let documents = self.document_map.read().await;
        let uri = &params.text_document_position.text_document.uri;

        let doc = documents
            .get(uri)
            .ok_or(LspError::DocumentNotFound(uri.to_owned()))?;

        let pos = params.text_document_position.position;

        let line = doc
            .text
            .lines()
            .nth(pos.line as usize)
            .ok_or(LspError::Internal("Rope proccesing error".into()))?;

        let slice = line
            .get_slice(..pos.character as usize)
            .ok_or(LspError::ConversionFailed(
                "Rope to slice conversion failed".into(),
            ))?;

        let prefix = slice.as_str().ok_or(LspError::ConversionFailed(
            "RopeSlice to str conversion failed".into(),
        ))?;

        let completions = self
            .completion_provider
            .process_completions(prefix, &doc.functions.functions_and_docs())
            .map(CompletionResponse::Array);

        Ok(completions)
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let documents = self.document_map.read().await;
        let uri = &params.text_document_position_params.text_document.uri;

        let doc = documents
            .get(uri)
            .ok_or(LspError::DocumentNotFound(uri.to_owned()))?;
        let functions = doc.functions.functions();

        let token_pos = params.text_document_position_params.position;

        let token_span = position_to_span(token_pos)?;
        let Ok(Some(call)) = find_related_call(&functions, token_span) else {
            return Ok(None);
        };

        let call_span = get_call_span(call)?;
        let (start, end) = span_to_positions(&call_span)?;

        let description = match call.name() {
            parse::CallName::Jet(jet) => {
                let element =
                    simplicityhl::simplicity::jet::Elements::from_str(format!("{jet}").as_str())
                        .map_err(|err| LspError::ConversionFailed(err.to_string()))?;

                let template = completion::jet::jet_to_template(element);
                format!(
                    "Jet function\n```simplicityhl\nfn {}({}) -> {}\n```\n---\n\n{}",
                    template.display_name,
                    template.args.join(", "),
                    template.return_type,
                    template.description
                )
            }
            parse::CallName::Custom(func) => {
                let (function, function_doc) =
                    doc.functions
                        .get(func.as_inner())
                        .ok_or(LspError::FunctionNotFound(format!(
                            "Function {func} is not found"
                        )))?;

                let template = completion::function_to_template(function, function_doc);
                format!(
                    "```simplicityhl\nfn {}({}) -> {}\n```\n---\n{}",
                    template.display_name,
                    template.args.join(", "),
                    template.return_type,
                    template.description
                )
            }
            other => {
                let Some(template) = completion::builtin::match_callname(other) else {
                    return Ok(None);
                };
                format!(
                    "Built-in function\n```simplicityhl\nfn {}({}) -> {}\n```\n---\n{}",
                    template.display_name,
                    template.args.join(", "),
                    template.return_type,
                    template.description
                )
            }
        };

        Ok(Some(Hover {
            contents: tower_lsp_server::lsp_types::HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value: description,
            }),
            range: Some(Range { start, end }),
        }))
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let documents = self.document_map.read().await;
        let uri = &params.text_document_position_params.text_document.uri;

        let doc = documents
            .get(uri)
            .ok_or(LspError::DocumentNotFound(uri.to_owned()))?;
        let functions = doc.functions.functions();

        let token_position = params.text_document_position_params.position;
        let token_span = position_to_span(token_position)?;

        let Ok(Some(call)) = find_related_call(&functions, token_span) else {
            let Some(func) = functions
                .iter()
                .find(|func| span_contains(func.span(), &token_span))
            else {
                return Ok(None);
            };
            let range = find_function_name_range(func, &doc.text)?;

            if token_position <= range.end && token_position >= range.start {
                return Ok(Some(GotoDefinitionResponse::from(Location::new(
                    uri.clone(),
                    range,
                ))));
            }
            return Ok(None);
        };

        match call.name() {
            simplicityhl::parse::CallName::Custom(func) => {
                let function =
                    doc.functions
                        .get_func(func.as_inner())
                        .ok_or(LspError::FunctionNotFound(format!(
                            "Function {func} is not found"
                        )))?;

                let (start, end) = span_to_positions(function.as_ref())?;
                Ok(Some(GotoDefinitionResponse::from(Location::new(
                    uri.clone(),
                    Range::new(start, end),
                ))))
            }
            _ => Ok(None),
        }
    }

    async fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let documents = self.document_map.read().await;
        let uri = &params.text_document_position.text_document.uri;

        let doc = documents
            .get(uri)
            .ok_or(LspError::DocumentNotFound(uri.to_owned()))?;
        let functions = doc.functions.functions();

        let token_position = params.text_document_position.position;

        let token_span = position_to_span(token_position)?;

        let call_name =
            find_related_call(&functions, token_span)?.map(simplicityhl::parse::Call::name);

        match call_name {
            Some(parse::CallName::Custom(_)) | None => {}
            Some(name) => {
                return Ok(Some(
                    find_all_references(&functions, name)?
                        .iter()
                        .map(|range| Location {
                            range: *range,
                            uri: uri.clone(),
                        })
                        .collect(),
                ));
            }
        }

        let Some(func) = functions.iter().find(|func| match call_name {
            Some(parse::CallName::Custom(name)) => func.name() == name,
            _ => span_contains(func.span(), &token_span),
        }) else {
            return Ok(None);
        };

        let range = find_function_name_range(func, &doc.text)?;

        if (token_position <= range.end && token_position >= range.start) || call_name.is_some() {
            Ok(Some(
                find_all_references(&functions, &parse::CallName::Custom(func.name().clone()))?
                    .into_iter()
                    .chain(std::iter::once(range))
                    .map(|range| Location {
                        range,
                        uri: uri.clone(),
                    })
                    .collect(),
            ))
        } else {
            Ok(None)
        }
    }
}

impl Backend {
    pub fn new(client: Client) -> Self {
        Self {
            client,
            document_map: Arc::new(RwLock::new(HashMap::new())),
            completion_provider: CompletionProvider::new(),
        }
    }

    /// Function which executed on change of file (`did_save`, `did_open` or `did_change` methods)
    async fn on_change(&self, params: TextDocumentItem<'_>) {
        let (err, document) = parse_program(params.text);

        let mut documents = self.document_map.write().await;
        if let Some(doc) = document {
            documents.insert(params.uri.clone(), doc);
        } else if let Some(doc) = documents.get_mut(&params.uri) {
            doc.text = Rope::from_str(params.text);
        }

        match err {
            None => {
                self.client
                    .publish_diagnostics(params.uri.clone(), vec![], params.version)
                    .await;
            }
            Some(err) => {
                let (start, end) = match span_to_positions(err.span()) {
                    Ok(result) => result,
                    Err(err) => {
                        self.client
                            .log_message(
                                MessageType::ERROR,
                                format!("Catch error while parsing span: {err}"),
                            )
                            .await;
                        return;
                    }
                };

                self.client
                    .publish_diagnostics(
                        params.uri.clone(),
                        vec![Diagnostic::new_simple(
                            Range::new(start, end),
                            err.error().to_string(),
                        )],
                        params.version,
                    )
                    .await;
            }
        }
    }
}

/// Create [`Document`] using parsed program and code.
fn create_document(program: &simplicityhl::parse::Program, text: &str) -> Document {
    let mut document = Document {
        functions: Functions::new(),
        text: Rope::from_str(text),
    };

    program
        .items()
        .iter()
        .filter_map(|item| {
            if let parse::Item::Function(func) = item {
                Some(func)
            } else {
                None
            }
        })
        .for_each(|func| {
            let start_line = u32::try_from(func.as_ref().start.line.get()).unwrap_or_default() - 1;

            document.functions.insert(
                func.name().to_string(),
                func.to_owned(),
                get_comments_from_lines(start_line, &document.text),
            );
        });

    document
}

/// Parse program using [`simplicityhl`] compiler and return [`RichError`],
/// which used in Diagnostic. Also create [`Document`] from parsed program.
fn parse_program(text: &str) -> (Option<RichError>, Option<Document>) {
    let program = match parse::Program::parse_from_str(text) {
        Ok(p) => p,
        Err(e) => return (Some(e), None),
    };

    (
        ast::Program::analyze(&program).with_file(text).err(),
        Some(create_document(&program, text)),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_program() -> &'static str {
        "fn add(a: u32, b: u32) -> u32 { let (_, res): (bool, u32) = jet::add_32(a, b); res }
         fn main() {}"
    }

    fn invalid_program_on_ast() -> &'static str {
        "fn add(a: u32, b: u32) -> u32 {}"
    }

    fn invalid_program_on_parsing() -> &'static str {
        "fn add(a: u32 b: u32) -> u32 {}"
    }

    #[test]
    fn test_parse_program_valid() {
        let (err, doc) = parse_program(sample_program());
        assert!(err.is_none(), "Expected no parsing error");
        let doc = doc.expect("Expected Some(Document)");
        assert_eq!(doc.functions.map.len(), 2);
    }

    #[test]
    fn test_parse_program_invalid_ast() {
        let (err, doc) = parse_program(invalid_program_on_ast());
        assert!(
            err.unwrap()
                .to_string()
                .contains("Expected expression of type `u32`, found type `()`"),
            "Expected error on return type"
        );
        assert!(doc.is_some(), "Expected problem in AST build, not parse");
    }

    #[test]
    fn test_parse_program_invalid_parse() {
        let (err, doc) = parse_program(invalid_program_on_parsing());
        assert!(
            err.unwrap().to_string().contains("Grammar error"),
            "Expected `Grammar error`"
        );
        assert!(doc.is_none(), "Expected no document to return");
    }
}
