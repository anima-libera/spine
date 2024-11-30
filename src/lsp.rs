use std::cell::Cell;
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use serde_json::Value;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use crate::lang::{
	parse_to_ast, AstProgram, AstStatement, LineStartTable, LspPosition, SourceCode,
};

struct SourceFileData {
	source: Arc<SourceCode>,
	ast: AstProgram,
}

struct Backend {
	client: Client,
	source_files: Mutex<HashMap<PathBuf, SourceFileData>>,
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
	async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
		Ok(InitializeResult {
			server_info: None,
			capabilities: ServerCapabilities {
				text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
				position_encoding: Some(PositionEncodingKind::UTF8),
				hover_provider: Some(HoverProviderCapability::Simple(true)),
				completion_provider: Some(CompletionOptions {
					trigger_characters: Some(vec![]),
					..Default::default()
				}),
				..Default::default()
			},
		})
	}

	async fn initialized(&self, _: InitializedParams) {
		self
			.client
			.log_message(MessageType::INFO, "initialized")
			.await;
	}

	async fn shutdown(&self) -> Result<()> {
		self.client.log_message(MessageType::INFO, "shutdown").await;
		Ok(())
	}

	async fn did_change_watched_files(&self, _: DidChangeWatchedFilesParams) {
		self
			.client
			.log_message(MessageType::INFO, "did change watched files")
			.await;
	}

	async fn did_open(&self, params: DidOpenTextDocumentParams) {
		let source_file_path = params.text_document.uri.to_file_path().unwrap();
		let text = std::fs::read_to_string(&source_file_path).unwrap();
		let line_starts = LineStartTable::compute_for_text(&text);
		let source = Arc::new(SourceCode {
			text,
			name: source_file_path.to_str().unwrap().to_string(),
			line_starts,
		});
		let ast = parse_to_ast(Arc::clone(&source));
		let source_file = SourceFileData { source, ast };
		self
			.source_files
			.lock()
			.unwrap()
			.insert(source_file_path, source_file);

		self.client.log_message(MessageType::INFO, "did open").await;
	}

	async fn did_change(&self, params: DidChangeTextDocumentParams) {
		let source_file_path = params.text_document.uri.to_file_path().unwrap();
		//let source_file = self.source_files.lock().unwrap().get_mut(&source_file_path);
		let text = params.content_changes.first().unwrap().text.clone();
		let line_starts = LineStartTable::compute_for_text(&text);
		let source = Arc::new(SourceCode {
			text,
			name: source_file_path.to_str().unwrap().to_string(),
			line_starts,
		});
		let ast = parse_to_ast(Arc::clone(&source));
		let source_file = SourceFileData { source, ast };
		self
			.source_files
			.lock()
			.unwrap()
			.insert(source_file_path, source_file);
		self
			.client
			.log_message(MessageType::INFO, "did change")
			.await;
	}

	async fn did_close(&self, _: DidCloseTextDocumentParams) {
		self
			.client
			.log_message(MessageType::INFO, "did close")
			.await;
	}

	async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
		if params.context.is_some_and(|context| {
			context
				.trigger_character
				.is_some_and(|trigger_character| trigger_character.starts_with('`'))
		}) {
			Ok(Some(CompletionResponse::Array(vec![
				CompletionItem {
					label: "kwexit".to_string(),
					insert_text: Some("kwexit".to_string()),
					detail: Some("( -- ) Terminate execution".to_string()),
					kind: Some(CompletionItemKind::KEYWORD),
					documentation: Some(Documentation::MarkupContent(MarkupContent {
						kind: MarkupKind::Markdown,
						value: "Explicit keyword\n\n\
							Calls the `exit` syscall, which terminates the process execution."
							.to_string(),
					})),
					..CompletionItem::default()
				},
				CompletionItem {
					label: "kwprintchar".to_string(),
					insert_text: Some("kwprintchar".to_string()),
					detail: Some("( char -- ) Prints character".to_string()),
					kind: Some(CompletionItemKind::KEYWORD),
					documentation: Some(Documentation::MarkupContent(MarkupContent {
						kind: MarkupKind::Markdown,
						value: "Explicit keyword\n\n\
							Calls the `write` syscall with a string made of the provided character."
							.to_string(),
					})),
					..CompletionItem::default()
				},
				CompletionItem {
					label: "kwprintstr".to_string(),
					insert_text: Some("kwprintstr".to_string()),
					detail: Some("( ptr len -- ) Prints string".to_string()),
					kind: Some(CompletionItemKind::KEYWORD),
					documentation: Some(Documentation::MarkupContent(MarkupContent {
						kind: MarkupKind::Markdown,
						value: "Explicit keyword\n\n\
							Calls the `write` syscall with the given pointer and length."
							.to_string(),
					})),
					..CompletionItem::default()
				},
				CompletionItem {
					label: "kwadd".to_string(),
					insert_text: Some("kwadd".to_string()),
					detail: Some("( a b -- (a+b) ) Adds two numbers".to_string()),
					kind: Some(CompletionItemKind::KEYWORD),
					documentation: Some(Documentation::MarkupContent(MarkupContent {
						kind: MarkupKind::Markdown,
						value: "Explicit keyword\n\n\
							Pops number A, pops number B, pushes the result of A + B."
							.to_string(),
					})),
					..CompletionItem::default()
				},
			])))
		} else {
			Ok(None)
		}
	}

	async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
		let source_file_path = params
			.text_document_position_params
			.text_document
			.uri
			.to_file_path()
			.unwrap();
		let source_file_lock = self.source_files.lock();
		let Some(source_file) = source_file_lock.as_ref().unwrap().get(&source_file_path) else {
			return Ok(None);
		};
		let pos = params.text_document_position_params.position;
		let statement = 'statement_search: {
			for statement in source_file.ast.statements.iter() {
				if statement.span.contains_lsp_position(LspPosition {
					line_number: pos.line,
					index_in_bytes_in_line: pos.character,
				}) {
					break 'statement_search statement;
				}
			}
			return Ok(None);
		};
		let bit_of_code = statement.span.as_str();
		let line_range = statement.span.line_range();
		let documentation = format!(
			"{}\n\n{}",
			match statement.specific_statement {
				AstStatement::Empty => "Empty statement".to_string(),
				AstStatement::Code { ref instructions } =>
					format!("Code statement of {} insructions", instructions.len()),
			},
			if line_range.0 == line_range.1 {
				format!("On line {}", line_range.0 + 1)
			} else {
				format!("On lines {}-{}", line_range.0 + 1, line_range.1 + 1)
			}
		);
		let range = statement.span.to_lsp_positions();
		let highlight_range = Range {
			start: Position {
				line: range.start.line_number,
				character: range.start.index_in_bytes_in_line,
			},
			end: Position {
				line: range.end.line_number,
				character: range.end.index_in_bytes_in_line,
			},
		};
		Ok(Some(Hover {
			contents: HoverContents::Markup(MarkupContent {
				kind: MarkupKind::Markdown,
				value: format!("```spine\n{bit_of_code}\n```\n---\n{documentation}"),
			}),
			range: Some(highlight_range),
		}))
	}
}

pub(crate) fn run_lsp() {
	let async_runtime = tokio::runtime::Builder::new_current_thread()
		.thread_name("Tokio Runtime Thread")
		.enable_io()
		.build()
		.unwrap();

	async_runtime.block_on(async {
		let (stdin, stdout) = (tokio::io::stdin(), tokio::io::stdout());
		let (service, socket) =
			LspService::new(|client| Backend { client, source_files: Mutex::new(HashMap::new()) });
		Server::new(stdin, stdout, socket).serve(service).await;
	});
}
