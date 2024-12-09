#![allow(unused)] // For now, WIP stuff gets too yellow for my taste

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use spine_compiler::lang::{
	parse, CompilationError, CompilationWarning, HighInstruction, HighProgram, HighStatement,
	LspPosition, LspRange, Pos, SourceCode,
};

struct SourceFileData {
	source: Arc<SourceCode>,
	high_program: HighProgram,
}

struct SpineLanguageServer {
	client: Client,
	source_files: Mutex<HashMap<PathBuf, Arc<SourceFileData>>>,
}

impl SpineLanguageServer {
	fn get_source_file_data(&self, source_file_path: PathBuf) -> Option<Arc<SourceFileData>> {
		let mut source_file_lock = self.source_files.lock();
		if let Some(source_file) = source_file_lock.as_ref().unwrap().get(&source_file_path) {
			Some(Arc::clone(source_file))
		} else {
			let source = Arc::new(SourceCode::from_file(&source_file_path)?);
			let high_program = parse(Arc::clone(&source));
			let source_file = Arc::new(SourceFileData { source, high_program });
			source_file_lock
				.as_mut()
				.unwrap()
				.insert(source_file_path, Arc::clone(&source_file));
			Some(source_file)
		}
	}

	fn get_diagnostics(&self, source_file_path: PathBuf) -> Vec<Diagnostic> {
		let source_file = self.get_source_file_data(source_file_path);

		let mut diagnostics = vec![];
		if let Some(source_file) = source_file {
			let (errors, warnings) = source_file.high_program.get_errors_and_warnings();
			for error in errors {
				diagnostics.push(get_diagnostic_from_error(&error));
			}
			for warning in warnings {
				diagnostics.push(get_diagnostic_from_warning(&warning));
			}
		}

		diagnostics
	}
}

fn get_diagnostic_from_error(error: &CompilationError) -> Diagnostic {
	let range = lsp_range_into_range(error.span().to_lsp_range());
	Diagnostic {
		range,
		severity: Some(DiagnosticSeverity::ERROR),
		code: None,
		code_description: None,
		source: Some("spine".to_string()),
		message: error.message(),
		related_information: None,
		tags: None,
		data: None,
	}
}

fn get_diagnostic_from_warning(warning: &CompilationWarning) -> Diagnostic {
	let range = lsp_range_into_range(warning.span().to_lsp_range());
	Diagnostic {
		range,
		severity: Some(DiagnosticSeverity::WARNING),
		code: None,
		code_description: None,
		source: Some("spine".to_string()),
		message: warning.message(),
		related_information: None,
		tags: None,
		data: None,
	}
}

fn lsp_range_into_range(lsp_range: LspRange) -> Range {
	Range {
		start: Position {
			line: lsp_range.start.zero_based_line_number,
			character: lsp_range.start.index_in_bytes_in_line,
		},
		end: Position {
			line: lsp_range.end.zero_based_line_number,
			character: lsp_range.end.index_in_bytes_in_line,
		},
	}
}

#[tower_lsp::async_trait]
impl LanguageServer for SpineLanguageServer {
	async fn initialize(&self, _params: InitializeParams) -> Result<InitializeResult> {
		//params.capabilities.text_document.unwrap().diagnostic.unwrap().
		Ok(InitializeResult {
			server_info: Some(ServerInfo { name: "Spine language server".to_string(), version: None }),
			capabilities: ServerCapabilities {
				text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
				position_encoding: Some(PositionEncodingKind::UTF8),
				hover_provider: Some(HoverProviderCapability::Simple(true)),
				completion_provider: Some(CompletionOptions {
					trigger_characters: Some(vec![]),
					..Default::default()
				}),
				diagnostic_provider: Some(DiagnosticServerCapabilities::Options(DiagnosticOptions {
					identifier: None,
					inter_file_dependencies: true,
					workspace_diagnostics: false,
					work_done_progress_options: WorkDoneProgressOptions { work_done_progress: None },
				})),
				code_action_provider: Some(CodeActionProviderCapability::Options(CodeActionOptions {
					code_action_kinds: Some(vec![CodeActionKind::QUICKFIX]),
					work_done_progress_options: WorkDoneProgressOptions { work_done_progress: None },
					resolve_provider: None,
				})),
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
		let Some(source) = SourceCode::from_file(&source_file_path) else {
			return;
		};
		let source = Arc::new(source);
		let high_program = parse(Arc::clone(&source));
		let source_file = Arc::new(SourceFileData { source, high_program });
		self
			.source_files
			.lock()
			.unwrap()
			.insert(source_file_path.clone(), source_file);

		let diagnostics = self.get_diagnostics(source_file_path);
		self
			.client
			.publish_diagnostics(params.text_document.uri, diagnostics, None)
			.await;

		self.client.log_message(MessageType::INFO, "did open").await;
	}

	async fn did_change(&self, params: DidChangeTextDocumentParams) {
		let source_file_path = params.text_document.uri.to_file_path().unwrap();
		//let source_file = self.source_files.lock().unwrap().get_mut(&source_file_path);
		let source_text = params.content_changes.first().unwrap().text.clone();
		let name = source_file_path.to_str().unwrap().to_string();
		let source = Arc::new(SourceCode::from_string(source_text, name));
		let high_program = parse(Arc::clone(&source));
		let source_file = Arc::new(SourceFileData { source, high_program });
		self
			.source_files
			.lock()
			.unwrap()
			.insert(source_file_path.clone(), source_file);

		let diagnostics = self.get_diagnostics(source_file_path);
		self
			.client
			.publish_diagnostics(params.text_document.uri, diagnostics, None)
			.await;

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
		let Some(source_file) = self.get_source_file_data(source_file_path) else {
			return Ok(None);
		};
		let pos = params.text_document_position_params.position;
		let pos = LspPosition {
			zero_based_line_number: pos.line,
			index_in_bytes_in_line: pos.character,
		};
		fn statement_search(
			statements: &[HighStatement],
			pos: LspPosition,
		) -> Option<&HighStatement> {
			for statement in statements.iter() {
				if statement.span().contains_lsp_position(pos) {
					if let HighStatement::Block { statements, curly_open, curly_close } = statement {
						if curly_open.is_lsp_position(pos) || curly_close.is_lsp_position(pos) {
							return Some(statement);
						} else {
							return statement_search(statements, pos);
						}
					} else {
						return Some(statement);
					}
				}
			}
			None
		}
		let Some(statement) = statement_search(&source_file.high_program.statements, pos) else {
			return Ok(None);
		};
		enum TokenThingy<'a> {
			Semicolon(&'a Pos),
			CurlyOpen(&'a Pos),
			CurlyClose(&'a Pos),
			Instruction(&'a HighInstruction),
		}
		let token_thingy = 'token_thingy: {
			match statement {
				HighStatement::Code { instructions, semicolon } => {
					for instruction in instructions.iter() {
						if instruction.span().contains_lsp_position(pos) {
							break 'token_thingy Some(TokenThingy::Instruction(instruction));
						}
					}
					if let Some(semicolon) = semicolon {
						if semicolon.is_lsp_position(pos) {
							break 'token_thingy Some(TokenThingy::Semicolon(semicolon));
						}
					}
				},
				HighStatement::Block { curly_open, curly_close, .. } => {
					if curly_open.is_lsp_position(pos) {
						break 'token_thingy Some(TokenThingy::CurlyOpen(curly_open));
					}
					if curly_close.is_lsp_position(pos) {
						break 'token_thingy Some(TokenThingy::CurlyClose(curly_close));
					}
				},
				HighStatement::Empty { semicolon } => {
					if semicolon.is_lsp_position(pos) {
						break 'token_thingy Some(TokenThingy::Semicolon(semicolon));
					}
				},
				HighStatement::Error { .. } => {
					break 'token_thingy None;
				},
			}
			None
		};
		let statement_span = statement.span();
		let statement_one_based_line_range = statement.span().one_based_line_range();
		let (span, documentation) = match token_thingy {
			None => return Ok(None),
			Some(TokenThingy::Semicolon(_))
			| Some(TokenThingy::CurlyOpen(_))
			| Some(TokenThingy::CurlyClose(_)) => {
				let documentation = format!(
					"{}\n\n{}",
					match statement {
						HighStatement::Empty { .. } => "Empty statement".to_string(),
						HighStatement::Code { ref instructions, .. } =>
							format!("Code statement of {} insructions", instructions.len()),
						HighStatement::Block { ref statements, .. } =>
							format!("Block statement of {} statements", statements.len()),
						HighStatement::Error { .. } => "Error".to_string(),
					},
					if statement_one_based_line_range.0 == statement_one_based_line_range.1 {
						format!("On line {}", statement_one_based_line_range.0)
					} else {
						format!(
							"On lines {}-{}",
							statement_one_based_line_range.0, statement_one_based_line_range.1
						)
					}
				);
				(statement_span, documentation)
			},
			Some(TokenThingy::Instruction(instruction)) => {
				let documentation = match instruction {
					HighInstruction::IntegerLiteral(integer_literal) => {
						format!("Integer literal, of value {}", integer_literal.value)
					},
					HighInstruction::CharacterLiteral(character_literal) => {
						format!(
							"Character literal, of unicode code point U+{c:04X} ({c})",
							c = character_literal.value as u32
						)
					},
					HighInstruction::StringLiteral(_) => "String literal".to_string(),
					HighInstruction::ExplicitKeyword(_) => "Explicit keyword".to_string(),
					HighInstruction::Identifier(_) => "Identifier".to_string(),
				};
				(instruction.span().clone(), documentation)
			},
		};
		let range = span.to_lsp_range();
		let bit_of_code = span.as_str();
		Ok(Some(Hover {
			contents: HoverContents::Markup(MarkupContent {
				kind: MarkupKind::Markdown,
				value: format!("```spine\n{bit_of_code}\n```\n---\n{documentation}"),
			}),
			range: Some(lsp_range_into_range(range)),
		}))
	}

	async fn diagnostic(
		&self,
		params: DocumentDiagnosticParams,
	) -> Result<DocumentDiagnosticReportResult> {
		let source_file_path = params.text_document.uri.to_file_path().unwrap();
		let diagnostics = self.get_diagnostics(source_file_path);

		Ok(DocumentDiagnosticReportResult::Report(
			DocumentDiagnosticReport::Full(RelatedFullDocumentDiagnosticReport {
				related_documents: None,
				full_document_diagnostic_report: FullDocumentDiagnosticReport {
					result_id: None,
					items: diagnostics,
				},
			}),
		))
	}

	async fn code_action(&self, params: CodeActionParams) -> Result<Option<CodeActionResponse>> {
		let source_file_path = params.text_document.uri.to_file_path().unwrap();
		let source_file = self.get_source_file_data(source_file_path);

		let mut actions = vec![];
		let (errors, warnings) = source_file.unwrap().high_program.get_errors_and_warnings();
		for warning in warnings {
			if let Some(fix_by_rewrite) = warning.fix_by_rewrite_proposal() {
				actions.push(CodeActionOrCommand::CodeAction(CodeAction {
					title: fix_by_rewrite.description,
					kind: Some(CodeActionKind::QUICKFIX),
					diagnostics: Some(vec![get_diagnostic_from_warning(&warning)]),
					edit: Some(WorkspaceEdit {
						changes: Some({
							let mut map = HashMap::new();
							map.insert(
								params.text_document.uri.clone(),
								vec![TextEdit {
									range: lsp_range_into_range(warning.span().to_lsp_range()),
									new_text: fix_by_rewrite.new_code,
								}],
							);
							map
						}),
						document_changes: None,
						change_annotations: None,
					}),
					command: None,
					is_preferred: Some(true),
					disabled: None,
					data: None,
				}));
			}
		}

		Ok(Some(actions))
	}
}

pub fn run_lsp() {
	let async_runtime = tokio::runtime::Builder::new_current_thread()
		.thread_name("Tokio Runtime Thread")
		.enable_io()
		.build()
		.unwrap();

	async_runtime.block_on(async {
		let (stdin, stdout) = (tokio::io::stdin(), tokio::io::stdout());
		let (service, socket) = LspService::new(|client| SpineLanguageServer {
			client,
			source_files: Mutex::new(HashMap::new()),
		});
		Server::new(stdin, stdout, socket).serve(service).await;
	});
}
