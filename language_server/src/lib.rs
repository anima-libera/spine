#![allow(unused)] // For now, WIP stuff gets too yellow for my taste

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use spine_compiler::err::{CompilationError, CompilationWarning};
use spine_compiler::lang::{Comment, list_comments};
use spine_compiler::src::{LineNumber, LspPositionUtf16, LspRangeUtf16};
use tower_lsp_server::jsonrpc::Result;
use tower_lsp_server::ls_types::*;
use tower_lsp_server::{Client, LanguageServer, LspService, Server};

use spine_compiler::{
	lang::{HighInstruction, HighProgram, HighStatement, parse},
	src::{LspPosition, LspRange, Pos, SourceCode},
};

struct SourceFileData {
	source: Arc<SourceCode>,
	high_program: HighProgram,
	comments: Vec<Comment>,
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
			let comments = list_comments(Arc::clone(&source));
			let source_file = Arc::new(SourceFileData { source, high_program, comments });
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
	let range = lsp_range_utf16_into_range(error.span().to_lsp_range_utf16());
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
	let range = lsp_range_utf16_into_range(warning.span().to_lsp_range_utf16());
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

fn lsp_range_utf16_into_range(lsp_range_utf16: LspRangeUtf16) -> Range {
	Range {
		start: Position {
			line: lsp_range_utf16.start.zero_based_line_number,
			character: lsp_range_utf16.start.index_in_utf16_code_units_in_line,
		},
		end: Position {
			line: lsp_range_utf16.end.zero_based_line_number,
			character: lsp_range_utf16.end.index_in_utf16_code_units_in_line,
		},
	}
}

#[derive(Clone, Copy)]
enum TokenType {
	Comment = 0,
}

impl LanguageServer for SpineLanguageServer {
	async fn initialize(&self, params: InitializeParams) -> Result<InitializeResult> {
		Ok(InitializeResult {
			server_info: Some(ServerInfo { name: "Spine language server".to_string(), version: None }),
			capabilities: ServerCapabilities {
				text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
				position_encoding: Some(PositionEncodingKind::UTF16),
				hover_provider: Some(HoverProviderCapability::Simple(true)),
				completion_provider: Some(CompletionOptions {
					resolve_provider: None,
					trigger_characters: None,
					all_commit_characters: None,
					work_done_progress_options: WorkDoneProgressOptions { work_done_progress: None },
					completion_item: Some(CompletionOptionsCompletionItem {
						label_details_support: None,
					}),
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
				semantic_tokens_provider: Some(
					SemanticTokensServerCapabilities::SemanticTokensOptions(SemanticTokensOptions {
						work_done_progress_options: WorkDoneProgressOptions { work_done_progress: None },
						legend: SemanticTokensLegend {
							token_types: vec![SemanticTokenType::new("comment")],
							token_modifiers: vec![],
						},
						range: None,
						full: Some(SemanticTokensFullOptions::Bool(true)),
					}),
				),
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
		let comments = list_comments(Arc::clone(&source));
		let source_file = Arc::new(SourceFileData { source, high_program, comments });
		self
			.source_files
			.lock()
			.unwrap()
			.insert(source_file_path.to_path_buf(), source_file);

		let diagnostics = self.get_diagnostics(source_file_path.to_path_buf());
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
		let comments = list_comments(Arc::clone(&source));
		let source_file = Arc::new(SourceFileData { source, high_program, comments });
		self
			.source_files
			.lock()
			.unwrap()
			.insert(source_file_path.to_path_buf(), source_file);

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
		let source_file_path = params
			.text_document_position
			.text_document
			.uri
			.to_file_path()
			.unwrap();
		let Some(source_file) = self.get_source_file_data(source_file_path.to_path_buf()) else {
			return Ok(None);
		};
		let pos = params.text_document_position.position;
		let pos = LspPositionUtf16 {
			zero_based_line_number: pos.line,
			index_in_utf16_code_units_in_line: pos.character,
		};
		let Some(line_span) = source_file
			.source
			.line_content_span(LineNumber::from_zero_based(
				pos.zero_based_line_number as usize,
			))
		else {
			return Ok(None);
		};
		let pos = LspPositionUtf16::to_lsp_position(pos, line_span.as_str());
		let before_cusrsor = &line_span.as_str()[..(pos.index_in_bytes_in_line as usize)];
		let word_before_cursor = if before_cusrsor.ends_with(|c: char| c.is_ascii_alphanumeric()) {
			let mut word = String::new();
			let mut before = before_cusrsor;
			while before.ends_with(|c: char| c.is_ascii_alphanumeric()) {
				let index_last = before.floor_char_boundary(before.len() - 1);
				let character = before[index_last..].chars().next().unwrap();
				word.insert(0, character);
				before = &before[..index_last];
			}
			Some(word)
		} else {
			None
		};

		if let Some(word) = word_before_cursor
			&& (word == "k" || word.starts_with("kw"))
		{
			Ok(Some(CompletionResponse::Array(vec![
				CompletionItem {
					label: "kwexit".to_string(),
					label_details: Some(CompletionItemLabelDetails {
						detail: Some(" ( --> )".to_string()),
						description: Some("terminate execution".to_string()),
					}),
					insert_text: None,
					detail: None,
					kind: Some(CompletionItemKind::KEYWORD),
					documentation: Some(Documentation::MarkupContent(MarkupContent {
						kind: MarkupKind::Markdown,
						value: "```spine\n\
							kwexit\n\
							```\n\
							*Explicit keyword*\n\n\
							Calls the `exit` syscall, which terminates the process execution."
							.to_string(),
					})),
					..CompletionItem::default()
				},
				CompletionItem {
					label: "kwpc".to_string(),
					label_details: Some(CompletionItemLabelDetails {
						detail: Some(" (char --> )".to_string()),
						description: Some("print character".to_string()),
					}),
					insert_text: None,
					detail: None,
					kind: Some(CompletionItemKind::KEYWORD),
					documentation: Some(Documentation::MarkupContent(MarkupContent {
						kind: MarkupKind::Markdown,
						value: "```spine\n\
							kwpc\n\
							```\n\
							*Explicit keyword*\n\n\
							Calls the `write` syscall with a string made of the provided character."
							.to_string(),
					})),
					..CompletionItem::default()
				},
				CompletionItem {
					label: "kwps".to_string(),
					label_details: Some(CompletionItemLabelDetails {
						detail: Some(" (ptr len --> )".to_string()),
						description: Some("print string".to_string()),
					}),
					insert_text: None,
					detail: None,
					kind: Some(CompletionItemKind::KEYWORD),
					documentation: Some(Documentation::MarkupContent(MarkupContent {
						kind: MarkupKind::Markdown,
						value: "```spine\n\
							kwps\n\
							```\n\
							*Explicit keyword*\n\n\
							Calls the `write` syscall with the given pointer and length."
							.to_string(),
					})),
					..CompletionItem::default()
				},
				CompletionItem {
					label: "kwadd".to_string(),
					label_details: Some(CompletionItemLabelDetails {
						detail: Some(" (a b --> sum)".to_string()),
						description: Some("add two numbers".to_string()),
					}),
					insert_text: None,
					detail: None,
					kind: Some(CompletionItemKind::KEYWORD),
					documentation: Some(Documentation::MarkupContent(MarkupContent {
						kind: MarkupKind::Markdown,
						value: "```spine\n\
							kwadd\n\
							```\n\
							*Explicit keyword*\n\n\
							Pops two numbers then pushes the result of their addition."
							.to_string(),
					})),
					..CompletionItem::default()
				},
				CompletionItem {
					label: "kwsys".to_string(),
					label_details: Some(CompletionItemLabelDetails {
						detail: Some(" (s a1 a2 a3 a4 a5 a6 --> ret1 ret2)".to_string()),
						description: Some("syscall".to_string()),
					}),
					insert_text: None,
					detail: None,
					kind: Some(CompletionItemKind::KEYWORD),
					documentation: Some(Documentation::MarkupContent(MarkupContent {
						kind: MarkupKind::Markdown,
						value: "```spine\n\
							kwsys\n\
							```\n\
							*Explicit keyword*\n\n\
							Pops 6 syscall arguments (last argument is popped first, etc), \
							then pops a syscall number, then runs the syscall, \
							then pushes the result 2, then the result.\n\n\
							Result 2 is meaningless and should always be discarded, \
							expect in the very specific case of the pipe syscall (syscall number 22) \
							on some specific architectures where it happens to return two numbers."
							.to_string(),
					})),
					..CompletionItem::default()
				},
				CompletionItem {
					label: "kwcpi".to_string(),
					label_details: Some(CompletionItemLabelDetails {
						detail: Some(" (pointer --> number)".to_string()),
						description: Some("cast pointer to number".to_string()),
					}),
					insert_text: None,
					detail: None,
					kind: Some(CompletionItemKind::KEYWORD),
					documentation: Some(Documentation::MarkupContent(MarkupContent {
						kind: MarkupKind::Markdown,
						value: "```spine\n\
							kwcpi\n\
							```\n\
							*Explicit keyword*\n\n\
							Just casts the type of the top value from address to number. \
							Compile-time only, codegens down to nothing."
							.to_string(),
					})),
					..CompletionItem::default()
				},
				CompletionItem {
					label: "kwdi".to_string(),
					label_details: Some(CompletionItemLabelDetails {
						detail: Some(" (number --> )".to_string()),
						description: Some("discard a number".to_string()),
					}),
					insert_text: None,
					detail: None,
					kind: Some(CompletionItemKind::KEYWORD),
					documentation: Some(Documentation::MarkupContent(MarkupContent {
						kind: MarkupKind::Markdown,
						value: "```spine\n\
							kwdi\n\
							```\n\
							*Explicit keyword*\n\n\
							Pops a number and discards it."
							.to_string(),
					})),
					..CompletionItem::default()
				},
				CompletionItem {
					label: "kwill".to_string(),
					label_details: Some(CompletionItemLabelDetails {
						detail: Some(" ( --> )".to_string()),
						description: Some("illegal".to_string()),
					}),
					insert_text: None,
					detail: None,
					kind: Some(CompletionItemKind::KEYWORD),
					documentation: Some(Documentation::MarkupContent(MarkupContent {
						kind: MarkupKind::Markdown,
						value: "```spine\n\
							kwill\n\
							```\n\
							*Explicit keyword*\n\n\
							Executes the `UD2` illegal instruction, an explosion follows."
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
		let Some(source_file) = self.get_source_file_data(source_file_path.to_path_buf()) else {
			return Ok(None);
		};
		let pos = params.text_document_position_params.position;
		let pos = LspPositionUtf16 {
			zero_based_line_number: pos.line,
			index_in_utf16_code_units_in_line: pos.character,
		};
		let Some(line_span) = source_file
			.source
			.line_content_span(LineNumber::from_zero_based(
				pos.zero_based_line_number as usize,
			))
		else {
			return Ok(None);
		};
		let pos = LspPositionUtf16::to_lsp_position(pos, line_span.as_str());
		fn statement_search(
			statements: &[HighStatement],
			pos: LspPosition,
		) -> Option<&HighStatement> {
			for statement in statements.iter() {
				if statement.span().contains_lsp_position(pos) {
					if let HighStatement::Block { statements, curly_open, curly_close } = statement {
						if curly_open.is_lsp_position(pos)
							|| curly_close
								.as_ref()
								.is_some_and(|curly_close| curly_close.is_lsp_position(pos))
						{
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
					if let Some(semicolon) = semicolon
						&& semicolon.is_lsp_position(pos)
					{
						break 'token_thingy Some(TokenThingy::Semicolon(semicolon));
					}
				},
				HighStatement::Block { curly_open, curly_close, .. } => {
					if curly_open.is_lsp_position(pos) {
						break 'token_thingy Some(TokenThingy::CurlyOpen(curly_open));
					}
					if let Some(curly_close) = curly_close
						&& curly_close.is_lsp_position(pos)
					{
						break 'token_thingy Some(TokenThingy::CurlyClose(curly_close));
					}
				},
				HighStatement::Empty { semicolon } => {
					if semicolon.is_lsp_position(pos) {
						break 'token_thingy Some(TokenThingy::Semicolon(semicolon));
					}
				},
				HighStatement::SomeUnexpectedCharacters { .. } => {
					break 'token_thingy None;
				},
				HighStatement::UnexpectedClosingCurly { .. } => {
					break 'token_thingy None;
				},
			}
			None
		};
		let statement_span = statement.span();
		let statement_line_range = statement.span().line_range();
		let (span, documentation) = match token_thingy {
			None => return Ok(None),
			Some(TokenThingy::Semicolon(_))
			| Some(TokenThingy::CurlyOpen(_))
			| Some(TokenThingy::CurlyClose(_)) => {
				let documentation = format!(
					"{}\n\n{}",
					match statement {
						HighStatement::Empty { .. } => "Empty statement".to_string(),
						HighStatement::Code { instructions, .. } =>
							format!("Code statement of {} insructions", instructions.len()),
						HighStatement::Block { statements, .. } =>
							format!("Block statement of {} statements", statements.len()),
						HighStatement::SomeUnexpectedCharacters { .. } => "Error".to_string(),
						HighStatement::UnexpectedClosingCurly { .. } => "Error".to_string(),
					},
					if statement_line_range.0 == statement_line_range.1 {
						format!("On line {}", statement_line_range.0.one_based())
					} else {
						format!(
							"On lines {}-{}",
							statement_line_range.0.one_based(),
							statement_line_range.1.one_based()
						)
					}
				);
				(statement_span, documentation)
			},
			Some(TokenThingy::Instruction(instruction)) => {
				let documentation = match instruction {
					HighInstruction::IntegerLiteral(integer_literal) => {
						if let Some(Ok(value)) = integer_literal.value {
							format!("Integer literal, of value {value}")
						} else {
							return Ok(None);
						}
					},
					HighInstruction::CharacterLiteral(character_literal) => {
						if let Ok(value) = character_literal.value {
							format!(
								"Character literal, of unicode code point U+{c:04X} ({c})",
								c = value as u32
							)
						} else {
							return Ok(None);
						}
					},
					HighInstruction::StringLiteral(_) => "String literal".to_string(),
					HighInstruction::ExplicitKeyword(_) => "Explicit keyword".to_string(),
					HighInstruction::Identifier(_) => "Identifier".to_string(),
				};
				(instruction.span().clone(), documentation)
			},
		};
		let range_utf16 = span.to_lsp_range_utf16();
		let bit_of_code = span.as_str();
		Ok(Some(Hover {
			contents: HoverContents::Markup(MarkupContent {
				kind: MarkupKind::Markdown,
				value: format!("```spine\n{bit_of_code}\n```\n---\n{documentation}"),
			}),
			range: Some(lsp_range_utf16_into_range(range_utf16)),
		}))
	}

	async fn semantic_tokens_full(
		&self,
		params: SemanticTokensParams,
	) -> Result<Option<SemanticTokensResult>> {
		let source_file_path = params.text_document.uri.to_file_path().unwrap();
		let source_file = self
			.get_source_file_data(source_file_path.to_path_buf())
			.unwrap();
		let mut semantic_tokens = vec![];

		// LSP wants relative positions (both for lines and offsets in lines)
		// so we keep the absolute position of the last token to turn new absolute positions
		// into relative positions.
		let mut last_token_line = None;
		let mut last_token_index_utf16 = None;

		for comment in &source_file.comments {
			let range_utf16 = comment.span.to_lsp_range_utf16();

			// LSP spec says that multi-line tokens are an optional client capability,
			// so the client might not support them (or support might be dropped one day).
			// Just to be safe, we cut multi-line tokens into non-multi-line tokens.
			let (line_start, line_end) = comment.span.line_range();
			for zero_based_line_number in line_start.zero_based()..=line_end.zero_based() {
				let line = LineNumber::from_zero_based(zero_based_line_number);

				let delta_line = last_token_line
					.map_or(line.zero_based(), |last_line: LineNumber| line - last_line)
					as u32;

				let start_in_current_line = if line == line_start {
					range_utf16.start.index_in_utf16_code_units_in_line
				} else {
					// We are NOT at the first line of the current multi-line token,
					// so this piece of token starts at the beginning of the current line.
					0
				};
				let delta_start = if last_token_line == Some(line) {
					start_in_current_line - last_token_index_utf16.unwrap()
				} else {
					start_in_current_line
				};

				let length = if line == line_end {
					range_utf16.end.index_in_utf16_code_units_in_line - start_in_current_line
				} else {
					let line_length_utf16 = source_file
						.source
						.line_content_span(line)
						.unwrap()
						.as_str()
						.encode_utf16()
						.count() as u32;
					line_length_utf16 - start_in_current_line
				};
				semantic_tokens.push(SemanticToken {
					delta_line,
					delta_start,
					length,
					token_type: TokenType::Comment as u32,
					token_modifiers_bitset: 0,
				});
				last_token_line = Some(line);
				last_token_index_utf16 = Some(start_in_current_line);
			}
		}

		Ok(Some(SemanticTokensResult::Tokens(SemanticTokens {
			result_id: None,
			data: semantic_tokens,
		})))
	}

	async fn diagnostic(
		&self,
		params: DocumentDiagnosticParams,
	) -> Result<DocumentDiagnosticReportResult> {
		let source_file_path = params.text_document.uri.to_file_path().unwrap();
		let diagnostics = self.get_diagnostics(source_file_path.to_path_buf());

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
		let source_file = self.get_source_file_data(source_file_path.to_path_buf());

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
									range: lsp_range_utf16_into_range(warning.span().to_lsp_range_utf16()),
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
