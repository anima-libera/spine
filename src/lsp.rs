use serde_json::Value;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

#[derive(Debug)]
struct Backend {
	client: Client,
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
	async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
		Ok(InitializeResult {
			server_info: None,
			capabilities: ServerCapabilities {
				position_encoding: Some(PositionEncodingKind::UTF8),
				hover_provider: Some(HoverProviderCapability::Simple(true)),
				..ServerCapabilities::default()
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

	async fn did_open(&self, _: DidOpenTextDocumentParams) {
		self.client.log_message(MessageType::INFO, "did open").await;
	}

	async fn did_change(&self, _: DidChangeTextDocumentParams) {
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
		Ok(Some(CompletionResponse::Array(vec![CompletionItem {
			label: "`exit".to_string(),
			detail: Some("Terminate execution".to_string()),
			label_details: Some(CompletionItemLabelDetails {
				detail: Some("Terminate execution".to_string()),
				description: None,
			}),
			kind: Some(CompletionItemKind::KEYWORD),
			documentation: Some(Documentation::MarkupContent(MarkupContent {
				kind: MarkupKind::Markdown,
				value: "Calls the `exit` syscall, which terminates the process execution.".to_string(),
			})),
			..CompletionItem::default()
		}])))
	}

	async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
		let pos = params.text_document_position_params.position;
		Ok(Some(Hover {
			contents: HoverContents::Array(vec![
				MarkedString::LanguageString(LanguageString {
					language: "spine".to_string(),
					value: "\"jaaj\\xdd\"".to_string(),
				}),
				MarkedString::String("a".to_string()),
			]),
			range: Some(Range {
				start: pos,
				end: Position { line: pos.line, character: pos.character + 1 },
			}),
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
		let (service, socket) = LspService::new(|client| Backend { client });
		Server::new(stdin, stdout, socket).serve(service).await;
	});
}
