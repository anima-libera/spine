use core::str;
use std::collections::VecDeque;
use std::fmt::Debug;
use std::sync::Arc;

use crate::asm::{AsmInstr, Reg64};
use crate::elf::Binary;
use crate::imm::{Imm, Imm64};

/// Used as `Arc<Self>`.
#[derive(Debug)]
pub(crate) struct SourceCode {
	pub(crate) text: String,
	pub(crate) name: String,
	pub(crate) line_starts: LineStartTable,
}

#[derive(Debug)]
pub(crate) struct LineStartTable {
	/// Line of zero-based number N starts at `table[N]` chars/bytes in the source code.
	pub(crate) table: Vec<LineStart>,
}

#[derive(Debug)]
pub(crate) struct LineStart {
	/// Index in bytes of the UTF-8 encoded version of the source code.
	pub(crate) index_in_bytes: usize,
	/// Zero-based.
	pub(crate) index_in_chars: usize,
}

impl LineStartTable {
	pub(crate) fn compute_for_text(text: &str) -> LineStartTable {
		let mut index_in_bytes = 0;
		let mut index_in_chars = 0;
		let mut table = vec![LineStart { index_in_bytes, index_in_chars }];
		#[allow(clippy::explicit_counter_loop)]
		for character in text.chars() {
			index_in_bytes += character.len_utf8();
			index_in_chars += 1;
			if character == '\n' {
				table.push(LineStart { index_in_bytes, index_in_chars });
			}
		}
		LineStartTable { table }
	}
}

struct SourceCodeReader {
	source: Arc<SourceCode>,
	next_char_pos: Option<CharacterPos>,
	previous_char_pos: Option<CharacterPos>,
}

impl SourceCodeReader {
	fn new(source: Arc<SourceCode>) -> SourceCodeReader {
		let next_char_pos = if source.text.is_empty() {
			None
		} else {
			Some(CharacterPos { index_in_bytes: 0, index_in_chars: 0, line_number: 0 })
		};
		SourceCodeReader { source, next_char_pos, previous_char_pos: None }
	}

	fn previous_character_pos(&self) -> Option<CharacterPos> {
		self.previous_char_pos
	}

	fn next_character_pos(&self) -> Option<CharacterPos> {
		self.next_char_pos
	}

	fn passed_span(&self, pos_start: CharacterPos, pos_end: CharacterPos) -> SourceCodeSpan {
		if pos_end.index_in_chars < pos_start.index_in_chars {
			panic!("Span cannot end before it starts");
		}
		if self.previous_char_pos.unwrap().index_in_chars < pos_end.index_in_chars {
			panic!("Span cannot end after last popped/skipped character");
		}
		SourceCodeSpan { source: Arc::clone(&self.source), pos_start, pos_end }
	}

	fn peek_character(&self) -> Option<char> {
		self.source.text[self.next_char_pos?.index_in_bytes..]
			.chars()
			.next()
	}

	fn pop_character(&mut self) -> Option<char> {
		let next_next_char_pos = self.next_char_pos?.next_char_pos(&self.source);
		let character = self.peek_character().unwrap();
		self.previous_char_pos = self.next_char_pos;
		self.next_char_pos = next_next_char_pos;
		Some(character)
	}

	fn skip_character(&mut self) {
		self.pop_character();
	}

	fn skip_characters_while(&mut self, predicate: impl Fn(char) -> bool) {
		while self.peek_character().is_some_and(&predicate) {
			self.skip_character();
		}
	}

	fn skip_whitespace(&mut self) {
		self.skip_characters_while(|c| c.is_whitespace());
	}
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct CharacterPos {
	/// Index in bytes of the UTF-8 encoded version of the source code.
	pub(crate) index_in_bytes: usize,
	/// Zero-based.
	pub(crate) index_in_chars: usize,
	/// Zero-based.
	pub(crate) line_number: usize,
}

impl CharacterPos {
	fn next_char_pos(&self, source: &SourceCode) -> Option<CharacterPos> {
		let character = source.text[self.index_in_bytes..].chars().next().unwrap();
		let next_character_exists = source.text[self.index_in_bytes..].chars().nth(1).is_some();
		next_character_exists.then(|| CharacterPos {
			index_in_bytes: self.index_in_bytes + character.len_utf8(),
			index_in_chars: self.index_in_chars + 1,
			line_number: self.line_number + if character == '\n' { 1 } else { 0 },
		})
	}

	fn min(&self, other: &CharacterPos) -> CharacterPos {
		CharacterPos {
			index_in_bytes: self.index_in_bytes.min(other.index_in_bytes),
			index_in_chars: self.index_in_chars.min(other.index_in_chars),
			line_number: self.line_number.min(other.line_number),
		}
	}

	fn max(&self, other: &CharacterPos) -> CharacterPos {
		CharacterPos {
			index_in_bytes: self.index_in_bytes.max(other.index_in_bytes),
			index_in_chars: self.index_in_chars.max(other.index_in_chars),
			line_number: self.line_number.max(other.line_number),
		}
	}

	fn to_lsp_position(self, source: &SourceCode) -> LspPosition {
		let line_number = self.line_number;
		let line_start_in_bytes = source.line_starts.table[self.line_number].index_in_bytes;
		let index_in_bytes_in_line = (self.index_in_bytes - line_start_in_bytes) as u32;
		LspPosition { line_number: self.line_number as u32, index_in_bytes_in_line }
	}
}

#[derive(Clone)]
pub(crate) struct SourceCodeSpan {
	source: Arc<SourceCode>,
	/// Included.
	pos_start: CharacterPos,
	/// Included.
	pos_end: CharacterPos,
}

impl Debug for SourceCodeSpan {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(
			f,
			"{}l{}:{}l{}",
			self.pos_start.index_in_chars,
			self.pos_start.line_number,
			self.pos_end.index_in_chars,
			self.pos_end.line_number
		)
	}
}

impl SourceCodeSpan {
	fn next_char_pos(&self) -> Option<CharacterPos> {
		self.pos_end.next_char_pos(&self.source)
	}

	fn combine(&self, other: SourceCodeSpan) -> SourceCodeSpan {
		assert!(Arc::ptr_eq(&self.source, &other.source));
		SourceCodeSpan {
			source: Arc::clone(&self.source),
			pos_start: self.pos_start.min(&other.pos_start),
			pos_end: self.pos_end.max(&other.pos_end),
		}
	}

	pub(crate) fn as_str(&self) -> &str {
		&self.source.text[self.pos_start.index_in_bytes..=self.pos_end.index_in_bytes]
	}

	pub(crate) fn line_range(&self) -> (usize, usize) {
		(self.pos_start.line_number, self.pos_end.line_number)
	}

	pub(crate) fn contains_lsp_position(&self, lsp_pos: LspPosition) -> bool {
		let line_start_in_bytes =
			self.source.line_starts.table[lsp_pos.line_number as usize].index_in_bytes as u32;
		let lsp_pos_index_in_bytes = line_start_in_bytes + lsp_pos.index_in_bytes_in_line;
		(self.pos_start.index_in_bytes..=self.pos_end.index_in_bytes)
			.contains(&(lsp_pos_index_in_bytes as usize))
	}

	pub(crate) fn to_lsp_positions(&self) -> LspRange {
		LspRange {
			start: self.pos_start.to_lsp_position(&self.source),
			end: self
				.pos_end
				.next_char_pos(&self.source)
				.unwrap()
				.to_lsp_position(&self.source),
		}
	}
}

pub(crate) struct LspPosition {
	/// Zero-based.
	pub(crate) line_number: u32,
	/// Zero-based, index in the bytes of the line.
	pub(crate) index_in_bytes_in_line: u32,
}

pub(crate) struct LspRange {
	/// Included.
	pub(crate) start: LspPosition,
	/// Excluded.
	pub(crate) end: LspPosition,
}

#[derive(Debug)]
pub(crate) struct IntegerLiteral {
	pub(crate) span: SourceCodeSpan,
	pub(crate) radix_prefix: Option<RadixPrefix>,
	pub(crate) value: i64,
}

#[derive(Debug)]
pub(crate) struct CharacterLiteral {
	pub(crate) span: SourceCodeSpan,
	pub(crate) character_escape: Option<CharacterEscape>,
	pub(crate) value: char,
}

#[derive(Debug)]
pub(crate) struct StringLiteral {
	pub(crate) span: SourceCodeSpan,
	pub(crate) character_escapes: Vec<CharacterEscape>,
	pub(crate) value: String,
}

#[derive(Debug)]
pub(crate) enum ExplicitKeywordWhich {
	/// Pops an i64 and prints the ASCII character it represents.
	PrintChar,
	/// Pops an i64 (string length) then pops a pointer (to the string content),
	/// then prints the UTF-8 encoded string.
	/// It works well with string literals (`printstr "uwu\n"` does what we expect).
	PrintStr,
	/// Pops two i64 values, add them together, and push the result.
	Add,
	/// Terminate the process execution by calling the exit syscall, with 0 as the exit code.
	Exit,
}

#[derive(Debug)]
pub(crate) struct ExplicitKeyword {
	pub(crate) span: SourceCodeSpan,
	pub(crate) keyword: Option<ExplicitKeywordWhich>,
}

#[derive(Debug)]
struct Comment {
	span: SourceCodeSpan,
	is_block: bool,
	is_doc: bool,
}

#[derive(Debug)]
struct WhitespaceAndComments {
	span: SourceCodeSpan,
	comments: Vec<Comment>,
}

#[derive(Debug)]
enum Token {
	IntegerLiteral(IntegerLiteral),
	CharacterLiteral(CharacterLiteral),
	StringLiteral(StringLiteral),
	ExplicitKeyword(ExplicitKeyword),
	Semicolon(SourceCodeSpan),
	WhitespaceAndComments(WhitespaceAndComments),
}

impl Token {
	fn span(&self) -> &SourceCodeSpan {
		match self {
			Token::IntegerLiteral(t) => &t.span,
			Token::CharacterLiteral(t) => &t.span,
			Token::StringLiteral(t) => &t.span,
			Token::ExplicitKeyword(t) => &t.span,
			Token::Semicolon(span) => span,
			Token::WhitespaceAndComments(t) => &t.span,
		}
	}
}

/// Consumes the source code representation of an escaped character,
/// assuming we are in a string or character literal, and that the next character is the `\`.
fn pop_escaped_character_from_reader(reader: &mut SourceCodeReader) -> CharacterEscape {
	let pos_first_character = reader.next_character_pos().unwrap();
	assert_eq!(reader.pop_character(), Some('\\'));
	let hex_digit_to_value = |hex_digit| match hex_digit {
		'0'..='9' => hex_digit as u32 - '0' as u32,
		'a'..='f' => hex_digit as u32 - 'a' as u32 + 10,
		'A'..='F' => hex_digit as u32 - 'A' as u32 + 10,
		_ => panic!(),
	};
	let produced_character = match reader.pop_character().unwrap() {
		'x' | 'X' => {
			// `\x1b`, unicode code point (in `0..=255`) with exactly two hex digits.
			let high = reader.pop_character().unwrap();
			let low = reader.pop_character().unwrap();
			let value = hex_digit_to_value(high) * 16 + hex_digit_to_value(low);
			char::from_u32(value).unwrap()
		},
		'u' | 'U' => {
			// `\u{fffd}`, unicode code point with hex digits.
			assert_eq!(reader.pop_character(), Some('{'));
			let mut value = 0;
			loop {
				let character = reader.pop_character().unwrap();
				if character == '}' {
					break;
				}
				value = value * 16 + hex_digit_to_value(character);
			}
			char::from_u32(value).unwrap()
		},
		'd' | 'D' => {
			// `\d{65533}`, unicode code point with decimal digits.
			assert_eq!(reader.pop_character(), Some('{'));
			let mut value = 0;
			loop {
				let character = reader.pop_character().unwrap();
				if character == '}' {
					break;
				}
				assert!(character.is_ascii_digit());
				value = value * 10 + hex_digit_to_value(character);
			}
			char::from_u32(value).unwrap()
		},
		'e' => '\x1b', // Escape
		'a' => '\x07', // Bell
		'b' => '\x08', // Backspace
		'n' => '\n',   // Newline
		't' => '\t',   // Tab
		'r' => '\r',   // Carriage return
		'v' => '\x0b', // Vertical tab
		'f' => '\x0c', // Page break
		'?' => '�',    // Replacement character
		'0' => '\0',   // Null
		'\\' => '\\',
		'\'' => '\'',
		'\"' => '\"',
		_ => panic!(),
	};
	let span = reader.passed_span(
		pos_first_character,
		reader.previous_character_pos().unwrap(),
	);
	let representation_in_source = span.as_str().to_string();
	CharacterEscape { span, produced_character, representation_in_source }
}

/// Consumes and tokenizes the next token.
fn pop_token_from_reader(reader: &mut SourceCodeReader) -> Option<Token> {
	let first_character = reader.peek_character();
	let pos_first_character = reader.next_character_pos();
	match first_character {
		Some('0'..='9') => {
			let radix_prefix = if reader.peek_character() == Some('0') {
				reader.skip_character();
				let maybe_radix_character = reader.peek_character();
				if maybe_radix_character.is_none_or(|c| !c.is_ascii_alphanumeric()) {
					// Not a radix prefix.
					None
				} else {
					reader.skip_character();
					let radix_character = maybe_radix_character.unwrap();
					match radix_character {
						'x' | 'X' => Some(RadixPrefix {
							span: reader.passed_span(
								pos_first_character.unwrap(),
								reader.previous_character_pos().unwrap(),
							),
							kind: RadixPrefixKind::Hexadecimal,
							uppercase: radix_character.is_uppercase(),
						}),
						'b' | 'B' => Some(RadixPrefix {
							span: reader.passed_span(
								pos_first_character.unwrap(),
								reader.previous_character_pos().unwrap(),
							),
							kind: RadixPrefixKind::Binary,
							uppercase: radix_character.is_uppercase(),
						}),
						'r' | 'R' => {
							assert_eq!(reader.pop_character(), Some('{'));
							let pos_radix_number_start = reader.next_character_pos().unwrap();
							reader.skip_characters_while(|c| c.is_ascii_digit());
							let pos_radix_number_end = reader.previous_character_pos().unwrap();
							assert_eq!(reader.pop_character(), Some('}'));
							let pos_last_character_radix_prefix = reader.previous_character_pos().unwrap();
							let pos_first_character_after_radix_prefix =
								reader.next_character_pos().unwrap();
							let radix_number_span =
								reader.passed_span(pos_radix_number_start, pos_radix_number_end);
							let radix_number = radix_number_span.as_str().parse().unwrap();
							Some(RadixPrefix {
								span: reader.passed_span(
									pos_first_character.unwrap(),
									pos_last_character_radix_prefix,
								),
								kind: RadixPrefixKind::Arbitrary(radix_number),
								uppercase: radix_character.is_uppercase(),
							})
						},
						unknown => panic!("unknown radix prefix char {unknown}"),
					}
				}
			} else {
				None
			};
			let radix_number = radix_prefix
				.as_ref()
				.map_or(10, |radix_prefix| radix_prefix.kind.radix());
			if 16 < radix_number {
				unimplemented!(); // yet
			}
			reader.skip_characters_while(|c| c.is_ascii_hexdigit());
			let span_without_radix_prefix = reader.passed_span(
				radix_prefix
					.as_ref()
					.map_or(pos_first_character, |radix_prefix| {
						radix_prefix.span.next_char_pos()
					})
					.unwrap(),
				reader.previous_character_pos().unwrap(),
			);
			let value = i64::from_str_radix(span_without_radix_prefix.as_str(), radix_number).unwrap();
			let span = reader.passed_span(
				pos_first_character.unwrap(),
				reader.previous_character_pos().unwrap(),
			);
			let token = Token::IntegerLiteral(IntegerLiteral { span, radix_prefix, value });
			Some(token)
		},
		Some('\'') => {
			reader.skip_character();
			let character_escape = (reader.peek_character() == Some('\\'))
				.then(|| pop_escaped_character_from_reader(reader));
			let character = if let Some(character_escape) = &character_escape {
				character_escape.produced_character
			} else {
				reader.pop_character().unwrap()
			};
			assert_eq!(reader.pop_character(), Some('\''));
			let span = reader.passed_span(
				pos_first_character.unwrap(),
				reader.previous_character_pos().unwrap(),
			);
			let token =
				Token::CharacterLiteral(CharacterLiteral { span, character_escape, value: character });
			Some(token)
		},
		Some('\"') => {
			reader.skip_character();
			let mut string = String::new();
			let mut character_escapes = vec![];
			loop {
				if reader.peek_character() == Some('\"') {
					reader.skip_character();
					break;
				} else if reader.peek_character() == Some('\\') {
					let character_escape = pop_escaped_character_from_reader(reader);
					string.push(character_escape.produced_character);
					character_escapes.push(character_escape);
				} else {
					string.push(reader.pop_character().unwrap());
				};
			}
			let span = reader.passed_span(
				pos_first_character.unwrap(),
				reader.previous_character_pos().unwrap(),
			);
			let token = Token::StringLiteral(StringLiteral { span, character_escapes, value: string });
			Some(token)
		},
		Some('`') => {
			reader.skip_character();
			reader.skip_characters_while(|c| c.is_ascii_alphanumeric());
			let span = reader.passed_span(
				pos_first_character.unwrap(),
				reader.previous_character_pos().unwrap(),
			);
			let keyword = match span.as_str() {
				"`printchar" => Some(ExplicitKeywordWhich::PrintChar),
				"`printstr" => Some(ExplicitKeywordWhich::PrintStr),
				"`add" => Some(ExplicitKeywordWhich::Add),
				"`exit" => Some(ExplicitKeywordWhich::Exit),
				_ => None,
			};
			let token = Token::ExplicitKeyword(ExplicitKeyword { span, keyword });
			Some(token)
		},
		Some(';') => {
			reader.skip_character();
			let span = reader.passed_span(pos_first_character.unwrap(), pos_first_character.unwrap());
			Some(Token::Semicolon(span))
		},
		Some('-' | ' ' | '\n' | '\r' | '\t') => {
			let mut comments = vec![];
			loop {
				reader.skip_whitespace();
				if reader.peek_character() != Some('-') {
					break;
				}
				reader.skip_character();
				assert_eq!(reader.pop_character(), Some('-'));
				let is_doc = reader.peek_character() == Some('-');
				if is_doc {
					reader.skip_character();
				}
				let is_block = reader.peek_character() == Some('{');
				if is_block {
					reader.skip_character();
					reader.skip_characters_while(|c| c != '}');
					reader.skip_character();
				} else {
					reader.skip_characters_while(|c| c != '\n');
					reader.skip_character();
				}
				let span = reader.passed_span(
					pos_first_character.unwrap(),
					reader.previous_character_pos().unwrap(),
				);
				let comment = Comment { span, is_block, is_doc };
				comments.push(comment);
			}
			let span = reader.passed_span(
				pos_first_character.unwrap(),
				reader.previous_character_pos().unwrap(),
			);
			let token = Token::WhitespaceAndComments(WhitespaceAndComments { span, comments });
			Some(token)
		},
		Some(unknown) => panic!("failed to tokenize char {unknown}"),
		None => None,
	}
}

fn pop_token_from_reader_ignoring_comments(reader: &mut SourceCodeReader) -> Option<Token> {
	loop {
		match pop_token_from_reader(reader) {
			Some(Token::WhitespaceAndComments(_)) => continue,
			not_a_comment => break not_a_comment,
		}
		unreachable!();
	}
}

struct Tokenizer {
	reader: SourceCodeReader,
	/// Peeking tokens queues them, so that they are not tokenized again when popped.
	queue: VecDeque<Token>,
}

impl Tokenizer {
	fn new(reader: SourceCodeReader) -> Tokenizer {
		Tokenizer { reader, queue: VecDeque::new() }
	}

	fn pop_token(&mut self) -> Option<Token> {
		if let Some(token) = self.queue.pop_front() {
			Some(token)
		} else {
			pop_token_from_reader_ignoring_comments(&mut self.reader)
		}
	}

	fn peek_ith_token(&mut self, index: usize) -> Option<&Token> {
		while self.queue.len() <= index {
			let token = pop_token_from_reader_ignoring_comments(&mut self.reader)?;
			self.queue.push_back(token);
		}
		Some(&self.queue[index])
	}

	fn peek_token(&mut self) -> Option<&Token> {
		self.peek_ith_token(0)
	}
}

#[derive(Debug)]
pub(crate) struct AstProgram {
	pub(crate) source: Arc<SourceCode>,
	pub(crate) statements: Vec<AstStatementAny>,
}

#[derive(Debug)]
pub(crate) struct AstStatementAny {
	// TODO: Add a field for doc in attached doc comment
	// (attached doc either starts on lines before, or is line comment on same line just after)
	pub(crate) span: SourceCodeSpan,
	pub(crate) terminating_semicolon: Option<SourceCodeSpan>,
	pub(crate) specific_statement: AstStatement,
}

#[derive(Debug)]
pub(crate) enum AstStatement {
	/// This statement contains code (computer programming computation waow)
	/// that actually does something when executed (so NOT a declarative statement).
	Code { instructions: Vec<AstInstruction> },
	/// A semicolon with nothing between it and the previous one or the start of file.
	/// It is valid syntax and does nothing.
	Empty,
}

#[derive(Debug)]
pub(crate) enum AstInstruction {
	IntegerLiteral(IntegerLiteral),
	CharacterLiteral(CharacterLiteral),
	StringLiteral(StringLiteral),
	ExplicitKeyword(ExplicitKeyword),
}

impl AstInstruction {
	fn span(&self) -> &SourceCodeSpan {
		match self {
			AstInstruction::IntegerLiteral(t) => &t.span,
			AstInstruction::CharacterLiteral(t) => &t.span,
			AstInstruction::StringLiteral(t) => &t.span,
			AstInstruction::ExplicitKeyword(t) => &t.span,
		}
	}
}

#[derive(Debug)]
pub(crate) struct RadixPrefix {
	pub(crate) span: SourceCodeSpan,
	pub(crate) kind: RadixPrefixKind,
	/// `0x` or `0X`
	pub(crate) uppercase: bool,
}

#[derive(Debug)]
pub(crate) enum RadixPrefixKind {
	Hexadecimal,    // 0x
	Binary,         // 0b
	Arbitrary(u32), // 0r{radix}
}

impl RadixPrefixKind {
	fn radix(&self) -> u32 {
		match self {
			RadixPrefixKind::Hexadecimal => 16,
			RadixPrefixKind::Binary => 2,
			RadixPrefixKind::Arbitrary(radix) => *radix,
		}
	}
}

#[derive(Debug)]
pub(crate) struct CharacterEscape {
	pub(crate) span: SourceCodeSpan,
	/// The character that ends up in the compiled program.
	/// This is the value that the escape sequence actually represents.
	pub(crate) produced_character: char,
	/// The escape sequence as written in the source code.
	pub(crate) representation_in_source: String,
}

pub(crate) fn parse_to_ast(source: Arc<SourceCode>) -> AstProgram {
	let reader = SourceCodeReader::new(Arc::clone(&source));
	let mut tokenizer = Tokenizer::new(reader);

	let mut statements = vec![];
	while tokenizer.peek_token().is_some() {
		let mut instructions = vec![];
		let semicolon_span = loop {
			match tokenizer.pop_token() {
				Some(Token::IntegerLiteral(integer_literal)) => {
					instructions.push(AstInstruction::IntegerLiteral(integer_literal));
				},
				Some(Token::CharacterLiteral(character_literal)) => {
					instructions.push(AstInstruction::CharacterLiteral(character_literal));
				},
				Some(Token::StringLiteral(string_literal)) => {
					instructions.push(AstInstruction::StringLiteral(string_literal))
				},
				Some(Token::ExplicitKeyword(explicit_keyword)) => {
					instructions.push(AstInstruction::ExplicitKeyword(explicit_keyword));
				},
				Some(Token::WhitespaceAndComments(_)) => {},
				Some(Token::Semicolon(span)) => break Some(span),
				None => break None,
			};
		};
		let span = match (instructions.first(), semicolon_span.clone()) {
			(Some(first_instruction), Some(semicolon_span)) => {
				first_instruction.span().combine(semicolon_span)
			},
			(Some(first_instruction), None) => first_instruction.span().clone(),
			(None, Some(semicolon_span)) => semicolon_span,
			(None, None) => unreachable!(),
		};
		let specific_statement = if instructions.is_empty() {
			AstStatement::Empty
		} else {
			AstStatement::Code { instructions }
		};
		let statement_any =
			AstStatementAny { span, terminating_semicolon: semicolon_span, specific_statement };
		statements.push(statement_any);
	}
	AstProgram { source: Arc::clone(&source), statements }
}

#[derive(Debug, PartialEq, Eq)]
enum SpineType {
	I64,
	DataAddr,
}

#[derive(Debug)]
enum SpineValue {
	I64(i64),
	DataAddr { offset_in_data_segment: u64 },
}

impl SpineValue {
	fn get_type(&self) -> SpineType {
		match self {
			SpineValue::I64(_) => SpineType::I64,
			SpineValue::DataAddr { .. } => SpineType::DataAddr,
		}
	}
}

#[derive(Debug)]
enum SpineInstr {
	PushConst(SpineValue),
	PushString(String),
	PopI64AndPrintAsChar,
	PopI64AndPtrAndPrintAsString,
	AddI64AndI64,
	Exit,
}

impl SpineInstr {
	/// Order:
	/// - If operand types are `[A, B]` then it means `B` will be popped before `A`.
	/// - If return types are `[A, B]` then it means `A` will be pushed before `B`.
	fn operand_and_return_types(&self) -> (Vec<SpineType>, Vec<SpineType>) {
		match self {
			SpineInstr::PushConst(value) => (vec![], vec![value.get_type()]),
			SpineInstr::PushString(_) => (vec![], vec![SpineType::DataAddr, SpineType::I64]),
			SpineInstr::PopI64AndPrintAsChar => (vec![SpineType::I64], vec![]),
			SpineInstr::PopI64AndPtrAndPrintAsString => {
				(vec![SpineType::DataAddr, SpineType::I64], vec![])
			},
			SpineInstr::AddI64AndI64 => (vec![SpineType::I64, SpineType::I64], vec![SpineType::I64]),
			SpineInstr::Exit => (vec![], vec![]),
		}
	}
}

#[derive(Debug)]
enum SpineStatement {
	Code {
		/// In the order that they are executed, so the reverse of the order in the source code.
		instrs: Vec<SpineInstr>,
	},
}

pub(crate) struct SpineProgram {
	statements: Vec<SpineStatement>,
}

pub(crate) fn parse(source: Arc<SourceCode>) -> SpineProgram {
	let reader = SourceCodeReader::new(source);
	let mut tokenizer = Tokenizer::new(reader);

	let mut statements = vec![];
	while tokenizer.peek_token().is_some() {
		let mut src_order_instrs = vec![];
		loop {
			match tokenizer.pop_token() {
				Some(Token::IntegerLiteral(IntegerLiteral { span, value, .. })) => {
					src_order_instrs.push(SpineInstr::PushConst(SpineValue::I64(value)));
				},
				Some(Token::CharacterLiteral(CharacterLiteral { span, value, .. })) => {
					src_order_instrs.push(SpineInstr::PushConst(SpineValue::I64(value as i64)));
				},
				Some(Token::StringLiteral(StringLiteral { span, value, .. })) => {
					src_order_instrs.push(SpineInstr::PushString(value));
				},
				Some(Token::ExplicitKeyword(ExplicitKeyword { span, keyword })) => {
					match keyword.unwrap() {
						ExplicitKeywordWhich::PrintChar => {
							src_order_instrs.push(SpineInstr::PopI64AndPrintAsChar);
						},
						ExplicitKeywordWhich::PrintStr => {
							src_order_instrs.push(SpineInstr::PopI64AndPtrAndPrintAsString);
						},
						ExplicitKeywordWhich::Add => {
							src_order_instrs.push(SpineInstr::AddI64AndI64);
						},
						ExplicitKeywordWhich::Exit => {
							src_order_instrs.push(SpineInstr::Exit);
						},
					}
				},
				Some(Token::WhitespaceAndComments(_)) => {},
				Some(Token::Semicolon(span)) => break,
				None => break,
			}
		}

		// Typecheking.
		let mut excpected_type_stack = vec![];
		for instr in src_order_instrs.iter() {
			let (mut operand_types, mut return_types) = instr.operand_and_return_types();
			while let Some(top_return_type) = return_types.pop() {
				if let Some(top_excpected_type) = excpected_type_stack.pop() {
					assert_eq!(top_excpected_type, top_return_type, "type mismatch");
				} else {
					panic!(
						"a value of type {:?} is pushed but there is no instruction to pop it",
						top_return_type
					);
				}
			}
			excpected_type_stack.append(&mut operand_types);
		}
		assert!(
			excpected_type_stack.is_empty(),
			"values of types {:?} are expected but there is no instruction to push them",
			excpected_type_stack,
		);

		let instrs = {
			src_order_instrs.reverse();
			src_order_instrs
		};
		statements.push(SpineStatement::Code { instrs });
	}

	SpineProgram { statements }
}

pub(crate) fn compile_to_binary(program: SpineProgram) -> Binary {
	let mut bin = Binary::new();

	use AsmInstr::*;

	for statement in program.statements.iter() {
		match statement {
			SpineStatement::Code { instrs } => {
				for instr in instrs.iter() {
					match instr {
						SpineInstr::PushConst(SpineValue::I64(value)) => {
							bin.asm_instrs.extend([
								MovImmToReg64 { imm_src: Imm::whatever_raw(*value), reg_dst: Reg64::Rax },
								PushReg64 { reg_src: Reg64::Rax },
							]);
						},
						SpineInstr::PushConst(SpineValue::DataAddr { .. }) => {
							unimplemented!()
						},
						SpineInstr::PushString(string) => {
							let offset_in_data_segment = bin.data_bytes.len() as u64;
							let string_len_in_bytes = string.len() as i64;
							bin.data_bytes.extend(string.as_bytes());
							bin.asm_instrs.extend([
								MovImmToReg64 {
									imm_src: Imm::Imm64(Imm64::DataAddr { offset_in_data_segment }),
									reg_dst: Reg64::Rax,
								},
								PushReg64 { reg_src: Reg64::Rax },
								MovImmToReg64 {
									imm_src: Imm::whatever_raw(string_len_in_bytes),
									reg_dst: Reg64::Rax,
								},
								PushReg64 { reg_src: Reg64::Rax },
							]);
						},
						SpineInstr::PopI64AndPrintAsChar => {
							bin.asm_instrs.extend([
								// Write(message) syscall
								MovImmToReg64 {
									imm_src: Imm::whatever_raw(1),
									reg_dst: Reg64::Rax, // Syscall number
								},
								MovImmToReg64 {
									imm_src: Imm::whatever_raw(1),
									reg_dst: Reg64::Rdi, // File descriptor
								},
								PushReg64 { reg_src: Reg64::Rsp },
								PopToReg64 { reg_dst: Reg64::Rsi }, // String address
								MovImmToReg64 {
									imm_src: Imm::whatever_raw(1),
									reg_dst: Reg64::Rdx, // String length
								},
								Syscall,
								// Pop
								PopToReg64 { reg_dst: Reg64::Rsi },
							]);
						},
						SpineInstr::PopI64AndPtrAndPrintAsString => {
							bin.asm_instrs.extend([
								// Write(message) syscall
								MovImmToReg64 {
									imm_src: Imm::whatever_raw(1),
									reg_dst: Reg64::Rax, // Syscall number
								},
								MovImmToReg64 {
									imm_src: Imm::whatever_raw(1),
									reg_dst: Reg64::Rdi, // File descriptor
								},
								PopToReg64 { reg_dst: Reg64::Rdx }, // String length
								PopToReg64 { reg_dst: Reg64::Rsi }, // String address
								Syscall,
								// Pop
								PopToReg64 { reg_dst: Reg64::Rsi },
							]);
						},
						SpineInstr::AddI64AndI64 => {
							bin.asm_instrs.extend([
								PopToReg64 { reg_dst: Reg64::Rax },
								PopToReg64 { reg_dst: Reg64::Rbx },
								AddReg64ToReg64 { reg_src: Reg64::Rbx, reg_dst: Reg64::Rax },
								PushReg64 { reg_src: Reg64::Rax },
							]);
						},
						SpineInstr::Exit => {
							bin.asm_instrs.extend([
								// Exit(0) syscall
								MovImmToReg64 {
									imm_src: Imm::whatever_raw(60),
									reg_dst: Reg64::Rax, // Syscall number
								},
								MovImmToReg64 {
									imm_src: Imm::whatever_raw(0),
									reg_dst: Reg64::Rdi, // Exit code, 0 means all good
								},
								Syscall,
							]);
						},
					}
				}
			},
		}
	}

	bin
}
