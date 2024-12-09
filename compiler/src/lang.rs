use core::str;
use std::collections::VecDeque;
use std::fmt::Debug;
use std::path::Path;
use std::sync::Arc;

use crate::asm::{AsmInstr, Reg64};
use crate::elf::Binary;
use crate::imm::{Imm, Imm64};

/// One pice of source code, for example one source file.
///
/// Used in [`Arc`]s so that many objects can access it.
/// For example [`SourceCodeSpan`]s have an `Arc` to the source code they are a slice of.
///
/// `Arc` instead of `Rc` because [`tower_lsp::LanguageServer`] requires `Send` and `Sync`
/// so the language server needs to be `Sync` and `Rc` is not.
#[derive(Debug)]
pub struct SourceCode {
	pub text: String,
	pub name: String,
	line_starts: LineStartTable,
}

impl SourceCode {
	pub fn from_file(path: impl AsRef<Path>) -> Option<SourceCode> {
		let text = std::fs::read_to_string(&path).ok()?;
		let name = path.as_ref().to_str().unwrap().to_string();
		let line_starts = LineStartTable::compute_for_text(&text);
		Some(SourceCode { text, name, line_starts })
	}

	/// Sometimes a pice of source code does not come from a file,
	/// for example the `--raw-source` CLI option allows to
	/// compile Spine source code given directly in the command line arguments.
	pub fn from_string(text: String, name: String) -> SourceCode {
		let line_starts = LineStartTable::compute_for_text(&text);
		SourceCode { text, name, line_starts }
	}

	/// The text that it at the given `pos` and after.
	fn text_at(&self, pos: PosSimple) -> &str {
		&self.text[pos.index_in_bytes..]
	}

	fn line_span(self: &Arc<Self>, zero_based_line_number: usize) -> Option<Span> {
		let line_start = self.line_starts.table.get(zero_based_line_number)?;
		let line_start = PosSimple {
			index_in_bytes: line_start.index_in_bytes,
			index_in_chars: line_start.index_in_chars,
			zero_based_line_number,
		};
		let next_line_start = self.line_starts.table.get(zero_based_line_number + 1);
		let line_end = if let Some(next_line_start) = next_line_start {
			let next_line_start = PosSimple {
				index_in_bytes: next_line_start.index_in_bytes,
				index_in_chars: next_line_start.index_in_chars,
				zero_based_line_number: zero_based_line_number + 1,
			};
			next_line_start.prev(self).unwrap()
		} else {
			PosSimple {
				index_in_bytes: self.text.len(),
				index_in_chars: self.line_starts.len_in_chars,
				zero_based_line_number,
			}
		};
		Some(Span { source: Arc::clone(self), start: line_start, end: line_end })
	}
}

/// This allows to situate a line in the source code given only the line number.
#[derive(Debug)]
pub struct LineStartTable {
	/// Line of zero-based number N starts at `table[N]` chars/bytes in the source code.
	pub(crate) table: Vec<LineStart>,
	/// The length (in characters, not in bytes) of the source code text.
	pub(crate) len_in_chars: usize,
}

/// See [`LineStartTable`].
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
		LineStartTable { table, len_in_chars: index_in_chars }
	}
}

/// Allows to read a [`SourceCode`] in ways that makes tokenization easier.
///
/// This is basically an iterator over the characters of the source code,
/// but instead of `next` it provides many methods to peek and pop characters
/// in different ways used by different pieces of the tokenizer.
///
/// This is sort of a reading head abstraction over the source code content.
/// - Popping advances the reading head.
/// - Peeking does not advance the reading head.
/// - Cloning allows to pop the clone without moving the original.
#[derive(Clone)]
struct Reader {
	source: Arc<SourceCode>,
	/// The position of the next character that will be popped.
	///
	/// It is `None` if we reached end-of-file.
	next: Option<PosSimple>,
	/// The position of the last character that was popped.
	///
	/// It is `None` if the next character is still the first character.
	prev: Option<PosSimple>,
}

impl Reader {
	fn new(source: Arc<SourceCode>) -> Reader {
		let next = Pos::first_character(Arc::clone(&source))
			.as_ref()
			.map(Pos::without_source);
		Reader { source, next, prev: None }
	}

	/// Position of the previously popped character.
	fn prev_pos(&self) -> Option<Pos> {
		self.prev.map(|p| p.with_source(Arc::clone(&self.source)))
	}

	/// Position of the next character to be popped.
	fn next_pos(&self) -> Option<Pos> {
		self.next.map(|p| p.with_source(Arc::clone(&self.source)))
	}

	/// Returns the `i`-th (zero-based) next character after the reading head position,
	/// without popping (so without advancing the head, this only looks ahead).
	///
	/// `peek_ith(0)` is the character that will be popped next.
	fn peek_ith(&self, index: usize) -> Option<char> {
		self.source.text_at(self.next?).chars().nth(index)
	}

	/// Returns the next character that will be popped, but without popping it,
	/// this only looks ahead.
	fn peek(&self) -> Option<char> {
		self.peek_ith(0)
	}

	/// Pops the next character.
	///
	/// Meaning, we read the next character (and return it) and advance the reading head
	/// so that the character we just read is behind us now.
	fn pop(&mut self) -> Option<char> {
		let next_next_char_pos = self.next?.next(&self.source);
		let character = self.peek().unwrap();
		self.prev = self.next;
		self.next = next_next_char_pos;
		Some(character)
	}

	/// Pops and discards.
	fn skip(&mut self) {
		self.pop();
	}

	/// Skips iff the next character verifies the given `predicate`.
	///
	/// Returns `true` iff we did skip a character.
	fn skip_if(&mut self, predicate: impl FnOnce(char) -> bool) -> bool {
		let Some(character) = self.peek() else {
			return false;
		};
		let verifies = predicate(character);
		if verifies {
			self.skip();
		}
		verifies
	}

	/// Skips iff the next character is the given `character_to_match`.
	///
	/// Returns `true` iff we did skip a character.
	fn skip_if_eq(&mut self, character_to_match: char) -> bool {
		self.skip_if(|c| c == character_to_match)
	}

	/// Skip all characters we encounter while they verify the given `predicate`
	/// until we encounter a character that does not verify it (or end-of-file).
	///
	/// The characer that does not verify the `predicate`
	/// (so the character that stops the skipping) is NOT skipped.
	fn skip_while(&mut self, predicate: impl Fn(char) -> bool) {
		while self.peek().is_some_and(&predicate) {
			self.skip();
		}
	}

	/// Skip whitespace characters until we arrive at a non-whitespace character.
	fn skip_whitespace(&mut self) {
		self.skip_while(|c| c.is_whitespace());
	}

	/// Run the given callable `f` on a clone of the reader,
	/// so the reader does not advance the reading (notice how this does not mutate `self`)
	/// while `f` can advance their reader to look ahead
	/// in ways that are not possible with simple peeking.
	fn look_ahead<T>(&self, f: impl FnOnce(Reader) -> T) -> T {
		f(self.clone())
	}

	/// Returns `true` iff the text that is next to be read by `self`
	/// starts by exactly the given `string_to_match`.
	fn ahead_is(&self, string_to_match: &str) -> bool {
		let mut chars_to_match = string_to_match.chars();
		self.look_ahead(|mut reader| loop {
			if let Some(char_to_match) = chars_to_match.next() {
				if reader.pop() != Some(char_to_match) {
					break false;
				}
			} else {
				break true;
			}
		})
	}

	/// Iff `ahead_is(string_to_match)` then skips all that (and returns `true`).
	fn skip_if_ahead_is(&mut self, string_to_match: &str) -> bool {
		let mut chars_to_match = string_to_match.chars();
		let reader_state_after_match = self.look_ahead(|mut reader| loop {
			if let Some(char_to_match) = chars_to_match.next() {
				if reader.pop() != Some(char_to_match) {
					break None;
				}
			} else {
				break Some(reader);
			}
		});
		if let Some(reader_state_after_match) = reader_state_after_match {
			*self = reader_state_after_match;
			true
		} else {
			false
		}
	}
}

/// The position of a character in a [`SourceCode`].
#[derive(Debug, Clone)]
pub struct Pos {
	pub(crate) source: Arc<SourceCode>,
	pub(crate) pos_simple: PosSimple,
}

/// Same as [`Pos`] but without its reference to the source.
#[derive(Debug, Clone, Copy)]
pub(crate) struct PosSimple {
	/// Index in bytes of the UTF-8 encoded version of the source code.
	pub(crate) index_in_bytes: usize,
	/// Zero-based.
	pub(crate) index_in_chars: usize,
	pub(crate) zero_based_line_number: usize,
}

impl Pos {
	fn first_character(source: Arc<SourceCode>) -> Option<Pos> {
		if source.text.is_empty() {
			// There is no first character in an empty text.
			None
		} else {
			Some(Pos {
				source,
				pos_simple: PosSimple {
					index_in_bytes: 0,
					index_in_chars: 0,
					zero_based_line_number: 0,
				},
			})
		}
	}

	fn without_source(&self) -> PosSimple {
		self.pos_simple
	}

	fn min(self, other: &Pos) -> Pos {
		Pos {
			source: self.source,
			pos_simple: self.pos_simple.min(&other.pos_simple),
		}
	}

	fn max(self, other: &Pos) -> Pos {
		Pos {
			source: self.source,
			pos_simple: self.pos_simple.max(&other.pos_simple),
		}
	}

	fn next(&self) -> Option<Pos> {
		self
			.without_source()
			.next(&self.source)
			.map(|pos| pos.with_source(Arc::clone(&self.source)))
	}

	pub fn one_char_span(self) -> Span {
		let pos_simple = self.without_source();
		Span { source: self.source, start: pos_simple, end: pos_simple }
	}

	fn is_in_same_source_than(&self, other: &Pos) -> bool {
		Arc::ptr_eq(&self.source, &other.source)
	}

	fn span_to(&self, other: &Pos) -> Span {
		assert!(self.is_in_same_source_than(other));
		self.clone().one_char_span().extend_to(other)
	}

	fn span_to_prev(&self, reader: &Reader) -> Span {
		self.span_to(&reader.prev_pos().unwrap())
	}
}

impl PosSimple {
	fn with_source(&self, source: Arc<SourceCode>) -> Pos {
		Pos { source, pos_simple: *self }
	}

	fn next(&self, source: &SourceCode) -> Option<PosSimple> {
		let character = source.text_at(*self).chars().next().unwrap();
		let next_character_exists = source.text_at(*self).chars().nth(1).is_some();
		next_character_exists.then(|| PosSimple {
			index_in_bytes: self.index_in_bytes + character.len_utf8(),
			index_in_chars: self.index_in_chars + 1,
			zero_based_line_number: self.zero_based_line_number
				+ if character == '\n' { 1 } else { 0 },
		})
	}

	fn prev(&self, source: &SourceCode) -> Option<PosSimple> {
		if self.index_in_bytes == 0 {
			None
		} else {
			for prev_char_size_in_bytes_try in 1..=4 {
				let prev_char_index_in_bytes_try = self.index_in_bytes - prev_char_size_in_bytes_try;
				if source.text.is_char_boundary(prev_char_index_in_bytes_try) {
					let character = source.text[prev_char_index_in_bytes_try..]
						.chars()
						.next()
						.unwrap();
					let zero_based_line_number =
						self.zero_based_line_number - if character == '\n' { 1 } else { 0 };
					return Some(PosSimple {
						index_in_bytes: prev_char_index_in_bytes_try,
						index_in_chars: self.index_in_chars - 1,
						zero_based_line_number,
					});
				}
			}
			unreachable!();
		}
	}

	fn min(&self, other: &PosSimple) -> PosSimple {
		PosSimple {
			index_in_bytes: self.index_in_bytes.min(other.index_in_bytes),
			index_in_chars: self.index_in_chars.min(other.index_in_chars),
			zero_based_line_number: self
				.zero_based_line_number
				.min(other.zero_based_line_number),
		}
	}

	fn max(&self, other: &PosSimple) -> PosSimple {
		PosSimple {
			index_in_bytes: self.index_in_bytes.max(other.index_in_bytes),
			index_in_chars: self.index_in_chars.max(other.index_in_chars),
			zero_based_line_number: self
				.zero_based_line_number
				.max(other.zero_based_line_number),
		}
	}
}

#[derive(Clone)]
pub struct Span {
	source: Arc<SourceCode>,
	/// Included.
	start: PosSimple,
	/// Included! Beware.
	end: PosSimple,
}

impl Debug for Span {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(
			f,
			"{}l{}:{}l{}",
			self.start.index_in_chars,
			self.start.zero_based_line_number,
			self.end.index_in_chars,
			self.end.zero_based_line_number
		)
	}
}

impl Span {
	fn start_pos(&self) -> Pos {
		self.start.with_source(Arc::clone(&self.source))
	}

	fn end_pos(&self) -> Pos {
		self.end.with_source(Arc::clone(&self.source))
	}

	fn next_pos(&self) -> Option<Pos> {
		self.end.with_source(Arc::clone(&self.source)).next()
	}

	fn is_in_same_source_than(&self, other: &Span) -> bool {
		Arc::ptr_eq(&self.source, &other.source)
	}

	fn is_in_same_source_than_pos(&self, other: &Pos) -> bool {
		Arc::ptr_eq(&self.source, &other.source)
	}

	fn combine(self, other: Span) -> Span {
		assert!(self.is_in_same_source_than(&other));
		Span {
			source: self.source,
			start: self.start.min(&other.start),
			end: self.end.max(&other.end),
		}
	}

	fn extend_to(self, pos: &Pos) -> Span {
		assert!(self.is_in_same_source_than_pos(pos));
		Span {
			source: self.source,
			start: self.start.min(&pos.without_source()),
			end: self.end.max(&pos.without_source()),
		}
	}

	pub fn as_str(&self) -> &str {
		&self.source.text[self.start.index_in_bytes..=self.end.index_in_bytes]
	}
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct LspPosition {
	pub zero_based_line_number: u32,
	/// Zero-based, index in the bytes of the line.
	pub index_in_bytes_in_line: u32,
}

pub struct LspRange {
	/// Included.
	pub start: LspPosition,
	/// Excluded! Beware.
	pub end: LspPosition,
}

impl Pos {
	fn to_lsp_position(&self) -> LspPosition {
		let line_start_in_bytes =
			self.source.line_starts.table[self.pos_simple.zero_based_line_number].index_in_bytes;
		let index_in_bytes_in_line = (self.pos_simple.index_in_bytes - line_start_in_bytes) as u32;
		LspPosition {
			zero_based_line_number: self.pos_simple.zero_based_line_number as u32,
			index_in_bytes_in_line,
		}
	}

	pub fn is_lsp_position(&self, lsp_pos: LspPosition) -> bool {
		self.to_lsp_position() == lsp_pos
	}
}

impl Span {
	pub(crate) fn zero_based_line_range(&self) -> (usize, usize) {
		(
			self.start.zero_based_line_number,
			self.end.zero_based_line_number,
		)
	}

	pub fn one_based_line_range(&self) -> (usize, usize) {
		(
			self.start.zero_based_line_number + 1,
			self.end.zero_based_line_number + 1,
		)
	}

	pub fn contains_lsp_position(&self, lsp_pos: LspPosition) -> bool {
		let line_start_in_bytes = self.source.line_starts.table
			[lsp_pos.zero_based_line_number as usize]
			.index_in_bytes as u32;
		let lsp_pos_index_in_bytes = line_start_in_bytes + lsp_pos.index_in_bytes_in_line;
		(self.start.index_in_bytes..=self.end.index_in_bytes)
			.contains(&(lsp_pos_index_in_bytes as usize))
	}

	pub fn to_lsp_range(&self) -> LspRange {
		LspRange {
			start: self
				.start
				.with_source(Arc::clone(&self.source))
				.to_lsp_position(),
			end: self
				.end
				.with_source(Arc::clone(&self.source))
				.next()
				.unwrap()
				.to_lsp_position(),
		}
	}
}

/// Integer literal token, like `41` or `0x6a`.
#[derive(Debug)]
pub struct IntegerLiteral {
	pub(crate) span: Span,
	pub(crate) radix_prefix: Option<RadixPrefix>,
	pub value: i64,
}

/// Character literal token, like `'a'` or `'\n'`.
#[derive(Debug)]
pub struct CharacterLiteral {
	pub(crate) span: Span,
	pub(crate) character_escape: Option<CharacterEscape>,
	pub value: char,
}

/// String literal token, like `"awa"`.
#[derive(Debug)]
pub struct StringLiteral {
	pub(crate) span: Span,
	pub(crate) character_escapes: Vec<CharacterEscape>,
	pub(crate) value: String,
}

/// An explicit keyword starts with `kw` in the code (like `kwexit`)
/// and serves as an internal compiler feature that is not intended
/// to be used by a Spine user when proper syntaxes and features come out.
#[derive(Debug)]
pub enum ExplicitKeywordWhich {
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

/// Explicit keyword token, like `kwexit`.
#[derive(Debug)]
pub struct ExplicitKeyword {
	pub(crate) span: Span,
	pub(crate) keyword: Option<ExplicitKeywordWhich>,
}

#[derive(Debug, Clone)]
pub struct Identifier {
	pub(crate) span: Span,
	pub(crate) name: String,
}

#[derive(Debug)]
struct Comment {
	span: Span,
	is_block: bool,
	is_doc: bool,
}

#[derive(Debug)]
struct WhitespaceAndComments {
	span: Span,
	comments: Vec<Comment>,
}

#[derive(Debug, Clone)]
pub struct UnexpectedCharacter {
	pub pos: Pos,
	pub character: char,
}

#[derive(Debug)]
enum Token {
	IntegerLiteral(IntegerLiteral),
	CharacterLiteral(CharacterLiteral),
	StringLiteral(StringLiteral),
	ExplicitKeyword(ExplicitKeyword),
	Identifier(Identifier),
	Semicolon(Pos),
	CurlyOpen(Pos),
	CurlyClose(Pos),
	WhitespaceAndComments(WhitespaceAndComments),
	UnexpectedCharacter(UnexpectedCharacter),
}

impl Token {
	fn span(&self) -> Span {
		match self {
			Token::IntegerLiteral(t) => t.span.clone(),
			Token::CharacterLiteral(t) => t.span.clone(),
			Token::StringLiteral(t) => t.span.clone(),
			Token::ExplicitKeyword(t) => t.span.clone(),
			Token::Identifier(t) => t.span.clone(),
			Token::Semicolon(pos) => pos.clone().one_char_span(),
			Token::CurlyOpen(pos) => pos.clone().one_char_span(),
			Token::CurlyClose(pos) => pos.clone().one_char_span(),
			Token::WhitespaceAndComments(t) => t.span.clone(),
			Token::UnexpectedCharacter(t) => t.pos.clone().one_char_span(),
		}
	}
}

/// Assumes that we are in a string or character literal,
/// and that the next character is the `\` that starts a character escape.
fn parse_character_escape(reader: &mut Reader) -> CharacterEscape {
	let start = reader.next_pos().unwrap();
	assert_eq!(reader.pop(), Some('\\'));
	let any_radix_digit_to_value = |any_radix_digit| match any_radix_digit {
		'0'..='9' => any_radix_digit as u32 - '0' as u32,
		'a'..='z' => any_radix_digit as u32 - 'a' as u32 + 10,
		'A'..='Z' => any_radix_digit as u32 - 'A' as u32 + 10,
		_ => panic!(),
	};
	let produced_character = match reader.pop().unwrap() {
		'x' | 'X' => {
			// `\x1b`, unicode code point (in `0..=255`) with exactly two hex digits.
			let high = reader.pop().unwrap();
			let low = reader.pop().unwrap();
			let value = any_radix_digit_to_value(high) * 16 + any_radix_digit_to_value(low);
			char::from_u32(value).unwrap()
		},
		'u' | 'U' => {
			// `\u{fffd}`, unicode code point with hex digits.
			assert_eq!(reader.pop(), Some('{'));
			let mut value = 0;
			loop {
				let character = reader.pop().unwrap();
				if character == '}' {
					break;
				}
				value = value * 16 + any_radix_digit_to_value(character);
			}
			char::from_u32(value).unwrap()
		},
		'd' | 'D' => {
			// `\d{65533}`, unicode code point with decimal digits.
			assert_eq!(reader.pop(), Some('{'));
			let mut value = 0;
			loop {
				let character = reader.pop().unwrap();
				if character == '}' {
					break;
				}
				assert!(character.is_ascii_digit());
				value = value * 10 + any_radix_digit_to_value(character);
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
	let span = start.span_to_prev(reader);
	let representation_in_source = span.as_str().to_string();
	CharacterEscape { span, produced_character, representation_in_source }
}

/// Assumes that we are at the beginning of an integer literal,
/// the next character is the first character of that integer literal.
fn parse_maybe_radix_prefix(reader: &mut Reader) -> Option<RadixPrefix> {
	let start = reader.next_pos().unwrap();
	if !reader.skip_if_eq('0') {
		// Radix prefixes all start by `0`.
		return None;
	}

	let maybe_radix_letter = reader.peek();
	if maybe_radix_letter.is_none_or(|c| !c.is_ascii_alphanumeric()) {
		// Radix prefixes all have a letter after the `0`.
		return None;
	}
	reader.skip();
	let radix_letter = maybe_radix_letter.unwrap();

	match radix_letter {
		// `0x` radix prefix
		'x' | 'X' => Some(RadixPrefix {
			span: start.span_to_prev(reader),
			kind: RadixPrefixKindAndValue::Hexadecimal,
			uppercase: radix_letter.is_uppercase(),
		}),
		// `0b` radix prefix
		'b' | 'B' => Some(RadixPrefix {
			span: start.span_to_prev(reader),
			kind: RadixPrefixKindAndValue::Binary,
			uppercase: radix_letter.is_uppercase(),
		}),
		// `0r{8}` sort of radix prefix (that can contain any supported radix number)
		'r' | 'R' => {
			assert_eq!(reader.pop(), Some('{'));
			let radix_number_start = reader.next_pos().unwrap();
			reader.skip_while(|c| c.is_ascii_digit());
			let radix_number_span = radix_number_start.span_to_prev(reader);
			assert_eq!(reader.pop(), Some('}'));
			let radix_number = radix_number_span.as_str().parse().unwrap();
			Some(RadixPrefix {
				span: start.span_to_prev(reader),
				kind: RadixPrefixKindAndValue::Arbitrary(radix_number),
				uppercase: radix_letter.is_uppercase(),
			})
		},
		unknown => panic!("unknown radix prefix char {unknown}"),
	}
}

fn will_parse_integer_literal(reader: &Reader) -> bool {
	reader.peek().is_some_and(|c| c.is_ascii_digit())
}

fn parse_integer_literal(reader: &mut Reader) -> Token {
	let start = reader.next_pos().unwrap();
	let radix_prefix = parse_maybe_radix_prefix(reader);
	if let Some(radix_prefix) = radix_prefix {
		// The number has a radix prefix, like in `0x6af2` or `0b10101`.
		// We have to get the span of the actual number part (like `6af2` or `10101`)
		// so that we can parse it (given the radix number).
		let radix_number = radix_prefix.kind.radix_number();
		if 36 < radix_number {
			unimplemented!(); // yet
		}
		reader.skip_while(|c| c.is_alphanumeric());
		let pos_after_radix_prefix = radix_prefix.span.next_pos().unwrap();
		let span_without_radix_prefix = pos_after_radix_prefix.span_to(&reader.prev_pos().unwrap());
		let value = i64::from_str_radix(span_without_radix_prefix.as_str(), radix_number).unwrap();
		let span = start.span_to(&reader.prev_pos().unwrap());
		Token::IntegerLiteral(IntegerLiteral { span, radix_prefix: Some(radix_prefix), value })
	} else {
		reader.skip_while(|c| c.is_alphanumeric());
		let span = start.span_to(&reader.prev_pos().unwrap());
		let value = span.as_str().parse::<i64>().unwrap();
		Token::IntegerLiteral(IntegerLiteral { span, radix_prefix: None, value })
	}
}

fn will_parse_character_literal(reader: &Reader) -> bool {
	reader.peek() == Some('\'')
}

fn parse_character_literal(reader: &mut Reader) -> Token {
	let first = reader.next_pos().unwrap();
	assert_eq!(reader.pop(), Some('\''));
	let character_escape = (reader.peek() == Some('\\')).then(|| parse_character_escape(reader));
	let character = if let Some(character_escape) = &character_escape {
		character_escape.produced_character
	} else {
		reader.pop().unwrap()
	};
	assert_eq!(reader.pop(), Some('\''));
	let span = first.span_to_prev(reader);
	Token::CharacterLiteral(CharacterLiteral { span, character_escape, value: character })
}

fn will_parse_string_literal(reader: &Reader) -> bool {
	reader.peek() == Some('\"')
}

fn parse_string_literal(reader: &mut Reader) -> Token {
	let first = reader.next_pos().unwrap();
	assert_eq!(reader.pop(), Some('\"'));
	let mut string = String::new();
	let mut character_escapes = vec![];
	loop {
		if reader.peek() == Some('\"') {
			reader.skip();
			break;
		} else if reader.peek() == Some('\\') {
			let character_escape = parse_character_escape(reader);
			string.push(character_escape.produced_character);
			character_escapes.push(character_escape);
		} else {
			string.push(reader.pop().unwrap());
		};
	}
	let span = first.span_to_prev(reader);
	Token::StringLiteral(StringLiteral { span, character_escapes, value: string })
}

fn will_parse_word(reader: &Reader) -> bool {
	reader.peek().is_some_and(|c| c.is_alphabetic() || c == '_')
}

fn parse_word(reader: &mut Reader) -> Token {
	let first = reader.next_pos().unwrap();
	reader.skip_while(|c| c.is_ascii_alphanumeric() || c == '_');
	let span = first.span_to_prev(reader);
	let word = span.as_str();
	if word.starts_with("kw") {
		// Explicit keyword
		let keyword = match word {
			"kwprintchar" => Some(ExplicitKeywordWhich::PrintChar),
			"kwprintstr" => Some(ExplicitKeywordWhich::PrintStr),
			"kwadd" => Some(ExplicitKeywordWhich::Add),
			"kwexit" => Some(ExplicitKeywordWhich::Exit),
			_ => None,
		};
		Token::ExplicitKeyword(ExplicitKeyword { span, keyword })
	} else {
		let name = word.to_string();
		Token::Identifier(Identifier { span, name })
	}
}

fn will_parse_whitespace_and_comments(reader: &Reader) -> bool {
	reader.peek().is_some_and(|c| c.is_whitespace()) || reader.ahead_is("--")
}

fn parse_whitespace_and_comments(reader: &mut Reader) -> Token {
	let first = reader.next_pos().unwrap();
	let mut comments = vec![];
	loop {
		reader.skip_whitespace();
		if !reader.skip_if_ahead_is("--") {
			// After skipping some whitespace we encounter something that is not a comment,
			// so this is neither whitespace nor a comment.
			// This is the end of the "whitespace and comments" token.
			break;
		}
		// We encountered a comment (and already popped the first `--` of it).
		let is_doc = reader.skip_if_eq('-');
		let is_block = reader.skip_if_eq('{');
		if is_block {
			reader.skip_while(|c| c != '}');
			reader.skip();
		} else {
			reader.skip_while(|c| c != '\n');
			reader.skip();
		}
		let span = first.span_to_prev(reader);
		let comment = Comment { span, is_block, is_doc };
		comments.push(comment);
	}
	let span = first.span_to_prev(reader);
	Token::WhitespaceAndComments(WhitespaceAndComments { span, comments })
}

/// Consumes and tokenizes the next token.
///
/// There it is, the core of the tokenizer.
fn pop_token_from_reader(reader: &mut Reader) -> Option<Token> {
	Some(if reader.peek().is_none() {
		return None;
	} else if will_parse_whitespace_and_comments(reader) {
		parse_whitespace_and_comments(reader)
	} else if will_parse_integer_literal(reader) {
		parse_integer_literal(reader)
	} else if will_parse_character_literal(reader) {
		parse_character_literal(reader)
	} else if will_parse_string_literal(reader) {
		parse_string_literal(reader)
	} else if will_parse_word(reader) {
		parse_word(reader)
	} else if reader.skip_if_eq(';') {
		Token::Semicolon(reader.prev_pos().unwrap())
	} else if reader.skip_if_eq('{') {
		Token::CurlyOpen(reader.prev_pos().unwrap())
	} else if reader.skip_if_eq('}') {
		Token::CurlyClose(reader.prev_pos().unwrap())
	} else {
		let pos = reader.next_pos().unwrap();
		let character = reader.pop().unwrap();
		Token::UnexpectedCharacter(UnexpectedCharacter { pos, character })
	})
}

fn pop_token_from_reader_ignoring_comments(reader: &mut Reader) -> Option<Token> {
	loop {
		match pop_token_from_reader(reader) {
			Some(Token::WhitespaceAndComments(_)) => continue,
			not_a_comment => break not_a_comment,
		}
	}
}

struct Tokenizer {
	reader: Reader,
	/// Peeking tokens queues them, so that they are not tokenized again when popped.
	queue: VecDeque<Token>,
}

impl Tokenizer {
	fn new(reader: Reader) -> Tokenizer {
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
pub struct HighProgram {
	pub(crate) source: Arc<SourceCode>,
	pub statements: Vec<HighStatement>,
}

enum MessageKind {
	Error,
	Warning,
}

fn print_compilation_message(kind: MessageKind, span: Span, message: String) {
	let red = "\x1b[31m";
	let yellow = "\x1b[33m";
	let color = match kind {
		MessageKind::Error => red,
		MessageKind::Warning => yellow,
	};
	let message_kind_name = match kind {
		MessageKind::Error => "error",
		MessageKind::Warning => "warning",
	};
	let default_color = "\x1b[39m";
	println!("{color}{message_kind_name}:{default_color} {message}");
	let (one_based_line_start, one_based_line_end) = span.one_based_line_range();
	if one_based_line_start == one_based_line_end {
		let one_based_line_number = one_based_line_start;
		let zero_based_line_number = one_based_line_number - 1;
		let line_span = span.source.line_span(zero_based_line_number).unwrap();
		let line_text = line_span.as_str();
		let span_start_in_line_in_chars = span.start.index_in_chars - line_span.start.index_in_chars;
		let span_end_in_line_in_chars = span.end.index_in_chars - line_span.start.index_in_chars;
		let span_start_in_line_in_bytes = line_text
			.char_indices()
			.nth(span_start_in_line_in_chars)
			.unwrap()
			.0;
		let span_end_in_line_in_bytes = line_text
			.char_indices()
			.nth(span_end_in_line_in_chars)
			.unwrap()
			.0;
		eprintln!(
			" {one_based_line_number} | {}{color}{}{default_color}{}",
			&line_text[..span_start_in_line_in_bytes],
			&line_text[span_start_in_line_in_bytes..(span_end_in_line_in_bytes + 1)],
			&line_text[(span_end_in_line_in_bytes + 1)..].trim_end(),
		);
	} else {
		unimplemented!() // yet
	}
}

pub enum CompilationError {
	UnexpectedCharacter(UnexpectedCharacter),
	UnknownIdentifier(Identifier),
}

impl CompilationError {
	pub fn span(&self) -> Span {
		match self {
			CompilationError::UnexpectedCharacter(unexpected_character) => {
				unexpected_character.pos.clone().one_char_span()
			},
			CompilationError::UnknownIdentifier(identifier) => identifier.span.clone(),
		}
	}

	pub fn message(&self) -> String {
		match self {
			CompilationError::UnexpectedCharacter(unexpected_character) => {
				format!(
					"character \'{}\' is unexpected here and causes a parsing error",
					unexpected_character.character
				)
			},
			CompilationError::UnknownIdentifier(identifier) => {
				format!("unknown identifier \"{}\"", identifier.name)
			},
		}
	}

	pub fn print(&self) {
		print_compilation_message(MessageKind::Error, self.span(), self.message());
	}
}

pub enum CompilationWarning {
	MissingTerminatingSemicolon { statement_span: Span },
}

impl CompilationWarning {
	pub fn span(&self) -> Span {
		match self {
			CompilationWarning::MissingTerminatingSemicolon { statement_span } => {
				statement_span.clone()
			},
		}
	}

	pub fn message(&self) -> String {
		match self {
			CompilationWarning::MissingTerminatingSemicolon { statement_span } => {
				"missing terminating semicolon \';\' at the end of this statement".to_string()
			},
		}
	}

	pub fn print(&self) {
		print_compilation_message(MessageKind::Warning, self.span(), self.message());
	}

	pub fn fix_by_rewrite_proposal(&self) -> Option<FixByRewrite> {
		match self {
			CompilationWarning::MissingTerminatingSemicolon { statement_span } => Some(FixByRewrite {
				description: "Add a terminating semicolon \';\'".to_string(),
				new_code: statement_span.as_str().to_string() + ";",
			}),
		}
	}
}

pub struct FixByRewrite {
	pub description: String,
	pub new_code: String,
}

impl HighStatement {
	pub fn get_errors_and_warnings(&self) -> (Vec<CompilationError>, Vec<CompilationWarning>) {
		let mut errors = vec![];
		let mut warnings = vec![];
		match self {
			HighStatement::Error { unexpected_characters, .. } => {
				for unexpected_character in unexpected_characters.iter() {
					errors.push(CompilationError::UnexpectedCharacter(
						unexpected_character.clone(),
					));
				}
			},
			HighStatement::Code { instructions, semicolon } => {
				for instruction in instructions.iter() {
					if let HighInstruction::Identifier(identifier) = instruction {
						errors.push(CompilationError::UnknownIdentifier(identifier.clone()));
					}
				}
				if semicolon.is_none() {
					let statement_span = self.span();
					warnings.push(CompilationWarning::MissingTerminatingSemicolon { statement_span });
				}
			},
			HighStatement::Block { statements, .. } => {
				for statement in statements {
					let (mut sub_errors, mut sub_warnings) = statement.get_errors_and_warnings();
					errors.append(&mut sub_errors);
					warnings.append(&mut sub_warnings);
				}
			},
			_ => {},
		}
		(errors, warnings)
	}
}

impl HighProgram {
	pub fn get_errors_and_warnings(&self) -> (Vec<CompilationError>, Vec<CompilationWarning>) {
		let mut errors = vec![];
		let mut warnings = vec![];
		for statement in self.statements.iter() {
			let (mut sub_errors, mut sub_warnings) = statement.get_errors_and_warnings();
			errors.append(&mut sub_errors);
			warnings.append(&mut sub_warnings);
		}
		(errors, warnings)
	}
}

#[derive(Debug)]
pub enum HighStatement {
	/// This statement contains code (computer programming computation waow)
	/// that actually does something when executed (so NOT a declarative statement).
	Code {
		instructions: Vec<HighInstruction>,
		semicolon: Option<Pos>,
	},
	/// A block statement containing more statements.
	Block {
		statements: Vec<HighStatement>,
		curly_open: Pos,
		curly_close: Pos,
	},
	/// A semicolon with nothing between it and the previous one or the start of file.
	/// It is valid syntax and does nothing.
	Empty { semicolon: Pos },
	/// The compiler could not parse this piece of source code into a proper statement.
	/// This should produce a compile-time error.
	Error {
		span: Span,
		unexpected_characters: Vec<UnexpectedCharacter>,
		semicolon: Option<Pos>,
	},
}

impl HighStatement {
	pub fn span(&self) -> Span {
		match self {
			HighStatement::Code { instructions, semicolon } => {
				let start = instructions.first().unwrap().span().start_pos();
				let end = if let Some(semicolon) = semicolon {
					semicolon
				} else {
					&instructions.last().unwrap().span().end_pos()
				};
				start.span_to(end)
			},
			HighStatement::Block { curly_open, curly_close, .. } => curly_open.span_to(curly_close),
			HighStatement::Empty { semicolon } => semicolon.clone().one_char_span(),
			HighStatement::Error { span, .. } => span.clone(),
		}
	}
}

#[derive(Debug)]
pub enum HighInstruction {
	IntegerLiteral(IntegerLiteral),
	CharacterLiteral(CharacterLiteral),
	StringLiteral(StringLiteral),
	ExplicitKeyword(ExplicitKeyword),
	Identifier(Identifier),
}

struct OperandAndReturnTypes {
	/// If operand types are `[A, B]` then it means `B` will be popped before `A`.
	operand_types: Vec<SpineType>,
	/// If return types are `[A, B]` then it means `A` will be pushed before `B`.
	return_types: Vec<SpineType>,
}

impl HighInstruction {
	pub fn span(&self) -> &Span {
		match self {
			HighInstruction::IntegerLiteral(t) => &t.span,
			HighInstruction::CharacterLiteral(t) => &t.span,
			HighInstruction::StringLiteral(t) => &t.span,
			HighInstruction::ExplicitKeyword(t) => &t.span,
			HighInstruction::Identifier(t) => &t.span,
		}
	}

	/// Order:
	/// - If operand types are `[A, B]` then it means `B` will be popped before `A`.
	/// - If return types are `[A, B]` then it means `A` will be pushed before `B`.
	fn operand_and_return_types(&self) -> OperandAndReturnTypes {
		match self {
			HighInstruction::IntegerLiteral(_) => {
				OperandAndReturnTypes { operand_types: vec![], return_types: vec![SpineType::I64] }
			},
			HighInstruction::CharacterLiteral(_) => {
				OperandAndReturnTypes { operand_types: vec![], return_types: vec![SpineType::I64] }
			},
			HighInstruction::StringLiteral(_) => OperandAndReturnTypes {
				operand_types: vec![],
				return_types: vec![SpineType::DataAddr, SpineType::I64],
			},
			HighInstruction::ExplicitKeyword(ExplicitKeyword { keyword, .. }) => {
				match keyword.as_ref().unwrap() {
					ExplicitKeywordWhich::PrintChar => OperandAndReturnTypes {
						operand_types: vec![SpineType::I64],
						return_types: vec![],
					},
					ExplicitKeywordWhich::PrintStr => OperandAndReturnTypes {
						operand_types: vec![SpineType::DataAddr, SpineType::I64],
						return_types: vec![],
					},
					ExplicitKeywordWhich::Add => OperandAndReturnTypes {
						operand_types: vec![SpineType::I64, SpineType::I64],
						return_types: vec![SpineType::I64],
					},
					ExplicitKeywordWhich::Exit => {
						OperandAndReturnTypes { operand_types: vec![], return_types: vec![] }
					},
				}
			},
			HighInstruction::Identifier(_) => unimplemented!(),
		}
	}
}

/// Radix prefix, such as `0x` or `0B` or `0r{12}`.
#[derive(Debug)]
pub(crate) struct RadixPrefix {
	pub(crate) span: Span,
	pub(crate) kind: RadixPrefixKindAndValue,
	/// `0x` or `0X`
	pub(crate) uppercase: bool,
}

/// The kind of radix prefix, and the radix number value.
#[derive(Debug)]
pub(crate) enum RadixPrefixKindAndValue {
	Hexadecimal,    // 0x
	Binary,         // 0b
	Arbitrary(u32), // 0r{radix}
}

impl RadixPrefixKindAndValue {
	/// The radix number,
	/// ie the base used to represent the number in the integer literal that follows.
	fn radix_number(&self) -> u32 {
		match self {
			RadixPrefixKindAndValue::Hexadecimal => 16,
			RadixPrefixKindAndValue::Binary => 2,
			RadixPrefixKindAndValue::Arbitrary(radix) => *radix,
		}
	}
}

/// A character in a charater literal or in a string literal
/// can be represented by itself (such as `a`), or by a character escape (such as `\n`).
/// This holds the information about a parsed character escape.
#[derive(Debug)]
pub(crate) struct CharacterEscape {
	pub(crate) span: Span,
	/// The character that ends up in the compiled program.
	/// This is the value that the escape sequence actually represents.
	pub(crate) produced_character: char,
	/// The escape sequence as written in the source code.
	pub(crate) representation_in_source: String,
}

fn parse_statement(tokenizer: &mut Tokenizer) -> HighStatement {
	let first_token = tokenizer.peek_token().unwrap();

	if matches!(first_token, Token::CurlyOpen(_)) {
		return parse_block_statement(tokenizer);
	}

	let mut instructions = vec![];
	let mut unexpected_characters = vec![];
	let semicolon = 'instructions: loop {
		match tokenizer.pop_token() {
			Some(Token::IntegerLiteral(integer_literal)) => {
				instructions.push(HighInstruction::IntegerLiteral(integer_literal));
			},
			Some(Token::CharacterLiteral(character_literal)) => {
				instructions.push(HighInstruction::CharacterLiteral(character_literal));
			},
			Some(Token::StringLiteral(string_literal)) => {
				instructions.push(HighInstruction::StringLiteral(string_literal))
			},
			Some(Token::ExplicitKeyword(explicit_keyword)) => {
				instructions.push(HighInstruction::ExplicitKeyword(explicit_keyword));
			},
			Some(Token::Identifier(identifier)) => {
				instructions.push(HighInstruction::Identifier(identifier));
			},
			Some(Token::WhitespaceAndComments(_)) => {},
			Some(Token::Semicolon(span)) => break 'instructions Some(span),
			Some(Token::CurlyOpen(_span)) => panic!(),
			Some(Token::CurlyClose(_span)) => panic!(),
			Some(Token::UnexpectedCharacter(unexpected)) => {
				unexpected_characters.push(unexpected);
			},
			None => {
				if instructions.is_empty() {
					panic!("expected statement but found end-of-file");
				} else {
					// Missing terminating semicolon.
					break 'instructions None;
				}
			},
		};
	};

	if !unexpected_characters.is_empty() {
		let mut start = unexpected_characters.first().unwrap().pos.clone();
		let mut end = unexpected_characters.last().unwrap().pos.clone();
		if !unexpected_characters.is_empty() {
			start = start.min(&unexpected_characters.first().unwrap().pos);
			end = end.max(&unexpected_characters.last().unwrap().pos);
		}
		if let Some(semicolon) = &semicolon {
			end = semicolon.clone();
		}
		let span = start.span_to(&end);
		HighStatement::Error { span, unexpected_characters, semicolon }
	} else if instructions.is_empty() {
		HighStatement::Empty { semicolon: semicolon.unwrap() }
	} else {
		HighStatement::Code { instructions, semicolon }
	}
}

fn parse_block_statement(tokenizer: &mut Tokenizer) -> HighStatement {
	let Token::CurlyOpen(curly_open) = tokenizer.pop_token().unwrap() else {
		panic!()
	};
	let mut statements = vec![];
	let curly_close = loop {
		let first_token = tokenizer.peek_token().unwrap();
		if let Token::CurlyClose(curly_close) = first_token {
			let curly_close = curly_close.clone();
			tokenizer.pop_token();
			break curly_close.clone();
		}
		let statement = parse_statement(tokenizer);
		statements.push(statement);
	};
	HighStatement::Block { statements, curly_open, curly_close }
}

fn parse_program(tokenizer: &mut Tokenizer) -> HighProgram {
	let mut statements = vec![];
	while tokenizer.peek_token().is_some() {
		let statement = parse_statement(tokenizer);
		statements.push(statement);
	}
	let source = Arc::clone(&tokenizer.reader.source);
	HighProgram { source, statements }
}

pub fn parse(source: Arc<SourceCode>) -> HighProgram {
	let reader = Reader::new(Arc::clone(&source));
	let mut tokenizer = Tokenizer::new(reader);
	parse_program(&mut tokenizer)
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

/// Low level instruction.
#[derive(Debug)]
enum LowInstr {
	PushConst(SpineValue),
	PushString(String),
	PopI64AndPrintAsChar,
	PopI64AndPtrAndPrintAsString,
	AddI64AndI64,
	Exit,
}

impl LowInstr {
	/// Order:
	/// - If operand types are `[A, B]` then it means `B` will be popped before `A`.
	/// - If return types are `[A, B]` then it means `A` will be pushed before `B`.
	fn operand_and_return_types(&self) -> (Vec<SpineType>, Vec<SpineType>) {
		match self {
			LowInstr::PushConst(value) => (vec![], vec![value.get_type()]),
			LowInstr::PushString(_) => (vec![], vec![SpineType::DataAddr, SpineType::I64]),
			LowInstr::PopI64AndPrintAsChar => (vec![SpineType::I64], vec![]),
			LowInstr::PopI64AndPtrAndPrintAsString => {
				(vec![SpineType::DataAddr, SpineType::I64], vec![])
			},
			LowInstr::AddI64AndI64 => (vec![SpineType::I64, SpineType::I64], vec![SpineType::I64]),
			LowInstr::Exit => (vec![], vec![]),
		}
	}
}

/// Low level statement.
#[derive(Debug)]
enum LowStatement {
	Code {
		/// In the order that they are executed, so the reverse of the order in the source code.
		instrs: Vec<LowInstr>,
	},
}

/// Low level program.
pub struct LowProgram {
	statements: Vec<LowStatement>,
}

fn compile_statement_to_low_level_statements(
	statement: &HighStatement,
	low_statements: &mut Vec<LowStatement>,
) {
	match statement {
		HighStatement::Empty { .. } => {},
		HighStatement::Error { .. } => panic!(),
		HighStatement::Block { statements, .. } => {
			for statement in statements {
				compile_statement_to_low_level_statements(statement, low_statements);
			}
		},
		HighStatement::Code { instructions, .. } => {
			// Typecheking.
			let mut excpected_type_stack = vec![];
			for instr in instructions.iter() {
				let OperandAndReturnTypes { mut operand_types, mut return_types } =
					instr.operand_and_return_types();
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

			let instrs: Vec<_> = instructions
				.iter()
				.rev()
				.map(|instruction| match instruction {
					HighInstruction::IntegerLiteral(IntegerLiteral { value, .. }) => {
						LowInstr::PushConst(SpineValue::I64(*value))
					},
					HighInstruction::CharacterLiteral(CharacterLiteral { value, .. }) => {
						LowInstr::PushConst(SpineValue::I64(*value as i64))
					},
					HighInstruction::StringLiteral(StringLiteral { value, .. }) => {
						LowInstr::PushString(value.clone())
					},
					HighInstruction::ExplicitKeyword(ExplicitKeyword { keyword, .. }) => {
						match keyword.as_ref().unwrap() {
							ExplicitKeywordWhich::PrintChar => LowInstr::PopI64AndPrintAsChar,
							ExplicitKeywordWhich::PrintStr => LowInstr::PopI64AndPtrAndPrintAsString,
							ExplicitKeywordWhich::Add => LowInstr::AddI64AndI64,
							ExplicitKeywordWhich::Exit => LowInstr::Exit,
						}
					},
					HighInstruction::Identifier(_) => unimplemented!(),
				})
				.collect();
			low_statements.push(LowStatement::Code { instrs });
		},
	}
}

pub fn compile_to_low_level(program: &HighProgram) -> LowProgram {
	let mut low_statements = vec![];
	for statement in program.statements.iter() {
		compile_statement_to_low_level_statements(statement, &mut low_statements);
	}
	LowProgram { statements: low_statements }
}

pub fn compile_to_binary(program: &LowProgram) -> Binary {
	let mut bin = Binary::new();

	use AsmInstr::*;

	for statement in program.statements.iter() {
		match statement {
			LowStatement::Code { instrs } => {
				for instr in instrs.iter() {
					match instr {
						LowInstr::PushConst(SpineValue::I64(value)) => {
							bin.asm_instrs.extend([
								MovImmToReg64 { imm_src: Imm::whatever_raw(*value), reg_dst: Reg64::Rax },
								PushReg64 { reg_src: Reg64::Rax },
							]);
						},
						LowInstr::PushConst(SpineValue::DataAddr { .. }) => {
							unimplemented!()
						},
						LowInstr::PushString(string) => {
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
						LowInstr::PopI64AndPrintAsChar => {
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
						LowInstr::PopI64AndPtrAndPrintAsString => {
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
						LowInstr::AddI64AndI64 => {
							bin.asm_instrs.extend([
								PopToReg64 { reg_dst: Reg64::Rax },
								PopToReg64 { reg_dst: Reg64::Rbx },
								AddReg64ToReg64 { reg_src: Reg64::Rbx, reg_dst: Reg64::Rax },
								PushReg64 { reg_src: Reg64::Rax },
							]);
						},
						LowInstr::Exit => {
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
