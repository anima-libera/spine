//! Matters related to reading characters (not tokens, but really just characters)
//! from the source code, managing source code text, referring to characters
//! and spans of characters in the source code.

use std::{fmt::Debug, path::Path, sync::Arc};

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

	/// Span of the line of the given zero-based line number,
	/// excluding the terminating newline character (if any).
	pub(crate) fn line_content_span(
		self: &Arc<Self>,
		zero_based_line_number: usize,
	) -> Option<Span> {
		let line_start = self.line_starts.table.get(zero_based_line_number)?;
		let line_start = PosSimple {
			index_in_bytes: line_start.index_in_bytes,
			index_in_chars: line_start.index_in_chars,
			zero_based_line_number,
		};
		let mut reader = Reader::start_at(line_start.with_source(Arc::clone(self)));
		reader.skip_while(|character| character != '\n');
		let line_end = reader.prev_pos().unwrap();
		Some(Span {
			source: Arc::clone(self),
			start: line_start,
			end: line_end.pos_simple,
		})
	}
}

/// This allows to situate a line in the source code given only the line number.
#[derive(Debug)]
pub struct LineStartTable {
	/// Line of zero-based number N starts at `table[N]` chars/bytes in the source code.
	table: Vec<LineStart>,
	/// The length (in characters, not in bytes) of the source code text.
	len_in_chars: usize,
}

/// See [`LineStartTable`].
#[derive(Debug)]
pub(crate) struct LineStart {
	/// Index in bytes of the UTF-8 encoded version of the source code.
	index_in_bytes: usize,
	/// Zero-based.
	index_in_chars: usize,
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
pub(crate) struct Reader {
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
	pub(crate) fn new(source: Arc<SourceCode>) -> Reader {
		let next = Pos::first_character(Arc::clone(&source))
			.as_ref()
			.map(Pos::without_source);
		Reader { source, next, prev: None }
	}

	fn start_at(pos: Pos) -> Reader {
		let next = pos.next().map(|p| p.pos_simple);
		let prev = Some(pos.pos_simple);
		let source = pos.source;
		Reader { source, next, prev }
	}

	pub(crate) fn source(&self) -> &Arc<SourceCode> {
		&self.source
	}

	/// Position of the previously popped character.
	pub(crate) fn prev_pos(&self) -> Option<Pos> {
		self.prev.map(|p| p.with_source(Arc::clone(&self.source)))
	}

	/// Position of the next character to be popped.
	pub(crate) fn next_pos(&self) -> Option<Pos> {
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
	pub(crate) fn peek(&self) -> Option<char> {
		self.peek_ith(0)
	}

	/// Pops the next character.
	///
	/// Meaning, we read the next character (and return it) and advance the reading head
	/// so that the character we just read is behind us now.
	pub(crate) fn pop(&mut self) -> Option<char> {
		let next_next_char_pos = self.next?.next(&self.source);
		let character = self.peek().unwrap();
		self.prev = self.next;
		self.next = next_next_char_pos;
		Some(character)
	}

	/// Pops and discards.
	pub(crate) fn skip(&mut self) {
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
	pub(crate) fn skip_if_eq(&mut self, character_to_match: char) -> bool {
		self.skip_if(|c| c == character_to_match)
	}

	/// Skip all characters we encounter while they verify the given `predicate`
	/// until we encounter a character that does not verify it (or end-of-file).
	///
	/// The characer that does not verify the `predicate`
	/// (so the character that stops the skipping) is NOT skipped.
	pub(crate) fn skip_while(&mut self, predicate: impl Fn(char) -> bool) {
		while self.peek().is_some_and(&predicate) {
			self.skip();
		}
	}

	/// Skip whitespace characters until we arrive at a non-whitespace character.
	pub(crate) fn skip_whitespace(&mut self) {
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
	pub(crate) fn ahead_is(&self, string_to_match: &str) -> bool {
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
	pub(crate) fn skip_if_ahead_is(&mut self, string_to_match: &str) -> bool {
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

impl PartialEq for Pos {
	fn eq(&self, other: &Pos) -> bool {
		self.is_in_same_source_than(other) && self.pos_simple == other.pos_simple
	}
}

impl PartialEq for PosSimple {
	fn eq(&self, other: &PosSimple) -> bool {
		self.index_in_bytes == other.index_in_bytes
	}
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

	pub(crate) fn min(self, other: &Pos) -> Pos {
		Pos {
			source: self.source,
			pos_simple: self.pos_simple.min(&other.pos_simple),
		}
	}

	pub(crate) fn max(self, other: &Pos) -> Pos {
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

	pub(crate) fn span_to(&self, other: &Pos) -> Span {
		assert!(self.is_in_same_source_than(other));
		self.clone().one_char_span().extend_to(other)
	}

	pub(crate) fn span_to_prev(&self, reader: &Reader) -> Span {
		self.span_to(&reader.prev_pos().unwrap())
	}

	pub(crate) fn as_char(&self) -> char {
		self.source.text[self.pos_simple.index_in_bytes..]
			.chars()
			.next()
			.unwrap()
	}
}

impl PosSimple {
	fn with_source(&self, source: Arc<SourceCode>) -> Pos {
		if source.text.len() <= self.index_in_bytes {
			panic!("Pos cannot be ouf of bounds of the source")
		}
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
		if self.start.zero_based_line_number == self.end.zero_based_line_number {
			write!(
				f,
				"ch{}-{} l{}",
				self.start.index_in_chars,
				self.end.index_in_chars,
				self.start.zero_based_line_number + 1
			)
		} else {
			write!(
				f,
				"ch{}-{} l{}-{}",
				self.start.index_in_chars,
				self.end.index_in_chars,
				self.start.zero_based_line_number + 1,
				self.end.zero_based_line_number + 1
			)
		}
	}
}

impl Span {
	pub(crate) fn source(&self) -> &Arc<SourceCode> {
		&self.source
	}

	pub(crate) fn start_pos(&self) -> Pos {
		self.start.with_source(Arc::clone(&self.source))
	}

	pub(crate) fn end_pos(&self) -> Pos {
		self.end.with_source(Arc::clone(&self.source))
	}

	pub(crate) fn next_pos(&self) -> Option<Pos> {
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

	fn is_empty(&self) -> bool {
		self.end.index_in_bytes < self.start.index_in_bytes
	}

	pub(crate) fn iter_pos(&self) -> SpanPositions {
		SpanPositions {
			span: self.clone(),
			next_pos: if self.is_empty() {
				None
			} else {
				Some(self.start.with_source(Arc::clone(&self.source)))
			},
		}
	}
}

/// Iterator over all the [`Pos`]s contained in a [`Span`], in order.
pub(crate) struct SpanPositions {
	span: Span,
	next_pos: Option<Pos>,
}

impl Iterator for SpanPositions {
	type Item = Pos;
	fn next(&mut self) -> Option<Pos> {
		let res = self.next_pos.take();
		self.next_pos = res.as_ref().and_then(|current| {
			if current.pos_simple == self.span.end {
				None
			} else {
				current.next()
			}
		});
		res
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
