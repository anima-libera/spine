//! Matters related to reading characters (not tokens, but really just characters)
//! from the source code, managing source code text, referring to characters
//! and spans of characters in the source code.

use std::{cmp::Ordering, fmt::Debug, ops::Sub, path::Path, sync::Arc};

/// One pice of source code, for example one source file.
///
/// Used in [`Arc`]s so that many objects can access it.
/// For example [`Span`]s have an `Arc` to the source code they are a slice of.
///
/// `Arc` instead of `Rc` because `tower_lsp::LanguageServer` requires `Send` and `Sync`
/// so the language server needs to be `Sync` and `Rc` is not.
#[derive(Debug)]
pub struct SourceCode {
	/// The content of this piece of source code.
	/// If this comes from a file then this is the content of the file.
	text: String,
	/// The name of this piece of source code.
	/// If this comes from a file then this is the file path.
	name: String,
	line_starts: LineStartTable,
}

impl SourceCode {
	pub fn from_file(path: impl AsRef<Path>) -> Option<SourceCode> {
		let text = std::fs::read_to_string(&path).ok()?;
		let name = path.as_ref().to_str().unwrap().to_string();
		let line_starts = LineStartTable::compute_for_text(&text);
		Some(SourceCode { text, name, line_starts })
	}

	/// Sometimes a piece of source code does not come from a file,
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
	pub fn line_content_span(self: &Arc<Self>, line_number: LineNumber) -> Option<Span> {
		let line_start = self.line_starts.table.get(line_number.zero_based())?;
		let line_start = PosSimple {
			index_in_bytes: line_start.index_in_bytes,
			index_in_chars: line_start.index_in_chars,
			line_number,
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

/// A line number in some source code.
///
/// It removes the ambiguity between zero-based and one-based line numbers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LineNumber {
	zero_based_line_number: usize,
}

impl LineNumber {
	pub fn from_zero_based(zero_based_line_number: usize) -> LineNumber {
		LineNumber { zero_based_line_number }
	}

	/// Get the line number as a zero-based number
	/// (so a line number that assumes the first line is 0).
	///
	/// Nice for LSP (it uses zero-based line numbers) or arrays of lines.
	pub fn zero_based(self) -> usize {
		self.zero_based_line_number
	}

	/// Get the line number as a one-based number
	/// (so a line number that assumes the first line is 1).
	///
	/// Nice for displaying information to users, as IDEs display one-based line numbers.
	pub fn one_based(self) -> usize {
		self.zero_based_line_number + 1
	}

	/// Returns the smaller of two line numbers.
	fn min(self, other: LineNumber) -> LineNumber {
		LineNumber {
			zero_based_line_number: self
				.zero_based_line_number
				.min(other.zero_based_line_number),
		}
	}

	/// Returns the bigger of two line numbers.
	fn max(self, other: LineNumber) -> LineNumber {
		LineNumber {
			zero_based_line_number: self
				.zero_based_line_number
				.max(other.zero_based_line_number),
		}
	}
}

impl Sub for LineNumber {
	type Output = usize;
	fn sub(self, rhs: Self) -> Self::Output {
		self.zero_based() - rhs.zero_based()
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
		self.look_ahead(|mut reader| {
			loop {
				if let Some(char_to_match) = chars_to_match.next() {
					if reader.pop() != Some(char_to_match) {
						break false;
					}
				} else {
					break true;
				}
			}
		})
	}

	/// Iff `ahead_is(string_to_match)` then skips all that (and returns `true`).
	pub(crate) fn skip_if_ahead_is(&mut self, string_to_match: &str) -> bool {
		let mut chars_to_match = string_to_match.chars();
		let reader_state_after_match = self.look_ahead(|mut reader| {
			loop {
				if let Some(char_to_match) = chars_to_match.next() {
					if reader.pop() != Some(char_to_match) {
						break None;
					}
				} else {
					break Some(reader);
				}
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
	source: Arc<SourceCode>,
	pos_simple: PosSimple,
}

/// Same as [`Pos`] but without its reference to the source.
#[derive(Debug, Clone, Copy)]
pub(crate) struct PosSimple {
	/// Index in bytes of the UTF-8 encoded version of the source code.
	index_in_bytes: usize,
	/// Zero-based.
	index_in_chars: usize,
	line_number: LineNumber,
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

impl PartialOrd for Pos {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		if self.is_in_same_source_than(other) {
			self.pos_simple.partial_cmp(&other.pos_simple)
		} else {
			None
		}
	}
}

impl PartialOrd for PosSimple {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		self.index_in_bytes.partial_cmp(&other.index_in_bytes)
	}
}

impl Pos {
	/// Position of the first character in the given source code, if any.
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
					line_number: LineNumber { zero_based_line_number: 0 },
				},
			})
		}
	}

	pub(crate) fn without_source(&self) -> PosSimple {
		self.pos_simple
	}

	/// Returns the smaller of two character positions, meaning the one that comes first.
	pub(crate) fn min(self, other: &Pos) -> Pos {
		Pos {
			source: self.source,
			pos_simple: self.pos_simple.min(&other.pos_simple),
		}
	}

	/// Returns the bigger of two character positions, meaning the one that comes last.
	pub(crate) fn max(self, other: &Pos) -> Pos {
		Pos {
			source: self.source,
			pos_simple: self.pos_simple.max(&other.pos_simple),
		}
	}

	/// The position after `self`, if it exists in the source code (so not if it is end-of-file).
	pub(crate) fn next(&self) -> Option<Pos> {
		self
			.without_source()
			.next(&self.source)
			.map(|pos| pos.with_source(Arc::clone(&self.source)))
	}

	/// The position before `self`, if it exists in the source code
	/// (so not if `self` is the first character of its file).
	pub(crate) fn prev(&self) -> Option<Pos> {
		self
			.without_source()
			.prev(&self.source)
			.map(|pos| pos.with_source(Arc::clone(&self.source)))
	}

	/// Transforms a character position into a character span that spans just this character.
	pub fn one_char_span(self) -> Span {
		let pos_simple = self.without_source();
		Span { source: self.source, start: pos_simple, end: pos_simple }
	}

	fn is_in_same_source_than(&self, other: &Pos) -> bool {
		Arc::ptr_eq(&self.source, &other.source)
	}

	/// Returns the span from `self` (included) to `other` (included),
	/// or `None` if `other` is before `self` (which would make the span empty).
	pub(crate) fn span_to(&self, other: &Pos) -> Option<Span> {
		assert!(self.is_in_same_source_than(other));
		if other.pos_simple.index_in_bytes < self.pos_simple.index_in_bytes {
			None
		} else {
			Some(self.clone().one_char_span().extend_to(other))
		}
	}

	/// Gets the span
	/// from `self` (included) to the last character popped from the reader (included).
	pub(crate) fn span_to_prev(&self, reader: &Reader) -> Option<Span> {
		self.span_to(&reader.prev_pos()?)
	}

	/// Reads the character that `self` is the position of.
	pub(crate) fn as_char(&self) -> char {
		self.source.text[self.pos_simple.index_in_bytes..]
			.chars()
			.next()
			.unwrap()
	}

	/// Returns 0 if it is the first character of its line,
	/// returns N-1 if it is the last character of its line of N characters,
	/// etc.
	///
	/// This deals in characters, not bytes.
	pub(crate) fn zero_based_char_index_in_line(&self) -> usize {
		let line_start_in_chars =
			self.source.line_starts.table[self.pos_simple.line_number.zero_based()].index_in_chars;
		self.pos_simple.index_in_chars - line_start_in_chars
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
			line_number: if character == '\n' {
				LineNumber { zero_based_line_number: self.line_number.zero_based() + 1 }
			} else {
				self.line_number
			},
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
					let line_number = if character == '\n' {
						LineNumber { zero_based_line_number: self.line_number.zero_based() - 1 }
					} else {
						self.line_number
					};
					return Some(PosSimple {
						index_in_bytes: prev_char_index_in_bytes_try,
						index_in_chars: self.index_in_chars - 1,
						line_number,
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
			line_number: self.line_number.min(other.line_number),
		}
	}

	fn max(&self, other: &PosSimple) -> PosSimple {
		PosSimple {
			index_in_bytes: self.index_in_bytes.max(other.index_in_bytes),
			index_in_chars: self.index_in_chars.max(other.index_in_chars),
			line_number: self.line_number.max(other.line_number),
		}
	}
}

/// Range of characters in a [`SourceCode`], can NOT be empty.
#[derive(Clone)]
pub struct Span {
	source: Arc<SourceCode>,
	/// Included.
	start: PosSimple,
	/// Included! Beware.
	///
	/// If `end` == `start` then the span is one character long.
	///
	/// `end` cannot be strictly before `start`.
	end: PosSimple,
}

impl Debug for Span {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		if self.start.line_number == self.end.line_number {
			write!(
				f,
				"ch{}-{} l{}",
				self.start.index_in_chars,
				self.end.index_in_chars,
				self.start.line_number.one_based()
			)
		} else {
			write!(
				f,
				"ch{}-{} l{}-{}",
				self.start.index_in_chars,
				self.end.index_in_chars,
				self.start.line_number.one_based(),
				self.end.line_number.one_based()
			)
		}
	}
}

impl Span {
	pub fn source(&self) -> &Arc<SourceCode> {
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

	pub(crate) fn combine(self, other: Span) -> Span {
		assert!(self.is_in_same_source_than(&other));
		Span {
			source: self.source,
			start: self.start.min(&other.start),
			end: self.end.max(&other.end),
		}
	}

	pub(crate) fn extend_to(self, pos: &Pos) -> Span {
		assert!(self.is_in_same_source_than_pos(pos));
		Span {
			source: self.source,
			start: self.start.min(&pos.without_source()),
			end: self.end.max(&pos.without_source()),
		}
	}

	/// The text (from the source code) that this span covers.
	pub fn as_str(&self) -> &str {
		&self.source.text[self.start.index_in_bytes..=self.end.index_in_bytes]
	}

	/// The number of characters (not bytes) that this span contains.
	pub(crate) fn char_count(&self) -> usize {
		self.end.index_in_chars - self.start.index_in_chars + 1
	}

	fn is_empty(&self) -> bool {
		self.end.index_in_bytes < self.start.index_in_bytes

		// TODO: What is the meaning of this? `Span`'s doc says it cannot be empty. What?
	}

	/// Part of the span that is on the left of the given pos, excluding the pos.
	pub(crate) fn before_excluding(&self, pos: PosSimple) -> Option<Span> {
		if pos <= self.start {
			None
		} else if pos <= self.end {
			Some(Span {
				source: Arc::clone(&self.source),
				start: self.start,
				end: pos.prev(&self.source)?,
			})
		} else {
			Some(self.clone())
		}
	}

	/// Part of the span that is on the right of the given pos, excluding the pos.
	pub(crate) fn after_excluding(&self, pos: PosSimple) -> Option<Span> {
		if self.end <= pos {
			None
		} else if self.start <= pos {
			Some(Span {
				source: Arc::clone(&self.source),
				start: pos.next(&self.source)?,
				end: self.end,
			})
		} else {
			Some(self.clone())
		}
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

/// VSCode really likes utf-16, at the time of writing its LSP client-side thingy doesn't support
/// `PositionEncodingKind::UTF8` (it used to but it stopped). Let's go for the utf-16 thingy
/// (for which the support is mendatory as per LSP documentation) to make sure the extension
/// works now and will never break again for this stupid reason.
///
/// Use [`LspPositionUtf16::to_lsp_position`] and [`LspPosition::to_lsp_position_utf16`]
/// to convert between capitalist utf-16 (bad) and communist utf-8 (epic).
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct LspPositionUtf16 {
	pub zero_based_line_number: u32,
	/// Zero-based, index in utf-16 code units in the utf-16 representation of the line of code.
	pub index_in_utf16_code_units_in_line: u32,
}

impl LspPositionUtf16 {
	pub fn to_lsp_position(self, line_str: &str) -> LspPosition {
		let target_utf16_index = self.index_in_utf16_code_units_in_line as usize;
		let mut line_chars = line_str.chars().chain(std::iter::once('\n'));
		let mut head_utf16_index = 0;
		let mut head_utf8_index = 0;
		loop {
			if head_utf16_index == target_utf16_index {
				return LspPosition {
					zero_based_line_number: self.zero_based_line_number,
					index_in_bytes_in_line: head_utf8_index as u32,
				};
			}
			let Some(character) = line_chars.next() else {
				break;
			};
			head_utf16_index += character.len_utf16();
			head_utf8_index += character.len_utf8();
		}
		panic!(
			"to_lsp_position couldn't convert utf-16 index to utf-8 index, at line {} (1-based)",
			self.zero_based_line_number + 1
		)
	}
}

impl LspPosition {
	pub fn to_lsp_position_utf16(self, line_str: &str) -> LspPositionUtf16 {
		let target_utf8_index = self.index_in_bytes_in_line as usize;
		let mut line_chars = line_str.chars().chain(std::iter::once('\n'));
		let mut head_utf16_index = 0;
		let mut head_utf8_index = 0;
		loop {
			if head_utf8_index == target_utf8_index {
				return LspPositionUtf16 {
					zero_based_line_number: self.zero_based_line_number,
					index_in_utf16_code_units_in_line: head_utf16_index as u32,
				};
			}
			let Some(character) = line_chars.next() else {
				break;
			};
			head_utf16_index += character.len_utf16();
			head_utf8_index += character.len_utf8();
		}
		panic!(
			"to_lsp_position couldn't convert utf-8 index to utf-16 index, at line {} (1-based)",
			self.zero_based_line_number + 1
		)
	}
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct LspPosition {
	pub zero_based_line_number: u32,
	/// Zero-based, index in the bytes of the line.
	pub index_in_bytes_in_line: u32,
}

pub struct LspRangeUtf16 {
	/// Included.
	pub start: LspPositionUtf16,
	/// Excluded! Beware.
	pub end: LspPositionUtf16,
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
			self.source.line_starts.table[self.pos_simple.line_number.zero_based()].index_in_bytes;
		let index_in_bytes_in_line = (self.pos_simple.index_in_bytes - line_start_in_bytes) as u32;
		LspPosition {
			zero_based_line_number: self.pos_simple.line_number.zero_based() as u32,
			index_in_bytes_in_line,
		}
	}

	/// Like `to_lsp_position` but for the next character in the line, whether it exists or not.
	fn to_lsp_position_next_in_line(&self) -> LspPosition {
		let mut lsp_position = self.to_lsp_position();
		lsp_position.index_in_bytes_in_line += self.as_char().len_utf8() as u32;
		lsp_position
	}

	pub fn is_lsp_position(&self, lsp_pos: LspPosition) -> bool {
		self.to_lsp_position() == lsp_pos
	}
}

impl Span {
	/// End is included.
	pub fn line_range(&self) -> (LineNumber, LineNumber) {
		(self.start.line_number, self.end.line_number)
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
				.to_lsp_position_next_in_line(),
		}
	}

	pub fn to_lsp_range_utf16(&self) -> LspRangeUtf16 {
		let lsp_range = self.to_lsp_range();

		let line_start_span = self.source.line_content_span(self.line_range().0).unwrap();
		let line_end_span = self.source.line_content_span(self.line_range().1).unwrap();

		LspRangeUtf16 {
			start: lsp_range
				.start
				.to_lsp_position_utf16(line_start_span.as_str()),
			end: lsp_range.end.to_lsp_position_utf16(line_end_span.as_str()),
		}
	}
}
