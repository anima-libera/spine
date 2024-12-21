use core::str;
use std::collections::VecDeque;
use std::fmt::Debug;
use std::path::Path;
use std::sync::Arc;

use crate::asm::{AsmInstr, Reg64};
use crate::elf::Binary;
use crate::err::{
	ArbitraryRadixMissingRadixNumber, ArbitraryRadixNumberInvalidDigit,
	ArbitraryRadixNumberTooBigUnsupported, ArbitraryRadixNumberTooSmall,
	ArbitraryRadixPrefixMissingClosingCurly, ArbitraryRadixPrefixMissingOpeningCurly,
	CharacterEscapeInvalidDigit, CharacterEscapeMissingClosingCurly,
	CharacterEscapeMissingHexadecimalDigit, CharacterEscapeMissingOpeningCurly,
	CharacterEscapeUnexpectedCharacter, CharacterLiteralMissingCharacter,
	CharacterLiteralMissingClosingQuote, CharacterLiteralMultipleCharacters,
	CharacterLiteralNonEscapedNewline, IntegerLiteralValueInvalidDigit, IntegerLiteralValueMissing,
	IntegerLiteralValueOutOfRange, StringLiteralMissingClosingQuote, UnexpectedCharacter,
	UnknownRadixPrefixLetter,
};
use crate::imm::{Imm, Imm64};
use crate::src::{Pos, Reader, SourceCode, Span};

#[derive(Debug, Clone)]
pub enum IntegerLiteralValueError {
	ValueMissing(IntegerLiteralValueMissing),
	ValueOutOfRange(IntegerLiteralValueOutOfRange),
	/// At least one.
	InvalidDigits(Vec<IntegerLiteralValueInvalidDigit>),
}

#[derive(Debug)]
pub(crate) enum RadixPrefixError {
	UnknownRadixPrefixLetter(UnknownRadixPrefixLetter),
	ArbitraryRadixPrefixMissingOpeningCurly(ArbitraryRadixPrefixMissingOpeningCurly),
	ArbitraryRadixPrefixMissingClosingCurly(ArbitraryRadixPrefixMissingClosingCurly),
}

/// Radix prefix, such as `0x` or `0B` or `0r{12}`.
#[derive(Debug)]
pub(crate) struct RadixPrefix {
	pub(crate) span: Span,
	pub(crate) kind: RadixPrefixKindAndValue,
	/// `0x` or `0X`
	pub(crate) uppercase: bool,
}

const MAX_SUPPORTED_RADIX_NUMBER: u32 = 36;

#[derive(Debug)]
pub(crate) enum ArbitraryRadixNumberError {
	TooBigUnsupported(ArbitraryRadixNumberTooBigUnsupported),
	TooSmall(ArbitraryRadixNumberTooSmall),
	MissingRadixNumber(ArbitraryRadixMissingRadixNumber),
	/// At least one.
	InvalidDigits(Vec<ArbitraryRadixNumberInvalidDigit>),
}

/// The kind of radix prefix, and the radix number value.
#[derive(Debug)]
pub(crate) enum RadixPrefixKindAndValue {
	/// `0x`
	Hexadecimal,
	/// `0b`
	Binary,
	/// `0r{radix}`, like `0r{8}`, `0r{36}`, etc.
	Arbitrary {
		radix_number: Result<u32, ArbitraryRadixNumberError>,
		radix_number_span: Option<Span>,
	},
}

impl RadixPrefixKindAndValue {
	/// The radix number,
	/// ie the base used to represent the number in the integer literal that follows.
	///
	/// Returns `None` if the radix number is too big to fit in a `u32`.
	fn radix_number(&self) -> Option<u32> {
		match self {
			RadixPrefixKindAndValue::Hexadecimal => Some(16),
			RadixPrefixKindAndValue::Binary => Some(2),
			RadixPrefixKindAndValue::Arbitrary { radix_number, .. } => {
				radix_number.as_ref().ok().copied()
			},
		}
	}
}

/// Integer literal token, like `41` or `0x6a`.
#[derive(Debug)]
pub struct IntegerLiteral {
	pub(crate) span: Span,
	pub(crate) radix_prefix: Option<Result<RadixPrefix, RadixPrefixError>>,
	/// Is `None` if `radix_prefix` has an error that prevented the parsing of the value.
	pub value: Option<Result<i64, IntegerLiteralValueError>>,
}

#[derive(Debug, Clone)]
pub enum CharacterEscapeError {
	UnexpectedCharacter(CharacterEscapeUnexpectedCharacter),
	MissingHexadecimalDigit(CharacterEscapeMissingHexadecimalDigit),
	MissingOpeningCurly(CharacterEscapeMissingOpeningCurly),
	MissingClosingCurly(CharacterEscapeMissingClosingCurly),
	InvalidDigit(CharacterEscapeInvalidDigit),
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

#[derive(Debug)]
pub enum CharacterLiteralError {
	CharacterEscapeError(CharacterEscapeError),
	MissingCharacter(CharacterLiteralMissingCharacter),
	MultipleCharacters(CharacterLiteralMultipleCharacters),
	NonEscapedNewline(CharacterLiteralNonEscapedNewline),
	MissingClosingQuote(CharacterLiteralMissingClosingQuote),
}

/// Character literal token, like `'a'` or `'\n'`.
#[derive(Debug)]
pub struct CharacterLiteral {
	pub(crate) span: Span,
	pub(crate) character_escape: Option<CharacterEscape>,
	pub value: Result<char, CharacterLiteralError>,
}

#[derive(Debug)]
pub enum StringLiteralError {
	CharacterEscapeError(CharacterEscapeError),
	MissingClosingQuote(StringLiteralMissingClosingQuote),
}

/// String literal token, like `"awa"`.
#[derive(Debug)]
pub struct StringLiteral {
	pub(crate) span: Span,
	pub(crate) character_escapes: Vec<CharacterEscape>,
	pub(crate) value: Result<String, StringLiteralError>,
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

fn any_radix_digit_to_value(any_radix_digit: char) -> Option<u32> {
	match any_radix_digit {
		'0'..='9' => Some(any_radix_digit as u32 - '0' as u32),
		'a'..='z' => Some(any_radix_digit as u32 - 'a' as u32 + 10),
		'A'..='Z' => Some(any_radix_digit as u32 - 'A' as u32 + 10),
		_ => None,
	}
}

fn will_parse_integer_literal(reader: &Reader) -> bool {
	reader.peek().is_some_and(|c| c.is_ascii_digit())
}

/// Assumes that we are at the beginning of an integer literal,
/// the next character is the first character of that integer literal.
fn parse_maybe_radix_prefix(reader: &mut Reader) -> Option<Result<RadixPrefix, RadixPrefixError>> {
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
	let radix_letter_pos = reader.prev_pos().unwrap();

	match radix_letter {
		// `0x` radix prefix
		'x' | 'X' => Some(Ok(RadixPrefix {
			span: start.span_to_prev(reader).unwrap(),
			kind: RadixPrefixKindAndValue::Hexadecimal,
			uppercase: radix_letter.is_uppercase(),
		})),

		// `0b` radix prefix
		'b' | 'B' => Some(Ok(RadixPrefix {
			span: start.span_to_prev(reader).unwrap(),
			kind: RadixPrefixKindAndValue::Binary,
			uppercase: radix_letter.is_uppercase(),
		})),

		// `0r{8}` sort of radix prefix (that can contain any supported radix number)
		'r' | 'R' => {
			// We popped `0r`, now we expect a `{`.
			let has_open_curly = reader.skip_if_eq('{');
			if !has_open_curly {
				return Some(Err(
					RadixPrefixError::ArbitraryRadixPrefixMissingOpeningCurly(
						ArbitraryRadixPrefixMissingOpeningCurly {
							span_of_0r: start.span_to(&radix_letter_pos).unwrap(),
							pos_of_not_open_curly: reader.next_pos(),
						},
					),
				));
			}
			let open_curly_pos = reader.prev_pos().unwrap();

			// We popped `0r{`, now we expect a radix number in base 10,
			// without any whitespace or sign or anything wierd.
			// We include whitespace in the span to emit a more comprehensive error when it happens.
			let radix_number_start = reader.next_pos().unwrap();
			reader.skip_while(|c| c.is_ascii_alphanumeric() || c.is_whitespace());
			let radix_number_span = radix_number_start.span_to_prev(reader);

			// We popped `0r{` and a radix number (maybe), now we expect a `}`.
			let has_close_curly = reader.skip_if_eq('}');
			if !has_close_curly {
				return Some(Err(
					RadixPrefixError::ArbitraryRadixPrefixMissingClosingCurly(
						ArbitraryRadixPrefixMissingClosingCurly {
							span_of_0r_and_open_curly: start.span_to(&open_curly_pos).unwrap(),
						},
					),
				));
			}

			// We read the whole radix prefix!
			// At this point we know that we will return a `Some(Ok(_))` and not a `Some(Err(_))`,
			// but there are still some check to be made to decide if the `radix_number`
			// field of the arbitrary radix prefix will be an `Ok(_)` or an `Err(_)`.
			let span = start.span_to_prev(reader).unwrap();

			// Make sure that the radix number that is between `0r{` and `}` was not missing,
			// i.e. that we did nit just read `0r{}`.
			let Some(radix_number_span) = radix_number_span else {
				let radix_prefix_span = span.clone();
				return Some(Ok(RadixPrefix {
					span,
					kind: RadixPrefixKindAndValue::Arbitrary {
						radix_number: Err(ArbitraryRadixNumberError::MissingRadixNumber(
							ArbitraryRadixMissingRadixNumber { radix_prefix_span },
						)),
						radix_number_span,
					},
					uppercase: radix_letter.is_uppercase(),
				}));
			};

			// Make sure that the radix number is written in base 10.
			let mut invalid_digits = vec![];
			for pos in radix_number_span.iter_pos() {
				let digit = pos.as_char();
				if !pos.as_char().is_ascii_digit() {
					let invalid_digit = digit;
					invalid_digits
						.push(ArbitraryRadixNumberInvalidDigit { invalid_digit_pos: pos, invalid_digit });
				}
			}
			if !invalid_digits.is_empty() {
				return Some(Ok(RadixPrefix {
					span,
					kind: RadixPrefixKindAndValue::Arbitrary {
						radix_number: Err(ArbitraryRadixNumberError::InvalidDigits(invalid_digits)),
						radix_number_span: Some(radix_number_span),
					},
					uppercase: radix_letter.is_uppercase(),
				}));
			}

			let radix_number: Option<u32> = radix_number_span.as_str().parse().ok();

			// Make sure that the radix number makes sense
			// (0 and 1 are the two integers that do not make sense as radix numbers).
			if let Some(radix_number @ (0 | 1)) = radix_number {
				return Some(Ok(RadixPrefix {
					span,
					kind: RadixPrefixKindAndValue::Arbitrary {
						radix_number: Err(ArbitraryRadixNumberError::TooSmall(
							ArbitraryRadixNumberTooSmall { radix_number_span: radix_number_span.clone() },
						)),
						radix_number_span: Some(radix_number_span),
					},
					uppercase: radix_letter.is_uppercase(),
				}));
			}

			// Make sure that the radix number is supported
			// (we support small radix numbers, but for example base 9000 is not supported).
			if radix_number.is_none_or(|radix_number| MAX_SUPPORTED_RADIX_NUMBER < radix_number) {
				return Some(Ok(RadixPrefix {
					span,
					kind: RadixPrefixKindAndValue::Arbitrary {
						radix_number: Err(ArbitraryRadixNumberError::TooBigUnsupported(
							ArbitraryRadixNumberTooBigUnsupported {
								radix_number_span: radix_number_span.clone(),
							},
						)),
						radix_number_span: Some(radix_number_span),
					},
					uppercase: radix_letter.is_uppercase(),
				}));
			}

			// Finally, we are sure now that we got a valid arbitrary radix prefix.
			Some(Ok(RadixPrefix {
				span,
				kind: RadixPrefixKindAndValue::Arbitrary {
					radix_number: Ok(radix_number.unwrap()),
					radix_number_span: Some(radix_number_span),
				},
				uppercase: radix_letter.is_uppercase(),
			}))
		},

		unknown => Some(Err(RadixPrefixError::UnknownRadixPrefixLetter(
			UnknownRadixPrefixLetter { radix_letter_pos },
		))),
	}
}

fn parse_integer_literal(reader: &mut Reader) -> Token {
	// Get the spans of the (optional) radix prefix and of the value part of the number.
	// In `0x00ff00ff`, `0x` is the radix prefix and `00ff00ff` is the value.

	let start = reader.next_pos().unwrap();
	let radix_prefix = parse_maybe_radix_prefix(reader);
	reader.skip_while(|c| c.is_ascii_alphanumeric());
	let span = start.span_to(&reader.prev_pos().unwrap()).unwrap();

	// Make sure that there is no error in the radix prefix (if any).
	if matches!(
		radix_prefix,
		Some(Ok(RadixPrefix {
			kind: RadixPrefixKindAndValue::Arbitrary { radix_number: Err(_), .. },
			..
		})) | Some(Err(_))
	) {
		return Token::IntegerLiteral(IntegerLiteral { span, radix_prefix, value: None });
	}

	let radix_prefix_span = radix_prefix
		.as_ref()
		.map(|radix_prefix| radix_prefix.as_ref().unwrap().span.clone());

	let value_span = radix_prefix_span.as_ref().map_or_else(
		|| Some(span.clone()),
		|radix_prefix_span| {
			radix_prefix_span
				.next_pos()
				.unwrap()
				.span_to(&reader.prev_pos().unwrap())
		},
	);

	// Make sure that there is a value.
	// A missing value would be something like `0x` with no digits after.
	let Some(value_span) = value_span else {
		return Token::IntegerLiteral(IntegerLiteral {
			span,
			radix_prefix,
			value: Some(Err(IntegerLiteralValueError::ValueMissing(
				IntegerLiteralValueMissing { radix_prefix_span: radix_prefix_span.unwrap() },
			))),
		});
	};

	let radix_number = radix_prefix
		.as_ref()
		.map(|radix_prefix| radix_prefix.as_ref().unwrap().kind.radix_number().unwrap())
		.unwrap_or(10);

	// Parse the actual value of the value part of the integer literal,
	// while recording errors that occur on the way.
	let mut value: Option<i64> = Some(0);
	let mut invalid_digits: Vec<IntegerLiteralValueInvalidDigit> = vec![];
	let mut value_is_out_of_range = false;
	for digit_pos in value_span.iter_pos() {
		let digit = digit_pos.as_char();
		let digit_value = any_radix_digit_to_value(digit).map(|d| d as i64);
		if digit_value.is_none_or(|digit_value| radix_number as i64 <= digit_value) {
			value = None;
			invalid_digits.push(IntegerLiteralValueInvalidDigit {
				radix_prefix_span: radix_prefix_span.clone(),
				value_span: value_span.clone(),
				invalid_digit_pos: digit_pos.clone(),
				invalid_digit: digit,
				radix_number,
			});
		}
		if value.is_some() {
			let new_value = value
				.unwrap()
				.checked_mul(radix_number as i64)
				.and_then(|value| value.checked_add(digit_value.unwrap()));
			if let Some(new_value) = new_value {
				value = Some(new_value);
			} else {
				value = None;
				value_is_out_of_range = true;
			}
		}
	}

	// We got all the info now.
	let value = Some(if let Some(value) = value {
		Ok(value)
	} else if !invalid_digits.is_empty() {
		Err(IntegerLiteralValueError::InvalidDigits(invalid_digits))
	} else if value_is_out_of_range {
		Err(IntegerLiteralValueError::ValueOutOfRange(
			IntegerLiteralValueOutOfRange { radix_prefix_span, integer_literal_span: span.clone() },
		))
	} else {
		unreachable!()
	});
	Token::IntegerLiteral(IntegerLiteral { span, radix_prefix, value })
}

/// Assumes that we are in a string or character literal,
/// and that the next character is the `\` that starts a character escape.
fn parse_character_escape(reader: &mut Reader) -> Result<CharacterEscape, CharacterEscapeError> {
	let start = reader.next_pos().unwrap();
	assert_eq!(reader.pop(), Some('\\'));
	let produced_character = match reader.pop().unwrap() {
		'x' | 'X' => {
			// `\x1b`, unicode code point (in `0..=255`) with exactly two hex digits.
			let mut two_hex_digits: [Option<char>; 2] = [None, None];
			#[allow(clippy::needless_range_loop)]
			for i in 0..2 {
				let character = reader.peek();
				if character.is_some_and(|c| c.is_ascii_hexdigit()) {
					two_hex_digits[i] = character;
					reader.skip();
				} else {
					return Err(CharacterEscapeError::MissingHexadecimalDigit(
						CharacterEscapeMissingHexadecimalDigit {
							backslash_x_and_maybe_first_digit_span: start.span_to_prev(reader).unwrap(),
							missing_hexadecimal_pos: character
								.is_some()
								.then(|| reader.next_pos().unwrap()),
							one_digit_was_found: i == 1,
						},
					));
				}
			}
			let value = any_radix_digit_to_value(two_hex_digits[0].unwrap()).unwrap() * 16
				+ any_radix_digit_to_value(two_hex_digits[1].unwrap()).unwrap();
			char::from_u32(value).unwrap()
		},
		'u' | 'U' => {
			// `\u{fffd}`, unicode code point with hex digits.

			let letter_pos = reader.prev_pos().unwrap();

			// We popped `\u`, now we expect a `{`.
			let has_open_curly = reader.skip_if_eq('{');
			if !has_open_curly {
				return Err(CharacterEscapeError::MissingOpeningCurly(
					CharacterEscapeMissingOpeningCurly {
						span_of_slash_and_letter: start.span_to(&reader.prev_pos().unwrap()).unwrap(),
						pos_of_not_open_curly: reader.next_pos(),
					},
				));
			}
			let open_curly_pos = reader.prev_pos().unwrap();

			let mut value = 0;
			loop {
				let character = reader.peek();
				match character {
					Some('}') => {
						reader.skip();
						break;
					},
					Some(c) if c.is_ascii_hexdigit() => {
						reader.skip();
						value = value * 16 + any_radix_digit_to_value(c).unwrap();
					},
					Some(c) => {
						let invalid_digit_pos = reader.next_pos().unwrap();
						let invalid_digit = invalid_digit_pos.as_char();
						return Err(CharacterEscapeError::InvalidDigit(
							CharacterEscapeInvalidDigit {
								invalid_digit_pos,
								invalid_digit,
								accepted_base: 16,
								span_of_slash_and_letter: start.span_to(&letter_pos).unwrap(),
							},
						));
					},
					None => {
						return Err(CharacterEscapeError::MissingClosingCurly(
							CharacterEscapeMissingClosingCurly {
								span_of_slash_letter_and_open_curly: start
									.span_to(&open_curly_pos)
									.unwrap(),
							},
						))
					},
				}
			}
			char::from_u32(value).unwrap()
		},
		'd' | 'D' => {
			// `\d{65533}`, unicode code point with decimal digits.

			let letter_pos = reader.prev_pos().unwrap();

			// We popped `\d`, now we expect a `{`.
			let has_open_curly = reader.skip_if_eq('{');
			if !has_open_curly {
				return Err(CharacterEscapeError::MissingOpeningCurly(
					CharacterEscapeMissingOpeningCurly {
						span_of_slash_and_letter: start.span_to(&reader.prev_pos().unwrap()).unwrap(),
						pos_of_not_open_curly: reader.next_pos(),
					},
				));
			}
			let open_curly_pos = reader.prev_pos().unwrap();

			let mut value = 0;
			loop {
				let character = reader.peek();
				match character {
					Some('}') => {
						reader.skip();
						break;
					},
					Some(c) if c.is_ascii_digit() => {
						reader.skip();
						value = value * 10 + any_radix_digit_to_value(c).unwrap();
					},
					Some(c) => {
						let invalid_digit_pos = reader.next_pos().unwrap();
						let invalid_digit = invalid_digit_pos.as_char();
						return Err(CharacterEscapeError::InvalidDigit(
							CharacterEscapeInvalidDigit {
								invalid_digit_pos,
								invalid_digit,
								accepted_base: 10,
								span_of_slash_and_letter: start.span_to(&letter_pos).unwrap(),
							},
						));
					},
					None => {
						return Err(CharacterEscapeError::MissingClosingCurly(
							CharacterEscapeMissingClosingCurly {
								span_of_slash_letter_and_open_curly: start
									.span_to(&open_curly_pos)
									.unwrap(),
							},
						))
					},
				}
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
		_ => {
			return Err(CharacterEscapeError::UnexpectedCharacter(
				CharacterEscapeUnexpectedCharacter {
					backslash_pos: start,
					invalid_character_pos: reader.prev_pos().unwrap(),
				},
			))
		},
	};
	let span = start.span_to_prev(reader).unwrap();
	let representation_in_source = span.as_str().to_string();
	Ok(CharacterEscape { span, produced_character, representation_in_source })
}

fn will_parse_character_literal(reader: &Reader) -> bool {
	reader.peek() == Some('\'')
}

fn parse_character_literal(reader: &mut Reader) -> Token {
	let first = reader.next_pos().unwrap();
	assert_eq!(reader.pop(), Some('\'')); // `will_parse_character_literal` made sure of that.

	let mut characters = vec![];
	let mut characters_spans = vec![];
	let mut character_escapes = vec![];
	let mut character_escape_errors = vec![];
	loop {
		if reader.peek() == Some('\'') {
			reader.skip();
			break;
		} else if reader.peek() == Some('\\') {
			let character_escape = parse_character_escape(reader);
			match character_escape {
				Err(error) => character_escape_errors.push(error),
				Ok(character_escape) => {
					characters.push(character_escape.produced_character);
					characters_spans.push(character_escape.span.clone());
					character_escapes.push(character_escape);
				},
			}
		} else if reader.peek().is_some() {
			characters.push(reader.pop().unwrap());
			characters_spans.push(reader.prev_pos().unwrap().one_char_span());
		} else {
			// End-of-file.
			let span = first.span_to_prev(reader).unwrap();
			return Token::CharacterLiteral(CharacterLiteral {
				span,
				character_escape: None,
				value: Err(CharacterLiteralError::MissingClosingQuote(
					CharacterLiteralMissingClosingQuote { open_quote_pos: first },
				)),
			});
		};
	}
	let span = first.span_to_prev(reader).unwrap();

	// Make sure that there are no invalid character escapes in the literal.
	if let Some(character_escape_error) = character_escape_errors.first() {
		return Token::CharacterLiteral(CharacterLiteral {
			span,
			character_escape: None,
			value: Err(CharacterLiteralError::CharacterEscapeError(
				character_escape_error.clone(),
			)),
		});
	}

	// Make sure that there are no non-escaped newline characters in the literal.
	for character_span in characters_spans.iter() {
		if character_span.as_str() == "\n" {
			let literal_span = span.clone();
			let newline_pos = character_span.start_pos();
			return Token::CharacterLiteral(CharacterLiteral {
				span,
				character_escape: None,
				value: Err(CharacterLiteralError::NonEscapedNewline(
					CharacterLiteralNonEscapedNewline { literal_span, newline_pos },
				)),
			});
		}
	}

	// Make sure that there are no more than one character in the literal.
	if 2 <= characters.len() {
		let literal_span = span.clone();
		return Token::CharacterLiteral(CharacterLiteral {
			span,
			character_escape: None,
			value: Err(CharacterLiteralError::MultipleCharacters(
				CharacterLiteralMultipleCharacters { literal_span, character_spans: characters_spans },
			)),
		});
	}

	// Make sure that the character in the literal is not missing.
	if characters.is_empty() {
		let literal_span = span.clone();
		return Token::CharacterLiteral(CharacterLiteral {
			span,
			character_escape: None,
			value: Err(CharacterLiteralError::MissingCharacter(
				CharacterLiteralMissingCharacter { literal_span },
			)),
		});
	}

	assert_eq!(characters.len(), 1);
	assert_eq!(characters_spans.len(), 1);
	assert!(character_escapes.len() <= 1);
	let character = characters[0];
	let character_escape = character_escapes.pop();

	Token::CharacterLiteral(CharacterLiteral { span, character_escape, value: Ok(character) })
}

fn will_parse_string_literal(reader: &Reader) -> bool {
	reader.peek() == Some('\"')
}

fn parse_string_literal(reader: &mut Reader) -> Token {
	let first = reader.next_pos().unwrap();
	assert_eq!(reader.pop(), Some('\"')); // `will_parse_string_literal` made sure of that.

	let mut string = String::new();
	let mut character_escapes = vec![];
	let mut character_escape_errors = vec![];
	loop {
		if reader.peek() == Some('\"') {
			reader.skip();
			break;
		} else if reader.peek() == Some('\\') {
			let character_escape = parse_character_escape(reader);
			match character_escape {
				Err(error) => character_escape_errors.push(error),
				Ok(character_escape) => {
					string.push(character_escape.produced_character);
					character_escapes.push(character_escape);
				},
			}
		} else if reader.peek().is_some() {
			string.push(reader.pop().unwrap());
		} else {
			// End-of-file.
			let span = first.span_to_prev(reader).unwrap();
			return Token::StringLiteral(StringLiteral {
				span,
				character_escapes: vec![],
				value: Err(StringLiteralError::MissingClosingQuote(
					StringLiteralMissingClosingQuote { open_quote_pos: first },
				)),
			});
		};
	}
	let span = first.span_to_prev(reader).unwrap();

	// Make sure that there are no invalid character escapes in the string.
	if let Some(character_escape_error) = character_escape_errors.first() {
		return Token::StringLiteral(StringLiteral {
			span,
			character_escapes,
			value: Err(StringLiteralError::CharacterEscapeError(
				character_escape_error.clone(),
			)),
		});
	}

	Token::StringLiteral(StringLiteral { span, character_escapes, value: Ok(string) })
}

fn will_parse_word(reader: &Reader) -> bool {
	reader.peek().is_some_and(|c| c.is_alphabetic() || c == '_')
}

fn parse_word(reader: &mut Reader) -> Token {
	let first = reader.next_pos().unwrap();
	reader.skip_while(|c| c.is_ascii_alphanumeric() || c == '_');
	let span = first.span_to_prev(reader).unwrap();
	let word = span.as_str();
	if word.starts_with("kw") {
		// Explicit keyword
		let keyword = match word {
			"kwpc" => Some(ExplicitKeywordWhich::PrintChar),
			"kwps" => Some(ExplicitKeywordWhich::PrintStr),
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
		let span = first.span_to_prev(reader).unwrap();
		let comment = Comment { span, is_block, is_doc };
		comments.push(comment);
	}
	let span = first.span_to_prev(reader).unwrap();
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
				start.span_to(end).unwrap()
			},
			HighStatement::Block { curly_open, curly_close, .. } => {
				curly_open.span_to(curly_close).unwrap()
			},
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

fn parse_statement(tokenizer: &mut Tokenizer) -> HighStatement {
	let first_token = tokenizer.peek_token().unwrap();

	if matches!(first_token, Token::CurlyOpen(_)) {
		return parse_block_statement(tokenizer);
	}

	let mut instructions = vec![];
	let mut unexpected_characters = vec![];
	let semicolon = 'instructions: loop {
		if matches!(tokenizer.peek_token(), Some(Token::CurlyClose(_))) {
			// Missing terminating semicolon.
			break 'instructions None;
		}
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
			Some(Token::CurlyClose(_span)) => unreachable!(),
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
		let span = start.span_to(&end).unwrap();
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
	let source = Arc::clone(tokenizer.reader.source());
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
						LowInstr::PushConst(SpineValue::I64(*value.as_ref().unwrap().as_ref().unwrap()))
					},
					HighInstruction::CharacterLiteral(CharacterLiteral { value, .. }) => {
						LowInstr::PushConst(SpineValue::I64(*value.as_ref().unwrap() as i64))
					},
					HighInstruction::StringLiteral(StringLiteral { value, .. }) => {
						LowInstr::PushString(value.as_ref().unwrap().clone())
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
