use core::str;
use std::collections::VecDeque;
use std::fmt::Debug;
use std::path::Path;
use std::sync::Arc;

use crate::asm::{AsmInstr, Reg64};
use crate::elf::Binary;
use crate::imm::{Imm, Imm64};
use crate::src::{Pos, Reader, SourceCode, Span};

/// The value of the integer literal is too big and cannot fit in an integer.
#[derive(Debug, Clone)]
pub struct IntegerLiteralValueOutOfRange {
	radix_prefix_span: Option<Span>,
	integer_literal_span: Span,
}

/// The value of the integer literal is missing, something like `0x` with no digits after.
#[derive(Debug, Clone)]
pub struct IntegerLiteralValueMissing {
	radix_prefix_span: Span,
}

/// A digit in the integer literal is not recognized as a digit (such as `ç`)
/// or is outside the range of digits allowed by the base (given by the radix prefix)
/// (such as `9` in octal or `z` is hexadecimal).
#[derive(Debug, Clone)]
pub struct IntegerLiteralValueInvalidDigit {
	radix_prefix_span: Option<Span>,
	value_span: Span,
	invalid_digit_pos: Pos,
	invalid_digit: char,
	radix_number: u32,
}

#[derive(Debug, Clone)]
pub enum IntegerLiteralValueError {
	ValueMissing(IntegerLiteralValueMissing),
	ValueOutOfRange(IntegerLiteralValueOutOfRange),
	/// At least one.
	InvalidDigits(Vec<IntegerLiteralValueInvalidDigit>),
}

/// Something like `0y`.
#[derive(Debug, Clone)]
pub struct UnknownRadixPrefixLetter {
	radix_letter_pos: Pos,
}

/// When `0r` is not directly followed by `{`. Something like `0r@` or `0r0`.
#[derive(Debug, Clone)]
pub struct ArbitraryRadixPrefixMissingOpeningCurly {
	span_of_0r: Span,
	/// Position of the caracter that comes just after `0r`
	/// and that was supposed to be `{` but that is not.
	///
	/// `None` if end-of-file.
	pos_of_not_open_curly: Option<Pos>,
}

/// Something like `0r{36` but not followed by `}`
#[derive(Debug, Clone)]
pub struct ArbitraryRadixPrefixMissingClosingCurly {
	span_of_0r_and_open_curly: Span,
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

/// A digit in the arbitrary radix number is not a base 10 digit, such as `ç`, 'a', etc.
#[derive(Debug, Clone)]
pub struct RadixNumberInvalidDigit {
	invalid_digit_pos: Pos,
	invalid_digit: char,
}

const MAX_SUPPORTED_RADIX_NUMBER: u32 = 36;

/// Radix numbers stricly greater than [`MAX_SUPPORTED_RADIX_NUMBER`]
/// are not supported by the language.
#[derive(Debug, Clone)]
pub struct ArbitraryRadixNumberTooBigUnsupported {
	radix_number_span: Span,
}

/// 0 and 1 are too small to make sense as a radix number.
#[derive(Debug, Clone)]
pub struct ArbitraryRadixNumberTooSmall {
	radix_number_span: Span,
}

/// `0r{}`
#[derive(Debug, Clone)]
pub struct ArbitraryRadixMissingRadixNumber {
	radix_prefix_span: Span,
}

#[derive(Debug)]
pub(crate) enum ArbitraryRadixNumberError {
	TooBigUnsupported(ArbitraryRadixNumberTooBigUnsupported),
	TooSmall(ArbitraryRadixNumberTooSmall),
	MissingRadixNumber(ArbitraryRadixMissingRadixNumber),
	/// At least one.
	InvalidDigits(Vec<RadixNumberInvalidDigit>),
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
			let open_curly = reader.pop();
			if open_curly != Some('{') {
				return Some(Err(
					RadixPrefixError::ArbitraryRadixPrefixMissingOpeningCurly(
						ArbitraryRadixPrefixMissingOpeningCurly {
							span_of_0r: start.span_to(&radix_letter_pos).unwrap(),
							pos_of_not_open_curly: reader.prev_pos(),
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
			let close_curly = reader.pop();
			if close_curly != Some('}') {
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
						.push(RadixNumberInvalidDigit { invalid_digit_pos: pos, invalid_digit });
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

fn will_parse_character_literal(reader: &Reader) -> bool {
	reader.peek() == Some('\'')
}

/// Assumes that we are in a string or character literal,
/// and that the next character is the `\` that starts a character escape.
fn parse_character_escape(reader: &mut Reader) -> CharacterEscape {
	let start = reader.next_pos().unwrap();
	assert_eq!(reader.pop(), Some('\\'));
	let produced_character = match reader.pop().unwrap() {
		'x' | 'X' => {
			// `\x1b`, unicode code point (in `0..=255`) with exactly two hex digits.
			let high = reader.pop().unwrap();
			let low = reader.pop().unwrap();
			let value =
				any_radix_digit_to_value(high).unwrap() * 16 + any_radix_digit_to_value(low).unwrap();
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
				value = value * 16 + any_radix_digit_to_value(character).unwrap();
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
				value = value * 10 + any_radix_digit_to_value(character).unwrap();
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
	let span = start.span_to_prev(reader).unwrap();
	let representation_in_source = span.as_str().to_string();
	CharacterEscape { span, produced_character, representation_in_source }
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
	let span = first.span_to_prev(reader).unwrap();
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
	let span = first.span_to_prev(reader).unwrap();
	Token::StringLiteral(StringLiteral { span, character_escapes, value: string })
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

enum MessageKind {
	Error,
	Warning,
}

fn print_compilation_message(kind: MessageKind, span: Span, message: String) {
	let negative = "\x1b[7m";
	let no_negative = "\x1b[27m";
	let bold = "\x1b[1m";
	let no_bold = "\x1b[22m";
	let red = "\x1b[31m";
	let yellow = "\x1b[33m";
	let blue = "\x1b[96m";
	let color = match kind {
		MessageKind::Error => red,
		MessageKind::Warning => yellow,
	};
	let message_kind_name = match kind {
		MessageKind::Error => "error",
		MessageKind::Warning => "warning",
	};
	let default_color = "\x1b[39m";
	println!("{bold}{color}{message_kind_name}:{default_color} {message}{no_bold}");
	let (line_start, line_end) = span.line_range();
	if line_start == line_end {
		// Code of all time incoming.
		let line_number = line_start;
		let line_span = span.source().line_content_span(line_number).unwrap();
		let line_span_before = line_span.before_excluding(span.start_pos().without_source());
		let line_span_after = line_span.after_excluding(span.end_pos().without_source());
		eprintln!(
			" {blue}{}{default_color} {blue}|{default_color} {}{color}{}{default_color}{}",
			line_number.one_based(),
			line_span_before
				.as_ref()
				.map_or("", |s| s.as_str().trim_start()),
			span.as_str(),
			line_span_after
				.as_ref()
				.map_or("", |s| s.as_str().trim_end()),
		);
		let underline_start = format!(
			" {} | {}",
			line_number.one_based(),
			line_span_before
				.as_ref()
				.map_or("", |s| s.as_str().trim_start()),
		)
		.len();
		for _ in 0..underline_start {
			eprint!(" ");
		}
		eprint!("{color}");
		for _ in 0..span.as_str().chars().count() {
			eprint!("^");
		}
		let start_in_line = span.start_pos().zero_based_char_index_in_line();
		let end_in_line = span.end_pos().zero_based_char_index_in_line();
		eprintln!(
			"{default_color} {blue}{}{default_color}",
			if start_in_line == end_in_line {
				format!("char {start_in_line}")
			} else {
				format!("chars {start_in_line}-{end_in_line}")
			}
		);
	} else {
		unimplemented!() // yet
	}
}

pub enum CompilationError {
	UnexpectedCharacter(UnexpectedCharacter),
	UnknownIdentifier(Identifier),
	UnknownRadixPrefixLetter(UnknownRadixPrefixLetter),
	ArbitraryRadixPrefixMissingOpeningCurly(ArbitraryRadixPrefixMissingOpeningCurly),
	ArbitraryRadixPrefixMissingClosingCurly(ArbitraryRadixPrefixMissingClosingCurly),
	ArbitraryRadixPrefixMissingRadixNumber(ArbitraryRadixMissingRadixNumber),
	RadixNumberInvalidDigit(RadixNumberInvalidDigit),
	RadixNumberTooBigUnsupported(ArbitraryRadixNumberTooBigUnsupported),
	RadixNumberTooSmall(ArbitraryRadixNumberTooSmall),
	IntegerLiteralValueMissing(IntegerLiteralValueMissing),
	IntegerLiteralValueInvalidDigit(IntegerLiteralValueInvalidDigit),
	IntegerLiteralValueOutOfRange(IntegerLiteralValueOutOfRange),
}

impl CompilationError {
	pub fn span(&self) -> Span {
		match self {
			CompilationError::UnexpectedCharacter(error) => error.pos.clone().one_char_span(),
			CompilationError::UnknownIdentifier(error) => error.span.clone(),
			CompilationError::UnknownRadixPrefixLetter(error) => {
				error.radix_letter_pos.clone().one_char_span()
			},
			CompilationError::ArbitraryRadixPrefixMissingOpeningCurly(error) => {
				error.span_of_0r.clone()
			},
			CompilationError::ArbitraryRadixPrefixMissingClosingCurly(error) => {
				error.span_of_0r_and_open_curly.clone()
			},
			CompilationError::ArbitraryRadixPrefixMissingRadixNumber(error) => {
				error.radix_prefix_span.clone()
			},
			CompilationError::RadixNumberInvalidDigit(error) => {
				error.invalid_digit_pos.clone().one_char_span()
			},
			CompilationError::RadixNumberTooBigUnsupported(error) => error.radix_number_span.clone(),
			CompilationError::RadixNumberTooSmall(error) => error.radix_number_span.clone(),
			CompilationError::IntegerLiteralValueMissing(error) => error.radix_prefix_span.clone(),
			CompilationError::IntegerLiteralValueInvalidDigit(error) => {
				error.invalid_digit_pos.clone().one_char_span()
			},
			CompilationError::IntegerLiteralValueOutOfRange(error) => {
				error.integer_literal_span.clone()
			},
		}
	}

	pub fn message(&self) -> String {
		match self {
			CompilationError::UnexpectedCharacter(error) => format!(
				"character \'{}\' is unexpected here and causes a parsing error",
				error.character
			),
			CompilationError::UnknownIdentifier(error) => {
				format!("unknown identifier \"{}\"", error.name)
			},
			CompilationError::UnknownRadixPrefixLetter(error) => format!(
				"unknown radix prefix \"0{}\"",
				error.radix_letter_pos.as_char()
			),
			CompilationError::ArbitraryRadixPrefixMissingOpeningCurly(error) => format!(
				"arbitrary radix prefix must have an open curly \'{{\' just after \"{}\"",
				error.span_of_0r.as_str()
			),
			CompilationError::ArbitraryRadixPrefixMissingClosingCurly(error) => {
				"arbitrary radix prefix must have an close curly \'}}\' after the radix number"
					.to_string()
			},
			CompilationError::ArbitraryRadixPrefixMissingRadixNumber(error) => format!(
				"arbitrary radix prefix \"{}\" is missing a radix number in the \"{{}}\" block",
				error.radix_prefix_span.as_str()
			),
			CompilationError::RadixNumberInvalidDigit(error) => format!(
				"character \'{}\' is not a base 10 digit, must be base 10{}",
				error.invalid_digit,
				if error.invalid_digit.is_whitespace() {
					" without whitespace"
				} else {
					""
				}
			),
			CompilationError::RadixNumberTooBigUnsupported(error) => format!(
				"radix number {} is too big, the maximum supported radix number is 36",
				error.radix_number_span.as_str()
			),
			CompilationError::RadixNumberTooSmall(error) => format!(
				"radix number {} is too small to make sense, a radix number has to be at least 2",
				error.radix_number_span.as_str()
			),
			CompilationError::IntegerLiteralValueMissing(error) => format!(
				"integer literal \"{}\" has a radix prefix but is missing a value",
				error.radix_prefix_span.as_str()
			),
			CompilationError::IntegerLiteralValueInvalidDigit(error) => format!(
				"character \'{}\' is not a digit of an integer written in base {}",
				error.invalid_digit_pos.as_char(),
				error.radix_number
			),
			CompilationError::IntegerLiteralValueOutOfRange(error) => format!(
				"integer value {} is too big to fit in a 64-bit signed integer, the maximum is {}",
				error.integer_literal_span.as_str(),
				i64::MAX
			),
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
					match instruction {
						HighInstruction::Identifier(identifier) => {
							errors.push(CompilationError::UnknownIdentifier(identifier.clone()));
						},
						HighInstruction::IntegerLiteral(integer_literal) => {
							if let IntegerLiteral { radix_prefix: Some(Err(radix_prefix_error)), .. } =
								&integer_literal
							{
								match radix_prefix_error {
									RadixPrefixError::UnknownRadixPrefixLetter(error) => {
										errors
											.push(CompilationError::UnknownRadixPrefixLetter(error.clone()));
									},
									RadixPrefixError::ArbitraryRadixPrefixMissingOpeningCurly(error) => {
										errors.push(
											CompilationError::ArbitraryRadixPrefixMissingOpeningCurly(
												error.clone(),
											),
										);
									},
									RadixPrefixError::ArbitraryRadixPrefixMissingClosingCurly(error) => {
										errors.push(
											CompilationError::ArbitraryRadixPrefixMissingClosingCurly(
												error.clone(),
											),
										);
									},
								}
							}
							if let IntegerLiteral {
								radix_prefix:
									Some(Ok(RadixPrefix {
										kind:
											RadixPrefixKindAndValue::Arbitrary {
												radix_number: Err(radix_number_error),
												..
											},
										..
									})),
								..
							} = &integer_literal
							{
								match radix_number_error {
									ArbitraryRadixNumberError::InvalidDigits(invalid_digits) => {
										for invalid_digit in invalid_digits.iter() {
											errors.push(CompilationError::RadixNumberInvalidDigit(
												invalid_digit.clone(),
											));
										}
									},
									ArbitraryRadixNumberError::MissingRadixNumber(error) => {
										errors.push(
											CompilationError::ArbitraryRadixPrefixMissingRadixNumber(
												error.clone(),
											),
										);
									},
									ArbitraryRadixNumberError::TooBigUnsupported(error) => {
										errors.push(CompilationError::RadixNumberTooBigUnsupported(
											error.clone(),
										));
									},
									ArbitraryRadixNumberError::TooSmall(error) => {
										errors.push(CompilationError::RadixNumberTooSmall(error.clone()));
									},
								}
							}
							if let Some(Err(integer_error)) = &integer_literal.value {
								match integer_error {
									IntegerLiteralValueError::InvalidDigits(invalid_digits) => {
										for invalid_digit in invalid_digits.iter() {
											errors.push(CompilationError::IntegerLiteralValueInvalidDigit(
												invalid_digit.clone(),
											));
										}
									},
									IntegerLiteralValueError::ValueOutOfRange(error) => {
										errors.push(CompilationError::IntegerLiteralValueOutOfRange(
											error.clone(),
										));
									},
									IntegerLiteralValueError::ValueMissing(error) => {
										errors
											.push(CompilationError::IntegerLiteralValueMissing(error.clone()));
									},
								}
							}
						},
						_ => {},
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
