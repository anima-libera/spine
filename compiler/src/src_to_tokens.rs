use std::{collections::VecDeque, sync::Arc};

use crate::{
	err::{
		ArbitraryRadixMissingRadixNumber, ArbitraryRadixNumberInvalidDigit,
		ArbitraryRadixNumberTooBigUnsupported, ArbitraryRadixNumberTooSmall,
		ArbitraryRadixPrefixMissingClosingCurly, ArbitraryRadixPrefixMissingOpeningCurly,
		CharacterEscapeInvalidDigit, CharacterEscapeInvalidUnicodeScalarValue,
		CharacterEscapeMissingClosingCurly, CharacterEscapeMissingHexadecimalDigit,
		CharacterEscapeMissingNumber, CharacterEscapeMissingOpeningCurly,
		CharacterEscapeUnexpectedCharacter, CharacterLiteralMissingCharacter,
		CharacterLiteralMissingClosingQuote, CharacterLiteralMultipleCharacters,
		CharacterLiteralNonEscapedNewline, IntegerLiteralValueInvalidDigit,
		IntegerLiteralValueMissing, IntegerLiteralValueOutOfRange, StringLiteralMissingClosingQuote,
		UnexpectedCharacter, UnknownRadixPrefixLetter,
	},
	keywords::{DEFAULT_KEYWORDS, KeywordWhich},
	src::{Reader, SourceCode},
	tokens::{
		ArbitraryRadixNumberError, CharacterEscape, CharacterEscapeError, CharacterLiteral,
		CharacterLiteralError, Comment, Identifier, IntegerLiteral, IntegerLiteralValueError,
		Keyword, MAX_SUPPORTED_RADIX_NUMBER, RadixPrefix, RadixPrefixError, RadixPrefixKindAndValue,
		StringLiteral, StringLiteralError, Token,
	},
};

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
			// but there are still some checks to be made to decide if the `radix_number`
			// field of the arbitrary radix prefix will be an `Ok(_)` or an `Err(_)`.
			let span = start.span_to_prev(reader).unwrap();

			// Make sure that the radix number that is between `0r{` and `}` was not missing,
			// i.e. that we did not just read `0r{}`.
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
			if let Some(0 | 1) = radix_number {
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

		_unknown => Some(Err(RadixPrefixError::UnknownRadixPrefixLetter(
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

			// TODO: Factorize with the 'd' | 'D' case!

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

			// Now we expect a number and a `}` without any whitespace.
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
					Some(_c) => {
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
						));
					},
				}
			}
			let close_curly_pos = reader.prev_pos().unwrap();

			// Make sure the number between `{` and `}` has at least one digit.
			let Some(span_of_number) = open_curly_pos
				.next()
				.unwrap()
				.span_to(&close_curly_pos.prev().unwrap())
			else {
				return Err(CharacterEscapeError::MissingNumber(
					CharacterEscapeMissingNumber { span: start.span_to_prev(reader).unwrap() },
				));
			};

			match char::from_u32(value) {
				Some(character) => character,
				None => {
					let value_ = u64::from_str_radix(span_of_number.as_str(), 16).ok();
					return Err(CharacterEscapeError::InvalidUnicodeScalarValue(
						CharacterEscapeInvalidUnicodeScalarValue { span_of_number, value: value_ },
					));
				},
			}
		},
		'd' | 'D' => {
			// `\d{65533}`, unicode code point with decimal digits.

			// TODO: Factorize with the 'u' | 'U' case!

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

			// Now we expect a number and a `}` without any whitespace.
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
					Some(_c) => {
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
						));
					},
				}
			}
			let close_curly_pos = reader.prev_pos().unwrap();

			// Make sure the number between `{` and `}` has at least one digit.
			let Some(span_of_number) = open_curly_pos
				.next()
				.unwrap()
				.span_to(&close_curly_pos.prev().unwrap())
			else {
				return Err(CharacterEscapeError::MissingNumber(
					CharacterEscapeMissingNumber { span: start.span_to_prev(reader).unwrap() },
				));
			};

			match char::from_u32(value) {
				Some(character) => character,
				None => {
					let value_ = span_of_number.as_str().parse().ok();
					return Err(CharacterEscapeError::InvalidUnicodeScalarValue(
						CharacterEscapeInvalidUnicodeScalarValue { span_of_number, value: value_ },
					));
				},
			}
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
			));
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

/// A word can be an identifier or a keyword.
fn parse_word(reader: &mut Reader) -> Token {
	let first = reader.next_pos().unwrap();
	reader.skip_while(|c| c.is_ascii_alphanumeric() || c == '_');
	let span = first.span_to_prev(reader).unwrap();
	let word = span.as_str();

	let identify_keyword = |word| -> Option<KeywordWhich> {
		DEFAULT_KEYWORDS
			.iter()
			.find_map(|wk_in_lang| (wk_in_lang.word == word).then_some(wk_in_lang.which))
	};
	let keyword_and_kw_prefix = if let Some(word) = word.strip_prefix("kw") {
		Some((identify_keyword(word), true))
	} else {
		identify_keyword(word).map(|keyword| (Some(keyword), false))
	};

	if let Some((keyword, kw_prefix)) = keyword_and_kw_prefix {
		Token::Keyword(Keyword { span, kw_prefix, keyword })
	} else {
		let name = word.to_string();
		Token::Identifier(Identifier { span, name })
	}
}

fn will_parse_comment(reader: &Reader) -> bool {
	reader.ahead_is("--")
}

fn parse_comment(reader: &mut Reader) -> Token {
	let first = reader.next_pos().unwrap();
	assert!(reader.skip_if_ahead_is("--")); // `will_parse_comment` made sure of that.

	let is_doc = reader.skip_if_eq('-');
	let is_block = reader.skip_if_eq('{');
	let mut is_missing_expected_closing_curly = false;
	if is_block {
		// Block comment, that supports nested blocks.
		let mut depth = 1;
		loop {
			reader.skip_while(|c| c != '{' && c != '}');
			match reader.pop() {
				Some('{') => depth += 1,
				Some('}') => depth -= 1,
				Some(_) => unreachable!(),
				None => {
					is_missing_expected_closing_curly = true;
					break;
				},
			}
			if depth == 0 {
				break;
			}
		}
	} else {
		// Line comment.
		reader.skip_while(|c| c != '\n');
		reader.skip();
	}

	let span = first.span_to_prev(reader).unwrap();
	Token::Comment(Comment { span, is_block, is_doc, is_missing_expected_closing_curly })
}

fn will_parse_whitespace(reader: &Reader) -> bool {
	reader.peek().is_some_and(|c| c.is_whitespace())
}

fn parse_whitespace(reader: &mut Reader) -> Token {
	let first = reader.next_pos().unwrap();
	reader.skip_whitespace();
	let span = first.span_to_prev(reader).unwrap();
	Token::Whitespace(span)
}

/// Consumes and tokenizes the next token.
///
/// There it is, the core of the tokenizer.
fn pop_token_from_reader(reader: &mut Reader) -> Option<Token> {
	Some(if reader.peek().is_none() {
		return None;
	} else if will_parse_whitespace(reader) {
		parse_whitespace(reader)
	} else if will_parse_comment(reader) {
		parse_comment(reader)
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

fn pop_token_from_reader_ignoring_whitespace_and_comments(reader: &mut Reader) -> Option<Token> {
	loop {
		match pop_token_from_reader(reader) {
			Some(Token::Whitespace(_)) => continue,
			Some(Token::Comment(_)) => continue,
			important => break important,
		}
	}
}

pub(crate) struct Tokenizer {
	pub(crate) reader: Reader,
	/// Peeking tokens queues them, so that they are not tokenized again when popped.
	queue: VecDeque<Token>,
}

impl Tokenizer {
	pub(crate) fn new(reader: Reader) -> Tokenizer {
		Tokenizer { reader, queue: VecDeque::new() }
	}

	pub(crate) fn pop_token(&mut self) -> Option<Token> {
		if let Some(token) = self.queue.pop_front() {
			Some(token)
		} else {
			pop_token_from_reader_ignoring_whitespace_and_comments(&mut self.reader)
		}
	}

	fn peek_ith_token(&mut self, index: usize) -> Option<&Token> {
		while self.queue.len() <= index {
			let token = pop_token_from_reader_ignoring_whitespace_and_comments(&mut self.reader)?;
			self.queue.push_back(token);
		}
		Some(&self.queue[index])
	}

	pub(crate) fn peek_token(&mut self) -> Option<&Token> {
		self.peek_ith_token(0)
	}
}

pub fn list_tokens_except_whitespace(source: Arc<SourceCode>) -> Vec<Token> {
	let mut reader = Reader::new(Arc::clone(&source));
	let mut tokens = vec![];
	while let Some(token) = pop_token_from_reader(&mut reader) {
		if let Token::Whitespace(_) = token {
		} else {
			tokens.push(token);
		}
	}
	tokens
}
