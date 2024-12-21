//! Compile-time errors and warnings.

use crate::{
	lang::{
		ArbitraryRadixNumberError, CharacterEscapeError, CharacterLiteral, CharacterLiteralError,
		HighInstruction, HighProgram, HighStatement, Identifier, IntegerLiteral,
		IntegerLiteralValueError, RadixPrefix, RadixPrefixError, RadixPrefixKindAndValue,
		StringLiteralError,
	},
	src::{Pos, Span},
};

#[derive(Debug, Clone)]
pub struct UnexpectedCharacter {
	pub pos: Pos,
	pub character: char,
}

/// Something like `0y`.
#[derive(Debug, Clone)]
pub struct UnknownRadixPrefixLetter {
	pub(crate) radix_letter_pos: Pos,
}

/// When `0r` is not directly followed by `{`. Something like `0r@` or `0r0`.
#[derive(Debug, Clone)]
pub struct ArbitraryRadixPrefixMissingOpeningCurly {
	pub(crate) span_of_0r: Span,
	/// Position of the caracter that comes just after `0r`
	/// and that was supposed to be `{` but that is not.
	///
	/// `None` if end-of-file.
	pub(crate) pos_of_not_open_curly: Option<Pos>,
}

/// Something like `0r{36` but not followed by `}`
#[derive(Debug, Clone)]
pub struct ArbitraryRadixPrefixMissingClosingCurly {
	pub(crate) span_of_0r_and_open_curly: Span,
}

/// The value of the integer literal is too big and cannot fit in an integer.
#[derive(Debug, Clone)]
pub struct IntegerLiteralValueOutOfRange {
	pub(crate) radix_prefix_span: Option<Span>,
	pub(crate) integer_literal_span: Span,
}

/// The value of the integer literal is missing, something like `0x` with no digits after.
#[derive(Debug, Clone)]
pub struct IntegerLiteralValueMissing {
	pub(crate) radix_prefix_span: Span,
}

/// A digit in the integer literal is not recognized as a digit (such as `ç`)
/// or is outside the range of digits allowed by the base (given by the radix prefix)
/// (such as `9` in octal or `z` is hexadecimal).
#[derive(Debug, Clone)]
pub struct IntegerLiteralValueInvalidDigit {
	pub(crate) radix_prefix_span: Option<Span>,
	pub(crate) value_span: Span,
	pub(crate) invalid_digit_pos: Pos,
	pub(crate) invalid_digit: char,
	pub(crate) radix_number: u32,
}

/// A digit in the arbitrary radix number is not a base 10 digit, such as `ç`, 'a', etc.
#[derive(Debug, Clone)]
pub struct ArbitraryRadixNumberInvalidDigit {
	pub(crate) invalid_digit_pos: Pos,
	pub(crate) invalid_digit: char,
}

/// Radix numbers stricly greater than [`MAX_SUPPORTED_RADIX_NUMBER`]
/// are not supported by the language.
#[derive(Debug, Clone)]
pub struct ArbitraryRadixNumberTooBigUnsupported {
	pub(crate) radix_number_span: Span,
}

/// 0 and 1 are too small to make sense as a radix number.
#[derive(Debug, Clone)]
pub struct ArbitraryRadixNumberTooSmall {
	pub(crate) radix_number_span: Span,
}

/// `0r{}`
#[derive(Debug, Clone)]
pub struct ArbitraryRadixMissingRadixNumber {
	pub(crate) radix_prefix_span: Span,
}

/// Character literal that contains no character, like `''`.
#[derive(Debug, Clone)]
pub struct CharacterLiteralMissingCharacter {
	pub(crate) literal_span: Span,
}

/// Character literal that contains multiple characters (where only one is expected), like `'aa'`.
#[derive(Debug, Clone)]
pub struct CharacterLiteralMultipleCharacters {
	pub(crate) literal_span: Span,
	/// The spans of each characters. At least two.
	pub(crate) character_spans: Vec<Span>,
}

/// Character literal contains a non-escaped newline.
#[derive(Debug, Clone)]
pub struct CharacterLiteralNonEscapedNewline {
	pub(crate) literal_span: Span,
	pub(crate) newline_pos: Pos,
}

/// Character literal is never closed.
#[derive(Debug, Clone)]
pub struct CharacterLiteralMissingClosingQuote {
	pub(crate) open_quote_pos: Pos,
}

/// String literal is never closed.
#[derive(Debug, Clone)]
pub struct StringLiteralMissingClosingQuote {
	pub(crate) open_quote_pos: Pos,
}

/// When the character that follows the `\` in a character escape is invalid, such as `\!`.
#[derive(Debug, Clone)]
pub struct CharacterEscapeUnexpectedCharacter {
	pub(crate) backslash_pos: Pos,
	pub(crate) invalid_character_pos: Pos,
}

/// When there are zero or only one hexadecimal digit after `\x` when two are expected.
#[derive(Debug, Clone)]
pub struct CharacterEscapeMissingHexadecimalDigit {
	pub(crate) backslash_x_and_maybe_first_digit_span: Span,
	/// If `None` then it means that end-of-file was found instead of an hexadecimal digit,
	/// if `Some` then it means that an unexpected character was found in the place of
	/// an expected hexadecimal digit.
	pub(crate) missing_hexadecimal_pos: Option<Pos>,
	/// Distinguish between `\x@` and `\xa@`,
	/// where in the first case we did not even found the first of the two expected hex digits,
	/// of the second case where we did find one hex digit but not the second one.
	///
	/// `false` means that we found no hex digit,
	/// `true` means that we did find the first digit but the second one is missing.
	pub(crate) one_digit_was_found: bool,
}

/// When `\u` or `\d` is not directly followed by `{`.
#[derive(Debug, Clone)]
pub struct CharacterEscapeMissingOpeningCurly {
	/// Span of `\u` or `\d`.
	pub(crate) span_of_slash_and_letter: Span,
	/// Position of the caracter that comes just after `\u` or `\d`
	/// and that was supposed to be `{` but that is not.
	///
	/// `None` if end-of-file.
	pub(crate) pos_of_not_open_curly: Option<Pos>,
}

/// Something like `0u{aeae` or `0d{1919` but not followed by `}`
#[derive(Debug, Clone)]
pub struct CharacterEscapeMissingClosingCurly {
	/// Span of `0u{` or `0d{`.
	pub(crate) span_of_slash_letter_and_open_curly: Span,
}

/// A digit in the character escape number is not in the right base
/// (10 for `\d{...}`, 16 for `\u{...}`).
#[derive(Debug, Clone)]
pub struct CharacterEscapeInvalidDigit {
	pub(crate) invalid_digit_pos: Pos,
	pub(crate) invalid_digit: char,
	pub(crate) accepted_base: u32,
	/// Span of `\u` or `\d`.
	pub(crate) span_of_slash_and_letter: Span,
}

/// A character described with an escape like `\u{ffffffffff}` is not a valid character
/// as a Unicode scalar value is expected (like a Rust char).
#[derive(Debug, Clone)]
pub struct CharacterEscapeInvalidUnicodeScalarValue {
	pub(crate) span_of_number: Span,
	pub(crate) value: Option<u64>,
}

/// Something like `\u{}` or `\d{}`.
#[derive(Debug, Clone)]
pub struct CharacterEscapeMissingNumber {
	pub(crate) span: Span,
}

pub enum CompilationError {
	UnexpectedCharacter(UnexpectedCharacter),
	UnknownIdentifier(Identifier),
	UnknownRadixPrefixLetter(UnknownRadixPrefixLetter),
	ArbitraryRadixPrefixMissingOpeningCurly(ArbitraryRadixPrefixMissingOpeningCurly),
	ArbitraryRadixPrefixMissingClosingCurly(ArbitraryRadixPrefixMissingClosingCurly),
	ArbitraryRadixPrefixMissingRadixNumber(ArbitraryRadixMissingRadixNumber),
	RadixNumberInvalidDigit(ArbitraryRadixNumberInvalidDigit),
	RadixNumberTooBigUnsupported(ArbitraryRadixNumberTooBigUnsupported),
	RadixNumberTooSmall(ArbitraryRadixNumberTooSmall),
	IntegerLiteralValueMissing(IntegerLiteralValueMissing),
	IntegerLiteralValueInvalidDigit(IntegerLiteralValueInvalidDigit),
	IntegerLiteralValueOutOfRange(IntegerLiteralValueOutOfRange),
	CharacterLiteralMissingCharacter(CharacterLiteralMissingCharacter),
	CharacterLiteralMultipleCharacters(CharacterLiteralMultipleCharacters),
	CharacterLiteralNonEscapedNewline(CharacterLiteralNonEscapedNewline),
	CharacterLiteralMissingClosingQuote(CharacterLiteralMissingClosingQuote),
	StringLiteralMissingClosingQuote(StringLiteralMissingClosingQuote),
	CharacterEscapeUnexpectedCharacter(CharacterEscapeUnexpectedCharacter),
	CharacterEscapeMissingHexadecimalDigit(CharacterEscapeMissingHexadecimalDigit),
	CharacterEscapeMissingOpeningCurly(CharacterEscapeMissingOpeningCurly),
	CharacterEscapeMissingClosingCurly(CharacterEscapeMissingClosingCurly),
	CharacterEscapeInvalidDigit(CharacterEscapeInvalidDigit),
	CharacterEscapeInvalidUnicodeScalarValue(CharacterEscapeInvalidUnicodeScalarValue),
	CharacterEscapeMissingNumber(CharacterEscapeMissingNumber),
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
			CompilationError::CharacterLiteralMissingCharacter(error) => error.literal_span.clone(),
			CompilationError::CharacterLiteralMultipleCharacters(error) => error.literal_span.clone(),
			CompilationError::CharacterLiteralNonEscapedNewline(error) => {
				error.newline_pos.clone().one_char_span()
			},
			CompilationError::CharacterLiteralMissingClosingQuote(error) => {
				error.open_quote_pos.clone().one_char_span()
			},
			CompilationError::StringLiteralMissingClosingQuote(error) => {
				error.open_quote_pos.clone().one_char_span()
			},
			CompilationError::CharacterEscapeUnexpectedCharacter(error) => error
				.backslash_pos
				.span_to(&error.invalid_character_pos)
				.unwrap(),
			CompilationError::CharacterEscapeMissingHexadecimalDigit(error) => {
				match &error.missing_hexadecimal_pos {
					Some(pos) => error
						.backslash_x_and_maybe_first_digit_span
						.clone()
						.extend_to(pos),
					None => error.backslash_x_and_maybe_first_digit_span.clone(),
				}
			},
			CompilationError::CharacterEscapeMissingOpeningCurly(error) => {
				error.span_of_slash_and_letter.clone()
			},
			CompilationError::CharacterEscapeMissingClosingCurly(error) => {
				error.span_of_slash_letter_and_open_curly.clone()
			},
			CompilationError::CharacterEscapeInvalidDigit(error) => {
				error.invalid_digit_pos.clone().one_char_span()
			},
			CompilationError::CharacterEscapeInvalidUnicodeScalarValue(error) => {
				error.span_of_number.clone()
			},
			CompilationError::CharacterEscapeMissingNumber(error) => error.span.clone(),
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
			CompilationError::CharacterLiteralMissingCharacter(error) => format!(
				"character literal {} contains no character, it has to contain one",
				error.literal_span.as_str()
			),
			CompilationError::CharacterLiteralMultipleCharacters(error) => format!(
				"character literal {} contains {} charaters{}, it has to contain only one",
				error.literal_span.as_str(),
				error.character_spans.len(),
				if error.character_spans.len() <= 5 {
					// There are few characters, we can list them.
					let mut characters = " (".to_string();
					for (i, character_span) in error.character_spans.iter().enumerate() {
						characters.push('\'');
						characters.push_str(character_span.as_str());
						characters.push('\'');
						#[allow(clippy::comparison_chain)]
						if i + 2 == error.character_spans.len() {
							characters.push_str(" and ");
						} else if i + 2 < error.character_spans.len() {
							characters.push_str(", ");
						}
					}
					characters.push(')');
					characters
				} else {
					"".to_string()
				}
			),
			CompilationError::CharacterLiteralNonEscapedNewline(error) => {
				"non-escaped newline character inside a character literal".to_string()
			},
			CompilationError::CharacterLiteralMissingClosingQuote(error) => {
				"character literal started here is never closed by a matching single-quote".to_string()
			},
			CompilationError::StringLiteralMissingClosingQuote(error) => {
				"string literal started here is never closed by a matching double-quote".to_string()
			},
			CompilationError::CharacterEscapeUnexpectedCharacter(error) => format!(
				"unknown character escape that begins by \"{}\"",
				self.span().as_str()
			),
			CompilationError::CharacterEscapeMissingHexadecimalDigit(error) => {
				if error.one_digit_was_found {
					match &error.missing_hexadecimal_pos {
						Some(pos) => format!(
							"character escape \"{}\" must have a 2nd hex digit but \'{}\' is not a hex digit",
							self.span().as_str(),
							pos.as_char(),
						),
						None => format!(
							"character escape \"{}\" must have a 2nd hex digit but there is only one",
							self.span().as_str(),
						),
					}
				} else {
					match &error.missing_hexadecimal_pos {
						Some(pos) => format!(
							"character escape \"{}\" must have two hex digits but \'{}\' is not a hex digit",
							self.span().as_str(),
							pos.as_char(),
						),
						None => format!(
							"character escape \"{}\" must have two hex digits but there are none",
							self.span().as_str(),
						),
					}
				}
			},
			CompilationError::CharacterEscapeMissingOpeningCurly(error) => format!(
				"this character escape must have an open curly \'{{\' just after \"{}\"",
				error.span_of_slash_and_letter.as_str()
			),
			CompilationError::CharacterEscapeMissingClosingCurly(error) => {
				"this character escape must have an close curly \'}}\' after the number".to_string()
			},
			CompilationError::CharacterEscapeInvalidDigit(error) => format!(
				"encountered invalid {} digit before a close curly \'}}\' in character escape",
				match error.accepted_base {
					10 => "decimal",
					16 => "hexadecimal",
					_ => panic!(),
				}
			),
			CompilationError::CharacterEscapeInvalidUnicodeScalarValue(error) => match error.value {
				None => "this does not even fit in 8 bytes, it cannot possibly be a character code"
					.to_string(),
				Some(value) => {
					format!("the number {value} (0x{value:x}) is not a Unicode scalar value")
				},
			},
			CompilationError::CharacterEscapeMissingNumber(error) => format!(
				"character escape \"{}\" is missing a number in the \"{{}}\" block",
				error.span.as_str()
			),
		}
	}

	pub fn print(&self) {
		print_compilation_message(MessageKind::Error, self.span(), self.message());
	}
}

pub enum CompilationWarning {
	MissingTerminatingSemicolon { statement_span: Span },
	NewlineInStringLiteral { newline_pos: Pos },
}

/// IDEs such as VSCode can suggest to the user one (or multiple) "quick fix" solutions
/// to diagnostics (errors, warnings, etc). A quick fix can be a code edit.
/// This is a code edit that can be suggested by a warning.
pub struct FixByRewrite {
	pub description: String,
	pub new_code: String,
}

impl CompilationWarning {
	pub fn span(&self) -> Span {
		match self {
			CompilationWarning::MissingTerminatingSemicolon { statement_span } => {
				statement_span.clone()
			},
			CompilationWarning::NewlineInStringLiteral { newline_pos } => {
				newline_pos.clone().one_char_span()
			},
		}
	}

	pub fn message(&self) -> String {
		match self {
			CompilationWarning::MissingTerminatingSemicolon { statement_span } => {
				"missing terminating semicolon \';\' at the end of this statement".to_string()
			},
			CompilationWarning::NewlineInStringLiteral { .. } => {
				"non-escaped newline character inside a string literal".to_string()
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
			CompilationWarning::NewlineInStringLiteral { .. } => {
				// TODO: propose to replace the non-escaped newline by `\n`
				None
			},
		}
	}
}

impl HighProgram {
	/// Get the list of errors and warnings contained in this AST node.
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

impl HighStatement {
	/// Get the list of errors and warnings contained in this AST node.
	pub fn get_errors_and_warnings(&self) -> (Vec<CompilationError>, Vec<CompilationWarning>) {
		let mut errors = vec![];
		let mut warnings = vec![];
		#[allow(clippy::collapsible_match)]
		match self {
			HighStatement::Error { unexpected_characters, .. } => {
				for unexpected_character in unexpected_characters.iter() {
					errors.push(CompilationError::UnexpectedCharacter(
						unexpected_character.clone(),
					));
				}
			},
			HighStatement::Code { instructions, semicolon } => {
				fn character_escape_error_to_compilation_error(
					character_escape_error: CharacterEscapeError,
				) -> CompilationError {
					match character_escape_error {
						CharacterEscapeError::UnexpectedCharacter(error) => {
							CompilationError::CharacterEscapeUnexpectedCharacter(error)
						},
						CharacterEscapeError::MissingHexadecimalDigit(error) => {
							CompilationError::CharacterEscapeMissingHexadecimalDigit(error)
						},
						CharacterEscapeError::MissingOpeningCurly(error) => {
							CompilationError::CharacterEscapeMissingOpeningCurly(error)
						},
						CharacterEscapeError::MissingClosingCurly(error) => {
							CompilationError::CharacterEscapeMissingClosingCurly(error)
						},
						CharacterEscapeError::InvalidDigit(error) => {
							CompilationError::CharacterEscapeInvalidDigit(error)
						},
						CharacterEscapeError::InvalidUnicodeScalarValue(error) => {
							CompilationError::CharacterEscapeInvalidUnicodeScalarValue(error)
						},
						CharacterEscapeError::MissingNumber(error) => {
							CompilationError::CharacterEscapeMissingNumber(error)
						},
					}
				}
				let errors_len_before = errors.len();
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
						HighInstruction::CharacterLiteral(character_literal) => {
							if let CharacterLiteral { value: Err(character_literal_error), .. } =
								&character_literal
							{
								match character_literal_error {
									CharacterLiteralError::CharacterEscapeError(character_escape_error) => {
										errors.push(character_escape_error_to_compilation_error(
											character_escape_error.clone(),
										));
									},
									CharacterLiteralError::MissingCharacter(error) => {
										errors.push(CompilationError::CharacterLiteralMissingCharacter(
											error.clone(),
										));
									},
									CharacterLiteralError::MultipleCharacters(error) => {
										errors.push(CompilationError::CharacterLiteralMultipleCharacters(
											error.clone(),
										));
									},
									CharacterLiteralError::NonEscapedNewline(error) => {
										errors.push(CompilationError::CharacterLiteralNonEscapedNewline(
											error.clone(),
										));
									},
									CharacterLiteralError::MissingClosingQuote(error) => {
										errors.push(CompilationError::CharacterLiteralMissingClosingQuote(
											error.clone(),
										));
									},
								}
							}
						},
						HighInstruction::StringLiteral(string_literal) => {
							if let Err(string_literal_error) = &string_literal.value {
								match string_literal_error {
									StringLiteralError::CharacterEscapeError(character_escape_error) => {
										errors.push(character_escape_error_to_compilation_error(
											character_escape_error.clone(),
										));
									},
									StringLiteralError::MissingClosingQuote(error) => {
										errors.push(CompilationError::StringLiteralMissingClosingQuote(
											error.clone(),
										));
									},
								}
							} else {
								for pos in string_literal.span.iter_pos() {
									if pos.as_char() == '\n' {
										warnings.push(CompilationWarning::NewlineInStringLiteral {
											newline_pos: pos,
										});
									}
								}
							}
						},
						_ => {},
					}
				}
				if errors_len_before == errors.len() {
					// This statement did not emit errors, so maybe we care about this warning.
					if semicolon.is_none() {
						let statement_span = self.span();
						warnings.push(CompilationWarning::MissingTerminatingSemicolon { statement_span });
					}
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
			span
				.as_str()
				.replace('\n', &format!("{negative} {no_negative}")),
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
