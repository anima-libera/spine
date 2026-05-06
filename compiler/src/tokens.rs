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
	keywords::KeywordWhich,
	src::{Pos, Span},
};

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

pub(crate) const MAX_SUPPORTED_RADIX_NUMBER: u32 = 36;

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
	pub(crate) fn radix_number(&self) -> Option<u32> {
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
	pub span: Span,
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
	InvalidUnicodeScalarValue(CharacterEscapeInvalidUnicodeScalarValue),
	MissingNumber(CharacterEscapeMissingNumber),
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

#[derive(Debug)]
pub struct Keyword {
	pub(crate) span: Span,
	/// If true it was something like `kwexit`, if false it was like `exit`.
	pub kw_prefix: bool,
	pub keyword: Option<KeywordWhich>,
}

#[derive(Debug, Clone)]
pub struct Identifier {
	pub span: Span,
	pub(crate) name: String,
}

#[derive(Debug)]
pub struct Comment {
	pub span: Span,
	pub is_block: bool,
	pub is_doc: bool,
	pub is_missing_expected_closing_curly: bool,
}

#[derive(Debug)]
pub enum Token {
	IntegerLiteral(IntegerLiteral),
	CharacterLiteral(CharacterLiteral),
	StringLiteral(StringLiteral),
	Keyword(Keyword),
	Identifier(Identifier),
	Semicolon(Pos),
	CurlyOpen(Pos),
	CurlyClose(Pos),
	Comment(Comment),
	Whitespace(Span),
	UnexpectedCharacter(UnexpectedCharacter),
}

impl Token {
	pub fn span(&self) -> Span {
		match self {
			Token::IntegerLiteral(t) => t.span.clone(),
			Token::CharacterLiteral(t) => t.span.clone(),
			Token::StringLiteral(t) => t.span.clone(),
			Token::Keyword(t) => t.span.clone(),
			Token::Identifier(t) => t.span.clone(),
			Token::Semicolon(pos) => pos.clone().one_char_span(),
			Token::CurlyOpen(pos) => pos.clone().one_char_span(),
			Token::CurlyClose(pos) => pos.clone().one_char_span(),
			Token::Comment(t) => t.span.clone(),
			Token::Whitespace(span) => span.clone(),
			Token::UnexpectedCharacter(t) => t.pos.clone().one_char_span(),
		}
	}
}
