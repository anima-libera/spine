use core::str;
use std::{collections::VecDeque, rc::Rc};

use crate::asm::{AsmInstr, Reg64};
use crate::elf::Binary;
use crate::imm::{Imm, Imm64};

/// Used as `Rc<Self>`.
pub(crate) struct SourceCode {
	pub(crate) text: String,
	pub(crate) name: String,
}

struct SourceCodeReader {
	source: Rc<SourceCode>,
	next_char_pos: CharacterPos,
	previous_char_pos: Option<CharacterPos>,
}

impl SourceCodeReader {
	fn new(source: Rc<SourceCode>) -> SourceCodeReader {
		SourceCodeReader {
			source,
			next_char_pos: CharacterPos { index_in_bytes: 0, index_in_chars: 0 },
			previous_char_pos: None,
		}
	}

	fn previous_character_pos(&self) -> Option<CharacterPos> {
		self.previous_char_pos
	}

	fn next_character_pos(&self) -> Option<CharacterPos> {
		(self.next_char_pos.index_in_bytes < self.source.text.len()).then_some(self.next_char_pos)
	}

	fn passed_span(&self, pos_start: CharacterPos, pos_end: CharacterPos) -> SourceCodeSpan {
		if pos_end.index_in_chars < pos_start.index_in_chars {
			panic!("Span cannot end before it starts");
		}
		if self.next_char_pos.index_in_chars <= pos_end.index_in_chars {
			panic!("Span cannot end after last popped/skipped character");
		}
		SourceCodeSpan { source: Rc::clone(&self.source), pos_start, pos_end }
	}

	fn peek_character(&self) -> Option<char> {
		self.source.text[self.next_char_pos.index_in_bytes..]
			.chars()
			.next()
	}

	fn pop_character(&mut self) -> Option<char> {
		let character = self.peek_character();
		if let Some(character) = character {
			self.previous_char_pos = Some(self.next_char_pos);
			self.next_char_pos.index_in_bytes += character.len_utf8();
			self.next_char_pos.index_in_chars += 1;
		}
		character
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

#[derive(Clone, Copy)]
struct CharacterPos {
	index_in_bytes: usize,
	index_in_chars: usize,
}

struct SourceCodeSpan {
	source: Rc<SourceCode>,
	/// Included.
	pos_start: CharacterPos,
	/// Included.
	pos_end: CharacterPos,
}

impl SourceCodeSpan {
	fn as_str(&self) -> &str {
		&self.source.text[self.pos_start.index_in_bytes..=self.pos_end.index_in_bytes]
	}
}

struct TokenIntegerLiteral {
	span: SourceCodeSpan,
	value_i64: i64,
}

struct TokenCharacterLiteral {
	span: SourceCodeSpan,
	character: char,
}

struct TokenStringLiteral {
	span: SourceCodeSpan,
	string: String,
}

enum ExplicitKeyword {
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

struct TokenExplicitKeyword {
	span: SourceCodeSpan,
	keyword: Option<ExplicitKeyword>,
}

struct TokenComment {
	span: SourceCodeSpan,
	is_block: bool,
	is_doc: bool,
}

enum Token {
	IntegerLiteral(TokenIntegerLiteral),
	CharacterLiteral(TokenCharacterLiteral),
	StringLiteral(TokenStringLiteral),
	ExplicitKeyword(TokenExplicitKeyword),
	Semicolon(SourceCodeSpan),
	Comment(TokenComment),
}

/// Consumes the source code representation of an escaped character,
/// assuming we are in a string or character literal, and that we just popped a `\`.
fn pop_escaped_character_from_reader(reader: &mut SourceCodeReader) -> char {
	let hex_digit_to_value = |hex_digit| match hex_digit {
		'0'..='9' => hex_digit as u32 - '0' as u32,
		'a'..='f' => hex_digit as u32 - 'a' as u32 + 10,
		'A'..='F' => hex_digit as u32 - 'A' as u32 + 10,
		_ => panic!(),
	};
	match reader.pop_character().unwrap() {
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
	}
}

/// Consumes and tokenizes the next token.
fn pop_token_from_reader(reader: &mut SourceCodeReader) -> Option<Token> {
	reader.skip_whitespace();
	let first_character = reader.peek_character();
	let pos_first_character = reader.next_character_pos();
	match first_character {
		Some('0'..='9') => {
			let (radix, pos_first_character_after_radix_prefix) =
				if reader.peek_character() == Some('0') {
					reader.skip_character();
					let maybe_radix_character = reader.peek_character();
					if maybe_radix_character.is_none_or(|c| !c.is_ascii_alphanumeric()) {
						// Not a radix prefix.
						(10, None)
					} else {
						reader.skip_character();
						match maybe_radix_character.unwrap() {
							'x' | 'X' => (16, Some(reader.next_character_pos().unwrap())),
							'b' | 'B' => (2, Some(reader.next_character_pos().unwrap())),
							'r' | 'R' => {
								assert_eq!(reader.pop_character(), Some('{'));
								let pos_radix_number_start = reader.next_character_pos().unwrap();
								reader.skip_characters_while(|c| c.is_ascii_digit());
								let pos_radix_number_end = reader.previous_character_pos().unwrap();
								assert_eq!(reader.pop_character(), Some('}'));
								let pos_first_character_after_radix_prefix =
									reader.next_character_pos().unwrap();
								let radix_number_span =
									reader.passed_span(pos_radix_number_start, pos_radix_number_end);
								let radix_number = radix_number_span.as_str().parse().unwrap();
								(radix_number, Some(pos_first_character_after_radix_prefix))
							},
							unknown => panic!("unknown radix prefix char {unknown}"),
						}
					}
				} else {
					(10, None)
				};
			if 16 < radix {
				unimplemented!(); // yet
			}
			reader.skip_characters_while(|c| c.is_ascii_hexdigit());
			let span_without_radix_prefix = reader.passed_span(
				pos_first_character_after_radix_prefix.unwrap_or(pos_first_character.unwrap()),
				reader.previous_character_pos().unwrap(),
			);
			let value_i64 = i64::from_str_radix(span_without_radix_prefix.as_str(), radix).unwrap();
			let span = reader.passed_span(
				pos_first_character.unwrap(),
				reader.previous_character_pos().unwrap(),
			);
			let token = Token::IntegerLiteral(TokenIntegerLiteral { span, value_i64 });
			Some(token)
		},
		Some('\'') => {
			reader.skip_character();
			let character = if reader.peek_character() == Some('\\') {
				reader.skip_character();
				pop_escaped_character_from_reader(reader)
			} else {
				reader.pop_character().unwrap()
			};
			assert_eq!(reader.pop_character(), Some('\''));
			let span = reader.passed_span(
				pos_first_character.unwrap(),
				reader.previous_character_pos().unwrap(),
			);
			let token = Token::CharacterLiteral(TokenCharacterLiteral { span, character });
			Some(token)
		},
		Some('\"') => {
			reader.skip_character();
			let mut string = String::new();
			loop {
				if reader.peek_character() == Some('\"') {
					reader.skip_character();
					break;
				} else if reader.peek_character() == Some('\\') {
					reader.skip_character();
					string.push(pop_escaped_character_from_reader(reader));
				} else {
					string.push(reader.pop_character().unwrap());
				};
			}
			let span = reader.passed_span(
				pos_first_character.unwrap(),
				reader.previous_character_pos().unwrap(),
			);
			let token = Token::StringLiteral(TokenStringLiteral { span, string });
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
				"`printchar" => Some(ExplicitKeyword::PrintChar),
				"`printstr" => Some(ExplicitKeyword::PrintStr),
				"`add" => Some(ExplicitKeyword::Add),
				"`exit" => Some(ExplicitKeyword::Exit),
				_ => None,
			};
			let token = Token::ExplicitKeyword(TokenExplicitKeyword { span, keyword });
			Some(token)
		},
		Some(';') => {
			reader.skip_character();
			let span = reader.passed_span(pos_first_character.unwrap(), pos_first_character.unwrap());
			Some(Token::Semicolon(span))
		},
		Some('-') => {
			reader.skip_character();
			assert_eq!(reader.peek_character(), Some('-'));
			reader.skip_character();
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
			let token = Token::Comment(TokenComment { span, is_block, is_doc });
			Some(token)
		},
		Some(_) => None,
		None => None,
	}
}

fn pop_token_from_reader_ignoring_comments(reader: &mut SourceCodeReader) -> Option<Token> {
	loop {
		match pop_token_from_reader(reader) {
			Some(Token::Comment(_)) => continue,
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

#[derive(Debug, PartialEq, Eq)]
enum SpineType {
	I64,
	DataAddr,
}

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

enum SpineStatement {
	Code {
		/// In the order that they are executed, so the reverse of the order in the source code.
		instrs: Vec<SpineInstr>,
	},
}

pub(crate) struct SpineProgram {
	statements: Vec<SpineStatement>,
}

pub(crate) fn parse(source: Rc<SourceCode>) -> SpineProgram {
	let reader = SourceCodeReader::new(source);
	let mut tokenizer = Tokenizer::new(reader);

	let mut statements = vec![];
	while tokenizer.peek_token().is_some() {
		let mut src_order_instrs = vec![];
		loop {
			match tokenizer.pop_token() {
				Some(Token::IntegerLiteral(TokenIntegerLiteral { span, value_i64 })) => {
					src_order_instrs.push(SpineInstr::PushConst(SpineValue::I64(value_i64)));
				},
				Some(Token::CharacterLiteral(TokenCharacterLiteral { span, character })) => {
					src_order_instrs.push(SpineInstr::PushConst(SpineValue::I64(character as i64)));
				},
				Some(Token::StringLiteral(TokenStringLiteral { span, string })) => {
					src_order_instrs.push(SpineInstr::PushString(string));
				},
				Some(Token::ExplicitKeyword(TokenExplicitKeyword { span, keyword })) => {
					match keyword.unwrap() {
						ExplicitKeyword::PrintChar => {
							src_order_instrs.push(SpineInstr::PopI64AndPrintAsChar);
						},
						ExplicitKeyword::PrintStr => {
							src_order_instrs.push(SpineInstr::PopI64AndPtrAndPrintAsString);
						},
						ExplicitKeyword::Add => {
							src_order_instrs.push(SpineInstr::AddI64AndI64);
						},
						ExplicitKeyword::Exit => {
							src_order_instrs.push(SpineInstr::Exit);
						},
					}
				},
				Some(Token::Comment(_)) => {},
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
