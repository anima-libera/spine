#![allow(unused)]

mod asm;
mod elf;
mod imm;

#[cfg(test)]
mod asm_test;

use core::str;
use std::{collections::VecDeque, rc::Rc};

use asm::{AsmInstr, Reg64};
use elf::{chmod_x, Binary};
use imm::Imm;

enum SpineType {
	I64,
}

enum SpineValue {
	I64(i64),
}

enum SpineInstr {
	PushConst(SpineValue),
	PopI64AndPrintAsChar,
	Exit,
}

struct SpineProgram {
	instrs: Vec<SpineInstr>,
}

/// Used as `Rc<Self>`.
struct SourceCode {
	text: String,
	name: String,
}

struct SourceCodeReader {
	source: Rc<SourceCode>,
	next_index: usize,
	popped_characters_count: usize,
}

impl SourceCodeReader {
	fn new(source: Rc<SourceCode>) -> SourceCodeReader {
		SourceCodeReader { source, next_index: 0, popped_characters_count: 0 }
	}

	fn previous_character_pos(&self) -> Option<usize> {
		self.popped_characters_count.checked_sub(1)
	}

	fn next_character_pos(&self) -> Option<usize> {
		(self.next_index < self.source.text.len()).then_some(self.popped_characters_count)
	}

	fn passed_span(&self, pos_start: usize, pos_end: usize) -> SourceCodeSpan {
		if pos_end < pos_start {
			panic!("Span cannot end before it starts");
		}
		if self.next_index <= pos_end {
			panic!("Span cannot end after last popped/skipped character");
		}
		SourceCodeSpan { source: Rc::clone(&self.source), pos_start, pos_end }
	}

	fn peek_character(&self) -> Option<char> {
		self.source.text[self.next_index..].chars().next()
	}

	fn pop_character(&mut self) -> Option<char> {
		let character = self.peek_character();
		if let Some(character) = character {
			self.next_index += character.len_utf8();
			self.popped_characters_count += 1;
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

struct SourceCodeSpan {
	source: Rc<SourceCode>,
	/// Included.
	pos_start: usize,
	/// Included.
	pos_end: usize,
}

impl SourceCodeSpan {
	fn as_str(&self) -> &str {
		&self.source.text[self.pos_start..=self.pos_end]
	}
}

struct TokenIntegerLiteral {
	span: SourceCodeSpan,
	value_i64: Option<i64>,
}

impl TokenIntegerLiteral {
	fn as_i64(&self) -> Option<i64> {
		self.span.as_str().parse().ok()
	}
}

enum ExplicitKeyword {
	PrintChar,
	Exit,
}

struct TokenExplicitKeyword {
	span: SourceCodeSpan,
	keyword: Option<ExplicitKeyword>,
}

impl TokenExplicitKeyword {
	fn as_i64(&self) -> Option<i64> {
		self.span.as_str().parse().ok()
	}
}

enum Token {
	IntegerLiteral(TokenIntegerLiteral),
	ExplicitKeyword(TokenExplicitKeyword),
}

fn pop_token_from_reader(reader: &mut SourceCodeReader) -> Option<Token> {
	reader.skip_whitespace();
	let first_character = reader.peek_character();
	let pos_first_character = reader.next_character_pos();
	match first_character {
		Some('0'..='9') => {
			reader.skip_characters_while(|c| c.is_ascii_digit());
			let span = reader.passed_span(
				pos_first_character.unwrap(),
				reader.previous_character_pos().unwrap(),
			);
			let value_i64 = span.as_str().parse().ok();
			let token = Token::IntegerLiteral(TokenIntegerLiteral { span, value_i64 });
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
				"`exit" => Some(ExplicitKeyword::Exit),
				_ => None,
			};
			let token = Token::ExplicitKeyword(TokenExplicitKeyword { span, keyword });
			Some(token)
		},
		Some(_) => None,
		None => None,
	}
}

struct Tokenizer {
	reader: SourceCodeReader,
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
			pop_token_from_reader(&mut self.reader)
		}
	}

	fn peek_ith_token(&mut self, index: usize) -> Option<&Token> {
		while self.queue.len() <= index {
			let token = pop_token_from_reader(&mut self.reader)?;
			self.queue.push_back(token);
		}
		Some(&self.queue[index])
	}

	fn peek_token(&mut self) -> Option<&Token> {
		self.peek_ith_token(0)
	}
}

fn parse(source: Rc<SourceCode>) -> SpineProgram {
	let reader = SourceCodeReader::new(source);
	let mut tokenizer = Tokenizer::new(reader);

	let mut instrs = vec![];
	while tokenizer.peek_token().is_some() {
		match tokenizer.pop_token().unwrap() {
			Token::IntegerLiteral(TokenIntegerLiteral { span, value_i64 }) => {
				instrs.push(SpineInstr::PushConst(SpineValue::I64(value_i64.unwrap())));
			},
			Token::ExplicitKeyword(TokenExplicitKeyword { span, keyword }) => match keyword.unwrap() {
				ExplicitKeyword::PrintChar => instrs.push(SpineInstr::PopI64AndPrintAsChar),
				ExplicitKeyword::Exit => instrs.push(SpineInstr::Exit),
			},
		}
	}
	SpineProgram { instrs }
}

fn compile_to_binary(program: SpineProgram) -> Binary {
	let mut bin = Binary::new();

	use AsmInstr::*;

	for instr in program.instrs.iter() {
		match instr {
			SpineInstr::PushConst(SpineValue::I64(value)) => {
				bin.asm_instrs.extend([
					MovImmToReg64 { imm_src: Imm::whatever_raw(*value), reg_dst: Reg64::Rax },
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

	bin
}

fn main() {
	let source_code_text = r"10 97 `printchar `printchar `exit";
	let source_code =
		Rc::new(SourceCode { text: source_code_text.to_string(), name: "test uwu".to_string() });
	let program = parse(source_code);
	let bin = compile_to_binary(program);

	for byte in bin.code_segment_binary_machine_code() {
		print!("{byte:02x}");
	}
	println!();

	std::fs::write("binary", bin.to_binary()).unwrap();
	chmod_x("binary");
}
