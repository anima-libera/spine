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

enum ExplicitKeyword {
	/// Pops an i64 and prints the character it represents as a unicode code point.
	PrintChar,
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
	ExplicitKeyword(TokenExplicitKeyword),
	Semicolon(SourceCodeSpan),
	Comment(TokenComment),
}

/// Consumes and tokenizes the next token.
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
}

enum SpineValue {
	I64(i64),
}

impl SpineValue {
	fn get_type(&self) -> SpineType {
		match self {
			SpineValue::I64(_) => SpineType::I64,
		}
	}
}

enum SpineInstr {
	PushConst(SpineValue),
	PopI64AndPrintAsChar,
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
			SpineInstr::PopI64AndPrintAsChar => (vec![SpineType::I64], vec![]),
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

struct SpineProgram {
	statements: Vec<SpineStatement>,
}

fn parse(source: Rc<SourceCode>) -> SpineProgram {
	let reader = SourceCodeReader::new(source);
	let mut tokenizer = Tokenizer::new(reader);

	let mut statements = vec![];
	while tokenizer.peek_token().is_some() {
		let mut src_order_instrs = vec![];
		loop {
			match tokenizer.pop_token() {
				Some(Token::IntegerLiteral(TokenIntegerLiteral { span, value_i64 })) => {
					src_order_instrs.push(SpineInstr::PushConst(SpineValue::I64(value_i64.unwrap())));
				},
				Some(Token::ExplicitKeyword(TokenExplicitKeyword { span, keyword })) => {
					match keyword.unwrap() {
						ExplicitKeyword::PrintChar => {
							src_order_instrs.push(SpineInstr::PopI64AndPrintAsChar);
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

fn compile_to_binary(program: SpineProgram) -> Binary {
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

fn main() {
	let mut source_file_path = None;
	let mut raw_source = None;
	let mut output_file_path = "binary".to_string();
	let mut verbose = false;
	let mut help = false;

	let args: Vec<_> = std::env::args().collect();
	if let Some(source_file_option_index) = args
		.iter()
		.position(|arg| arg == "-f" || arg == "--source-file")
	{
		source_file_path = Some(args[source_file_option_index + 1].clone());
	}
	if let Some(source_raw_option_index) = args
		.iter()
		.position(|arg| arg == "-r" || arg == "--raw-source")
	{
		raw_source = Some(args[source_raw_option_index + 1].clone());
	}
	if let Some(output_file_option_index) = args
		.iter()
		.position(|arg| arg == "-o" || arg == "--output-file")
	{
		output_file_path = args[output_file_option_index + 1].clone();
	}
	if args.iter().any(|arg| arg == "-v" || arg == "--verbose") {
		verbose = true;
	}
	if args.iter().any(|arg| arg == "-h" || arg == "--help") {
		help = true;
	}

	if help {
		println!("Options:");
		println!("  -f --source-file   Path to the source file to compile.");
		println!("  -r --raw-source    Source code to compile.");
		println!("  -o --output-file   Path to the binary to be produced.");
		println!("  -v --verbose       (flag) Compiler will print more stuff.");
		println!("  -h --help          (flag) Print this help message.");
		return;
	}

	if source_file_path.is_some() && raw_source.is_some() {
		panic!("Got both a source file (-f) and raw source (-r), need at most one of them");
	}
	let source_code = if let Some(source_file_path) = source_file_path {
		if verbose {
			println!("Reading source file \"{source_file_path}\"");
		}
		Rc::new(SourceCode {
			text: std::fs::read_to_string(&source_file_path).unwrap(),
			name: source_file_path.clone(),
		})
	} else if let Some(raw_source) = raw_source {
		if verbose {
			println!("Reading raw source from command line arguments");
		}
		Rc::new(SourceCode { text: raw_source.clone(), name: "<raw source>".to_string() })
	} else {
		panic!("No source code provided")
	};

	if verbose {
		println!("Compiling to intermediate representation");
	}
	let program = parse(source_code);
	if verbose {
		println!("Compiling to machine code");
	}
	let bin = compile_to_binary(program);

	if verbose {
		println!("Machine code:");
		for byte in bin.code_segment_binary_machine_code() {
			print!("{byte:02x}");
		}
		println!();
	}

	if verbose {
		println!("Writing compiled binary to file \"{output_file_path}\"");
	}
	std::fs::write(&output_file_path, bin.to_binary()).unwrap();
	chmod_x(&output_file_path);
}
