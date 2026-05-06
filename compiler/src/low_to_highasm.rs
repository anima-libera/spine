use core::str;
use std::collections::{HashMap, VecDeque};
use std::fmt::Debug;
use std::path::Path;
use std::sync::Arc;

use crate::elf::HighAsmBinaryPlan;
use crate::err::{
	ArbitraryRadixMissingRadixNumber, ArbitraryRadixNumberInvalidDigit,
	ArbitraryRadixNumberTooBigUnsupported, ArbitraryRadixNumberTooSmall,
	ArbitraryRadixPrefixMissingClosingCurly, ArbitraryRadixPrefixMissingOpeningCurly,
	CharacterEscapeInvalidDigit, CharacterEscapeInvalidUnicodeScalarValue,
	CharacterEscapeMissingClosingCurly, CharacterEscapeMissingHexadecimalDigit,
	CharacterEscapeMissingNumber, CharacterEscapeMissingOpeningCurly,
	CharacterEscapeUnexpectedCharacter, CharacterLiteralMissingCharacter,
	CharacterLiteralMissingClosingQuote, CharacterLiteralMultipleCharacters,
	CharacterLiteralNonEscapedNewline, IntegerLiteralValueInvalidDigit, IntegerLiteralValueMissing,
	IntegerLiteralValueOutOfRange, StringLiteralMissingClosingQuote, UnexpectedCharacter,
	UnknownRadixPrefixLetter,
};
use crate::high::{HighInstruction, HighProgram, HighScopeStack, HighStatement, WipDef};
use crate::high_to_low::SpineValue;
use crate::highasm::{HighAsmInstr, Reg64};
use crate::imm::{ImmRich, ImmRich64};
use crate::keywords::{DEFAULT_KEYWORDS, KeywordWhich};
use crate::low::{LowInstr, LowProgram, LowStatement};
use crate::parse_to_high::{CharacterLiteral, IntegerLiteral, Keyword, StringLiteral};
use crate::src::{Pos, Reader, SourceCode, Span};

pub fn low_to_binary_plan(program: &LowProgram) -> HighAsmBinaryPlan {
	let mut bin = HighAsmBinaryPlan::new();

	use HighAsmInstr::*;

	for statement in program.statements.iter() {
		match statement {
			LowStatement::Code { instrs } => {
				for instr in instrs.iter() {
					match instr {
						LowInstr::PushConst(SpineValue::I64(value)) => {
							bin.high_asm_instrs.extend([
								MovImmToReg64 {
									imm_src: ImmRich::whatever_value(*value),
									reg_dst: Reg64::Rax,
								},
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
							bin.high_asm_instrs.extend([
								MovImmToReg64 {
									imm_src: ImmRich::Imm64(ImmRich64::DataAddr { offset_in_data_segment }),
									reg_dst: Reg64::Rax,
								},
								PushReg64 { reg_src: Reg64::Rax },
								MovImmToReg64 {
									imm_src: ImmRich::whatever_value(string_len_in_bytes),
									reg_dst: Reg64::Rax,
								},
								PushReg64 { reg_src: Reg64::Rax },
							]);
						},
						LowInstr::PopI64AndPrintAsChar => {
							bin.high_asm_instrs.extend([
								// Write(message) syscall
								MovImmToReg64 {
									imm_src: ImmRich::whatever_value(1),
									reg_dst: Reg64::Rax, // Syscall number
								},
								MovImmToReg64 {
									imm_src: ImmRich::whatever_value(1),
									reg_dst: Reg64::Rdi, // File descriptor
								},
								PushReg64 { reg_src: Reg64::Rsp },
								PopToReg64 { reg_dst: Reg64::Rsi }, // String address
								MovImmToReg64 {
									imm_src: ImmRich::whatever_value(1),
									reg_dst: Reg64::Rdx, // String length
								},
								Syscall,
								// Pop
								PopToReg64 { reg_dst: Reg64::Rsi },
							]);
						},
						LowInstr::PopI64AndPtrAndPrintAsString => {
							bin.high_asm_instrs.extend([
								// Write(message) syscall
								MovImmToReg64 {
									imm_src: ImmRich::whatever_value(1),
									reg_dst: Reg64::Rax, // Syscall number
								},
								MovImmToReg64 {
									imm_src: ImmRich::whatever_value(1),
									reg_dst: Reg64::Rdi, // File descriptor
								},
								PopToReg64 { reg_dst: Reg64::Rdx }, // String length
								PopToReg64 { reg_dst: Reg64::Rsi }, // String address
								Syscall,
							]);
						},
						LowInstr::AddI64AndI64 => {
							bin.high_asm_instrs.extend([
								PopToReg64 { reg_dst: Reg64::Rax },
								PopToReg64 { reg_dst: Reg64::Rbx },
								AddReg64ToReg64 { reg_src: Reg64::Rbx, reg_dst: Reg64::Rax },
								PushReg64 { reg_src: Reg64::Rax },
							]);
						},
						LowInstr::Exit => {
							bin.high_asm_instrs.extend([
								// Exit(0) syscall
								MovImmToReg64 {
									imm_src: ImmRich::whatever_value(60),
									reg_dst: Reg64::Rax, // Syscall number
								},
								MovImmToReg64 {
									imm_src: ImmRich::whatever_value(0),
									reg_dst: Reg64::Rdi, // Exit code, 0 means all good
								},
								Syscall,
							]);
						},
						LowInstr::PopI64AndDiscard => {
							bin.high_asm_instrs.extend([
								// Pop
								PopToReg64 { reg_dst: Reg64::Rax },
							]);
						},
						LowInstr::NopZeroBytes => {},
						LowInstr::Syscall => {
							bin.high_asm_instrs.extend([
								// Parameters are in this order: RDI, RSI, RDX, R10, R8, R9.
								PopToReg64 { reg_dst: Reg64::R9 }, // Last argument
								PopToReg64 { reg_dst: Reg64::R8 },
								PopToReg64 { reg_dst: Reg64::R10 },
								PopToReg64 { reg_dst: Reg64::Rdx },
								PopToReg64 { reg_dst: Reg64::Rsi },
								PopToReg64 { reg_dst: Reg64::Rdi }, // First argument
								PopToReg64 { reg_dst: Reg64::Rax }, // Syscall number
								Syscall,
								// Syscall result
								PushReg64 { reg_src: Reg64::Rax },
								// Syscall second result, only used by the pipe syscall on some architectures,
								// see linux syscall documentation.
								PushReg64 { reg_src: Reg64::Rdx },
							]);
						},
						LowInstr::Illegal => {
							bin.high_asm_instrs.extend([
								// UD2
								Illegal,
							]);
						},
					}
				}
			},
		}
	}

	bin
}
