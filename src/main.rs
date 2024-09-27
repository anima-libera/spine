#![allow(unused)]

use asm::{AsmInstr, Imm, Reg64};
use elf::{chmod_x, Binary};

mod asm;
mod elf;

#[cfg(test)]
mod asm_test;

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

fn main() {
	let program = SpineProgram {
		instrs: vec![
			SpineInstr::PushConst(SpineValue::I64(10)),
			SpineInstr::PushConst(SpineValue::I64(97)),
			SpineInstr::PopI64AndPrintAsChar,
			SpineInstr::PopI64AndPrintAsChar,
			SpineInstr::Exit,
		],
	};

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
						reg_dst: Reg64::Rdi, // Stdout file descriptor
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

	for byte in bin.code_segment_binary_machine_code() {
		print!("{byte:02x}");
	}
	println!();

	std::fs::write("binary", bin.to_binary()).unwrap();
	chmod_x("binary");
}
