use std::u64;

use asm::{BaseSize, Imm32, Imm64, Imm8, Raw32, Raw64, Raw8};

use crate::*;

#[test]
fn some_assembly_instructions() {
	let mut bin = Binary::new();

	let message = b"hewwo :3\n";
	let message_offset_in_data = bin.data_bytes.len();
	bin.data_bytes.extend(message);

	let value = b"nyaaa :3";
	let value_offset_in_data = bin.data_bytes.len();
	bin.data_bytes.extend(value);

	use AsmInstr::*;
	bin.asm_instrs = vec![
		// Kinda do *(uint8_t*)message = (-1)+(*(uint8_t*)value); so we sould see "mewwo :3"
		MovImmToReg64 {
			imm_src: Imm::Imm64(Imm64::DataAddr {
				offset_in_data_segment: value_offset_in_data as u64,
			}),
			reg_dst: Reg64::Rax,
		},
		MovImmToReg64 {
			imm_src: Imm::Imm64(Imm64::DataAddr {
				offset_in_data_segment: message_offset_in_data as u64,
			}),
			reg_dst: Reg64::Rbx,
		},
		MovImmToReg64 {
			imm_src: Imm::Imm64(Imm64::Raw(Raw64::Signed(-1))),
			reg_dst: Reg64::Rcx,
		},
		MovDerefReg64ToReg64 {
			src_size: BaseSize::Size8,
			reg_as_ptr_src: Reg64::Rax,
			reg_dst: Reg64::Rax,
		},
		AddReg64ToReg64 { reg_src: Reg64::Rcx, reg_dst: Reg64::Rax },
		MovReg64ToDerefReg64 {
			dst_size: BaseSize::Size8,
			reg_src: Reg64::Rax,
			reg_as_ptr_dst: Reg64::Rbx,
		},
		// Write(message) syscall
		MovImmToReg64 {
			imm_src: Imm::Imm64(Imm64::Raw(Raw64::Unsigned(1))),
			reg_dst: Reg64::Rax,
		},
		MovImmToReg64 {
			imm_src: Imm::Imm64(Imm64::Raw(Raw64::Unsigned(1))),
			reg_dst: Reg64::Rdi,
		},
		MovImmToReg64 {
			imm_src: Imm::Imm64(Imm64::DataAddr {
				offset_in_data_segment: message_offset_in_data as u64,
			}),
			reg_dst: Reg64::Rsi,
		},
		MovImmToReg64 {
			imm_src: Imm::Imm64(Imm64::Raw(Raw64::Unsigned(message.len() as u64))),
			reg_dst: Reg64::Rdx,
		},
		Syscall,
		// Exit(0) syscall
		MovImmToReg64 {
			imm_src: Imm::Imm64(Imm64::Raw(Raw64::Unsigned(60))),
			reg_dst: Reg64::Rax,
		},
		MovImmToReg64 {
			imm_src: Imm::Imm64(Imm64::Raw(Raw64::Unsigned(0))),
			reg_dst: Reg64::Rdi,
		},
		Syscall,
		//
		Label { name: "loop_xd".to_string() },
		// Write(message) syscall
		MovImmToReg64 {
			imm_src: Imm::Imm64(Imm64::Raw(Raw64::Unsigned(1))),
			reg_dst: Reg64::Rax,
		},
		MovImmToReg64 {
			imm_src: Imm::Imm64(Imm64::Raw(Raw64::Unsigned(1))),
			reg_dst: Reg64::Rdi,
		},
		MovImmToReg64 {
			imm_src: Imm::Imm64(Imm64::DataAddr {
				offset_in_data_segment: message_offset_in_data as u64,
			}),
			reg_dst: Reg64::Rsi,
		},
		MovImmToReg64 {
			imm_src: Imm::Imm64(Imm64::Raw(Raw64::Unsigned(message.len() as u64))),
			reg_dst: Reg64::Rdx,
		},
		Syscall,
		//
		JumpToLabel { label_name: "loop_xd".to_string() },
		// Exit(0) syscall
		MovImmToReg64 {
			imm_src: Imm::Imm64(Imm64::Raw(Raw64::Unsigned(60))),
			reg_dst: Reg64::Rax,
		},
		MovImmToReg64 {
			imm_src: Imm::Imm64(Imm64::Raw(Raw64::Unsigned(0))),
			reg_dst: Reg64::Rdi,
		},
		Syscall,
	];

	for byte in bin.code_segment_binary_machine_code() {
		print!("{byte:02x}");
	}
	println!();

	std::fs::create_dir("test_binaries");
	let dot_path = "./test_binaries/binary_some_assembly_instructions";
	std::fs::write(dot_path, bin.to_binary()).unwrap();
	chmod_x(dot_path);

	let binary_execution_result = std::process::Command::new(dot_path).output().unwrap();
	let binary_execution_output =
		std::str::from_utf8(binary_execution_result.stdout.as_slice()).unwrap();
	assert_eq!(binary_execution_output, "mewwo :3\n");
}

#[test]
fn mov_imm_to_reg64_all_variants() {
	let mut bin = Binary::new();

	let regs_to_test = [
		Reg64::Rax,
		Reg64::Rbx,
		Reg64::Rcx,
		Reg64::Rdx,
		Reg64::Rbp,
		Reg64::Rdi,
		Reg64::Rsi,
		Reg64::R8,
		Reg64::R9,
		Reg64::R10,
		Reg64::R11,
		Reg64::R12,
		Reg64::R13,
		Reg64::R14,
		Reg64::R15,
	];

	use AsmInstr::*;
	for reg in regs_to_test.iter().copied() {
		bin.asm_instrs.extend([
			// Use the 6 variants (the 6 kinds of raw imms)
			MovImmToReg64 { imm_src: Imm::Imm8(Imm8::Raw(Raw8::Signed(-5))), reg_dst: reg },
			PushReg64 { reg_src: reg },
			MovImmToReg64 { imm_src: Imm::Imm8(Imm8::Raw(Raw8::Unsigned(5))), reg_dst: reg },
			PushReg64 { reg_src: reg },
			MovImmToReg64 {
				imm_src: Imm::Imm32(Imm32::Raw(Raw32::Signed(-555555))),
				reg_dst: reg,
			},
			PushReg64 { reg_src: reg },
			MovImmToReg64 {
				imm_src: Imm::Imm32(Imm32::Raw(Raw32::Unsigned(555555))),
				reg_dst: reg,
			},
			PushReg64 { reg_src: reg },
			MovImmToReg64 {
				imm_src: Imm::Imm64(Imm64::Raw(Raw64::Signed(-555555555555))),
				reg_dst: reg,
			},
			PushReg64 { reg_src: reg },
			MovImmToReg64 {
				imm_src: Imm::Imm64(Imm64::Raw(Raw64::Unsigned(555555555555))),
				reg_dst: reg,
			},
			PushReg64 { reg_src: reg },
		]);
	}
	bin.asm_instrs.extend([
		// Write syscall
		MovImmToReg64 {
			imm_src: Imm::whatever_raw(1),
			reg_dst: Reg64::Rax, // Syscall number
		},
		MovImmToReg64 {
			imm_src: Imm::whatever_raw(2),
			reg_dst: Reg64::Rdi, // File descriptor
		},
		PushReg64 { reg_src: Reg64::Rsp },
		PopToReg64 { reg_dst: Reg64::Rsi }, // String address
		MovImmToReg64 {
			imm_src: Imm::unsigned_raw(6 * 8 * (regs_to_test.len() as u64)),
			reg_dst: Reg64::Rdx, // String length
		},
		Syscall,
		// Exit syscall
		MovImmToReg64 {
			imm_src: Imm::whatever_raw(60),
			reg_dst: Reg64::Rax, // Syscall number
		},
		MovImmToReg64 {
			imm_src: Imm::unsigned_raw(0),
			reg_dst: Reg64::Rdi, // Exit code, 0 means all good
		},
		Syscall,
	]);

	for byte in bin.code_segment_binary_machine_code() {
		print!("{byte:02x}");
	}
	println!();

	std::fs::create_dir("test_binaries");
	let dot_path = "./test_binaries/binary_mov_imm_to_reg64_all_variants";
	std::fs::write(dot_path, bin.to_binary()).unwrap();
	chmod_x(dot_path);

	let binary_execution_result = std::process::Command::new(dot_path).output().unwrap();
	let binary_execution_output = binary_execution_result.stderr.as_slice();

	let mut expected_output = vec![];
	for _ in 0..(regs_to_test.len()) {
		expected_output.extend((555555555555_u64).to_le_bytes());
		expected_output.extend((-555555555555_i64).to_le_bytes());
		expected_output.extend((555555_u64).to_le_bytes());
		expected_output.extend((-555555_i64).to_le_bytes());
		expected_output.extend((5_u64).to_le_bytes());
		expected_output.extend((-5_i64).to_le_bytes());
	}

	assert_eq!(binary_execution_output, expected_output);
}
