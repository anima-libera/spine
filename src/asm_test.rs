use crate::asm::{AsmInstr, BaseSign, BaseSize, Reg64};
use crate::elf::{chmod_x, Binary};
use crate::imm::{Imm, Imm32, Imm64, Imm8, Raw32, Raw64, Raw8};

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
			src_sign: BaseSign::Unsigned,
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

	// We try all the `MovImmToReg64`s that we can think of.
	for reg in regs_to_test.iter().copied() {
		bin.asm_instrs.extend([
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

	// The results were all pushed on the stack,
	// now we extract them to be confronted to the expected results.
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

	let mut i = 0;
	for reg in regs_to_test.iter().rev() {
		println!("Testing register {reg:?}, 64-bits, unsigned");
		assert_eq!(
			binary_execution_output[i..(i + 8)],
			(555555555555_u64).to_le_bytes()
		);
		i += 8;
		println!("Testing register {reg:?}, 64-bits, signed");
		assert_eq!(
			binary_execution_output[i..(i + 8)],
			(-555555555555_i64).to_le_bytes()
		);
		i += 8;
		println!("Testing register {reg:?}, 32-bits, unsigned");
		assert_eq!(
			binary_execution_output[i..(i + 8)],
			(555555_u64).to_le_bytes()
		);
		i += 8;
		println!("Testing register {reg:?}, 32-bits, signed");
		assert_eq!(
			binary_execution_output[i..(i + 8)],
			(-555555_i64).to_le_bytes()
		);
		i += 8;
		println!("Testing register {reg:?}, 8-bits, unsigned");
		assert_eq!(binary_execution_output[i..(i + 8)], (5_u64).to_le_bytes());
		i += 8;
		println!("Testing register {reg:?}, 8-bits, signed");
		assert_eq!(binary_execution_output[i..(i + 8)], (-5_i64).to_le_bytes());
		i += 8;
	}
}

#[test]
fn mov_deref_reg_64_to_reg_64_all_variants() {
	let mut bin = Binary::new();

	let value = [0xfa, 0xf1, 0xfb, 0xf2, 0xfc, 0xf3, 0xfd, 0xf4];
	let value_offset_in_data = bin.data_bytes.len();
	bin.data_bytes.extend(value);

	let regs_to_test = [
		Reg64::Rax,
		Reg64::Rbx,
		//Reg64::Rcx,
		//Reg64::Rdx,
		////Reg64::Rbp,
		//Reg64::Rdi,
		//Reg64::Rsi,
		//Reg64::R8,
		//Reg64::R9,
		//Reg64::R10,
		//Reg64::R11,
		//Reg64::R12,
		//Reg64::R13,
		//Reg64::R14,
		//Reg64::R15,
	];

	use AsmInstr::*;

	// We try all the `MovDerefReg64ToReg64`s that we can think of.
	for src_reg in regs_to_test.iter().copied() {
		bin.asm_instrs.extend([MovImmToReg64 {
			imm_src: Imm::Imm64(Imm64::DataAddr {
				offset_in_data_segment: value_offset_in_data as u64,
			}),
			reg_dst: src_reg,
		}]);

		for dst_reg in regs_to_test.iter().copied() {
			if src_reg == dst_reg {
				continue;
			}

			bin.asm_instrs.extend([
				MovDerefReg64ToReg64 {
					src_size: BaseSize::Size8,
					src_sign: BaseSign::Signed,
					reg_as_ptr_src: src_reg,
					reg_dst: dst_reg,
				},
				PushReg64 { reg_src: dst_reg },
				MovDerefReg64ToReg64 {
					src_size: BaseSize::Size8,
					src_sign: BaseSign::Unsigned,
					reg_as_ptr_src: src_reg,
					reg_dst: dst_reg,
				},
				PushReg64 { reg_src: dst_reg },
				MovDerefReg64ToReg64 {
					src_size: BaseSize::Size32,
					src_sign: BaseSign::Signed,
					reg_as_ptr_src: src_reg,
					reg_dst: dst_reg,
				},
				PushReg64 { reg_src: dst_reg },
				MovDerefReg64ToReg64 {
					src_size: BaseSize::Size32,
					src_sign: BaseSign::Unsigned,
					reg_as_ptr_src: src_reg,
					reg_dst: dst_reg,
				},
				PushReg64 { reg_src: dst_reg },
				MovDerefReg64ToReg64 {
					src_size: BaseSize::Size64,
					src_sign: BaseSign::Signed,
					reg_as_ptr_src: src_reg,
					reg_dst: dst_reg,
				},
				PushReg64 { reg_src: dst_reg },
				MovDerefReg64ToReg64 {
					src_size: BaseSize::Size64,
					src_sign: BaseSign::Unsigned,
					reg_as_ptr_src: src_reg,
					reg_dst: dst_reg,
				},
				PushReg64 { reg_src: dst_reg },
			]);
		}
	}

	// The results were all pushed on the stack,
	// now we extract them to be confronted to the expected results.
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

	println!(
		"Value address: {:x}",
		bin.layout().data_segment_address + value_offset_in_data
	);

	std::fs::create_dir("test_binaries");
	let dot_path = "./test_binaries/binary_mov_deref_reg_64_to_reg_64_all_variants";
	std::fs::write(dot_path, bin.to_binary()).unwrap();
	chmod_x(dot_path);

	let binary_execution_result = std::process::Command::new(dot_path).output().unwrap();
	let binary_execution_output = binary_execution_result.stderr.as_slice();

	let mut i = 0;
	for src_reg in regs_to_test.iter().copied().rev() {
		for dst_reg in regs_to_test.iter().copied().rev() {
			if src_reg == dst_reg {
				continue;
			}

			println!("Testing *{src_reg:?} -> {dst_reg:?}, 64-bits, unsigned");
			assert_eq!(
				binary_execution_output[i..(i + 8)],
				u64::from_le_bytes(value[0..8].try_into().unwrap()).to_le_bytes()
			);
			i += 8;
			println!("Testing *{src_reg:?} -> {dst_reg:?}, 64-bits, signed");
			assert_eq!(
				binary_execution_output[i..(i + 8)],
				i64::from_le_bytes(value[0..8].try_into().unwrap()).to_le_bytes()
			);
			i += 8;
			println!("Testing *{src_reg:?} -> {dst_reg:?}, 32-bits, unsigned");
			assert_eq!(
				binary_execution_output[i..(i + 8)],
				(u32::from_le_bytes(value[0..4].try_into().unwrap()) as u64).to_le_bytes()
			);
			i += 8;
			println!("Testing *{src_reg:?} -> {dst_reg:?}, 32-bits, signed");
			assert_eq!(
				binary_execution_output[i..(i + 8)],
				(i32::from_le_bytes(value[0..4].try_into().unwrap()) as i64).to_le_bytes()
			);
			i += 8;
			println!("Testing *{src_reg:?} -> {dst_reg:?}, 8-bits, unsigned");
			assert_eq!(
				binary_execution_output[i..(i + 8)],
				(u8::from_le_bytes(value[0..1].try_into().unwrap()) as u64).to_le_bytes()
			);
			i += 8;
			println!("Testing *{src_reg:?} -> {dst_reg:?}, 8-bits, signed");
			assert_eq!(
				binary_execution_output[i..(i + 8)],
				(i8::from_le_bytes(value[0..1].try_into().unwrap()) as i64).to_le_bytes()
			);
			i += 8;
		}
	}
}
