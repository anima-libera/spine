use asm::{BaseSize, Imm64, Raw64};

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
