use crate::{
	asm::small_uints::{Bit, U2, U3, U4},
	elf::Layout,
	imm::Imm,
};

pub(crate) mod small_uints {
	//! Small unsigned integers on a few bits, like `U3` or `Bit`.
	//!
	//! These are not just aliases of `u8` because I want type safety on these,
	//! the backend cooks binary soup with these a lot and I want all the checks I can get.

	macro_rules! def {
		($type_name:ident, $size_in_bits:literal) => {
			#[derive(Debug, Clone, Copy, PartialEq, Eq)]
			pub(crate) struct $type_name(u8);

			impl $type_name {
				pub(crate) const fn new(value: u8) -> Self {
					assert!(value <= (1 << $size_in_bits));
					Self(value)
				}

				pub(crate) fn as_u8(self) -> u8 {
					self.0
				}
			}

			impl std::fmt::Display for $type_name {
				fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
					write!(f, "{}", self.0)
				}
			}
		};
	}

	def! {Bit, 1}
	def! {U2, 2}
	def! {U3, 3}
	def! {U4, 4}

	impl Bit {
		pub(crate) const _0: Bit = Bit::new(0);
		pub(crate) const _1: Bit = Bit::new(1);
	}
}

fn set_byte_bit(byte: &mut u8, bit_index: usize, bit_value: Bit) {
	*byte |= bit_value.as_u8() << bit_index;
}

fn byte_from_bits(bits: &[Bit; 8]) -> u8 {
	let mut byte = 0;
	for (i, bit) in bits.iter().copied().rev().enumerate() {
		set_byte_bit(&mut byte, i, bit);
	}
	byte
}

/// Okay, the REX prefix. It is optional, one byte, and comes just before the opcode bytes.
///
/// Its format is `0100wrxb` (from high to low), where:
/// - `w`: 1 means that the instruction uses 64-bits operands, 0 means it uses some default size,
/// - `r` is an extra high bit that expands ModR/M.reg from 3 to 4 bits (r is the high bit),
/// - `x` is an extra high bit that expands SIB.index from 3 to 4 bits (x is the high bit),
/// - `b` is an extra high bit that expands *something* from 3 to 4 bits (b is the high bit),
///   with *something* being one of:
///   - ModR/M.r/m
///   - SIB.base
///   - the register in the 3 low bits of the opcode byte.
fn rex_prefix_byte(w: Bit, r: Bit, x: Bit, b: Bit) -> u8 {
	byte_from_bits(&[Bit::_0, Bit::_1, Bit::_0, Bit::_0, w, r, x, b])
}

/// Okay, the ModR/M byte. It is optional, one byte, and comes just after the opcode bytes
/// (before the optional SIB byte and the optional displacement and the optional immediate).
///
/// Its format is `mod` (2 bits) then `reg` (3 bits) then `r/m` (3 bits) (from high to low), where:
/// - `mod`: if it is 11 it means there is no addressing stuff hapenning (no dereferencing),
///   if it is 00 it means there is *maybe* a simple dereferencing (or maybe not, the Table 2-2
///   "32-Bit Addressing Forms with the ModR/M Byte" in the Intel x86_64 manual says there are
///   some exceptions depending on the registers involved), if it is 01 or 10 it means there is
///   *maybe* a dereferencing of an address added to an immediate offset.
///   ***TODO** explain this better using § 2.1.3 "ModR/M and SIB Bytes" of the x86_64 manual.*
/// - `reg` is either the 3 low bits of a register id that is in one of the operands,
///   or a specific value that complements the opcode bytes.
/// - `r/m` is also the 3 low bits of a register id that is in one of the operands (or not?
///   idk, there may be more to it, ***TODO** explain this using § 2.1.3
///   "ModR/M and SIB Bytes" of the x86_64 manual*).
fn mod_rm_byte(mod_: U2, reg: U3, rm: U3) -> u8 {
	mod_.as_u8() << 6 | reg.as_u8() << 3 | rm.as_u8()
}

pub(crate) fn separate_bit_b_in_bxxx(four_bit_value: U4) -> (Bit, U3) {
	let high_bit = four_bit_value.as_u8() >> 3;
	let low_3_bits = four_bit_value.as_u8() & 0b00000111;
	(Bit::new(high_bit), U3::new(low_3_bits))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code)]
#[rustfmt::skip]
pub(crate) enum Reg64 {
	Rax, Rcx, Rdx, Rbx, Rsp, Rbp, Rsi, Rdi, R8, R9, R10, R11, R12, R13, R14, R15,
}

impl Reg64 {
	/// These registers are represented by 4-bit numbers.
	///
	/// When the high bit is 1 (for R8 to R15) it has to be set in the appropriate field in
	/// the REX prefix (because the places these numbers usually go are only 3-bit wide).
	#[rustfmt::skip]
	pub(crate) fn id(self) -> U4 {
		U4::new(match self {
			Reg64::Rax => 0,  Reg64::Rcx => 1,  Reg64::Rdx => 2,  Reg64::Rbx => 3,
			Reg64::Rsp => 4,  Reg64::Rbp => 5,  Reg64::Rsi => 6,  Reg64::Rdi => 7,
			Reg64::R8  => 8,  Reg64::R9  => 9,  Reg64::R10 => 10, Reg64::R11 => 11,
			Reg64::R12 => 12, Reg64::R13 => 13, Reg64::R14 => 14, Reg64::R15 => 15,
		})
	}

	pub(crate) fn id_lower_u3(self) -> U3 {
		U3::new(self.id().as_u8() & 0b111)
	}

	pub(crate) fn id_higher_bit(self) -> Bit {
		Bit::new(self.id().as_u8() >> 3)
	}

	#[rustfmt::skip]
	pub(crate) fn name(self) -> &'static str {
		match self {
			Reg64::Rax => "rax", Reg64::Rcx => "rcx", Reg64::Rdx => "rdx", Reg64::Rbx => "rbx",
			Reg64::Rsp => "rsp", Reg64::Rbp => "rbp", Reg64::Rsi => "rsi", Reg64::Rdi => "rdi",
			Reg64::R8  => "r8",  Reg64::R9  => "r9",  Reg64::R10 => "r10", Reg64::R11 => "r11",
			Reg64::R12 => "r12", Reg64::R13 => "r13", Reg64::R14 => "r14", Reg64::R15 => "r15",
		}
	}
}

impl std::fmt::Display for Reg64 {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.name())
	}
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum BaseSize {
	Size8,
	Size32,
	Size64,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum BaseSign {
	Signed,
	Unsigned,
}

pub(crate) enum AsmInstr {
	/// Sets the register to the immediate value,
	/// being careful about the zero/sign extentions when needed.
	MovImmToReg64 {
		imm_src: Imm,
		reg_dst: Reg64,
	},
	/// Does `dst = *src`, with `src` being interpreted as a pointer to a 8, 32 or 64 bits area.
	MovDerefReg64ToReg64 {
		/// How large is the memory region to read from?
		src_size: BaseSize,
		/// How signed is the value that is read?
		src_sign: BaseSign,
		reg_as_ptr_src: Reg64,
		reg_dst: Reg64,
	},
	/// Does `*dst = src`, with `dst` being interpreted as a pointer to a 8, 32 or 64 bits area.
	MovReg64ToDerefReg64 {
		/// How large is the memory region to write to?
		dst_size: BaseSize,
		reg_src: Reg64,
		reg_as_ptr_dst: Reg64,
	},
	PushReg64 {
		reg_src: Reg64,
	},
	PopToReg64 {
		reg_dst: Reg64,
	},
	AddReg64ToReg64 {
		reg_src: Reg64,
		reg_dst: Reg64,
	},
	/// Syscall number is in RAX.
	/// Arguments are passed via registers in that order: RDI, RSI, RDX, R10, R8, R9.
	/// Return value is in RAX,
	/// second return value (only used by the pipe syscall on some architectures) is in RDX.
	Syscall,
	/// `UD2` "Undefined Instruction", raises an "invalid opcode" exception.
	Illegal,
	/// This is a fake instruction that doesn't generate any machine code.
	/// It just helps with code generation by marking the address of the next instruction
	/// with its name (to make it an easy target for jumps, branches and calls).
	/// All label addresses can be found in the `Layout`.
	Label {
		name: String,
	},
	JumpToLabel {
		label_name: String,
	},
}

impl AsmInstr {
	/// Generates the machine code bytes for this assembly instruction.
	/// We are given to know in advence the memory address of this instruction via `instr_address`.
	//
	// TODO: Make it so that every call doesn't allocate a `Vec`. This is a bit silly >w<
	pub(crate) fn to_machine_code(&self, layout: &Layout, instr_address: usize) -> Vec<u8> {
		let bytes = match self {
			AsmInstr::MovImmToReg64 { imm_src, reg_dst } => {
				// One of:
				// - `MOV r64, imm64`
				// - `MOV r32, imm32`
				// - `MOV r/m64, imm32`
				// - `XOR r32, r/m32` then `MOV r8, imm8`
				// - `XOR r32, r/m32`

				// MOV has a lot of variants, we try to choose a variant that
				// uses fewer bytes (with moderate effort), so there are a lot of cases.

				let (reg_dst_id_high_bit, reg_dst_id_low_3_bits) = separate_bit_b_in_bxxx(reg_dst.id());
				let mut machine_code = vec![];

				// This case was becoming too long, a part of it was offloaded to this helper function.
				let config = ConfigForMovImmToReg64::get(imm_src, reg_dst);

				// If the value is zero, then we just zero the register without the need for
				// moving an immediate value (that would be zero) after.
				let only_zero_no_mov = imm_src.is_raw_zero();

				// If the value is not zero, then we use some variant of MOV that corresponds
				// to what the config says, there is even a case where we prepend a XOR instruction
				// to zero the destination register before the MOV.
				let need_zero = config.zero_before_and_8 || only_zero_no_mov;
				let need_mov = !only_zero_no_mov;

				if need_zero {
					// `XOR r32, r/m32` (zero extended so it zeros the whole 64 bits register)
					let rex_prefix =
						rex_prefix_byte(Bit::_0, reg_dst_id_high_bit, Bit::_0, reg_dst_id_high_bit);
					let opcode_byte = 0x33;
					let mod_rm =
						mod_rm_byte(U2::new(0b11), reg_dst_id_low_3_bits, reg_dst_id_low_3_bits);
					let needs_rex = reg_dst_id_high_bit == Bit::_1;
					if needs_rex {
						machine_code.extend([rex_prefix]);
					}
					machine_code.extend([opcode_byte, mod_rm]);
				}

				if need_mov {
					let rex_prefix =
						rex_prefix_byte(config.rex_w, Bit::_0, Bit::_0, reg_dst_id_high_bit);
					if config.zero_before_and_8 {
						// `MOV r8, imm8`
						assert_eq!(config.rex_w, Bit::_0);
						let register_will_be_confused = (4..=7).contains(&reg_dst.id().as_u8());
						let needs_rex = reg_dst_id_high_bit == Bit::_1 || register_will_be_confused;
						let opcode_byte = 0xb0 + reg_dst_id_low_3_bits.as_u8();
						if needs_rex {
							machine_code.extend([rex_prefix]);
						}
						machine_code.extend([opcode_byte]);
					} else if config.signed_32 {
						// `MOV r/m64, imm32`
						assert_eq!(config.rex_w, Bit::_1);
						let opcode_byte = 0xc7;
						let mod_rm = mod_rm_byte(U2::new(0b11), U3::new(0), reg_dst_id_low_3_bits);
						machine_code.extend([rex_prefix, opcode_byte, mod_rm]);
					} else {
						// `MOV r64, imm64` or `MOV r32, imm32`
						let opcode_byte = 0xb8 + reg_dst_id_low_3_bits.as_u8();
						let needs_rex = config.rex_w == Bit::_1 || reg_dst_id_high_bit == Bit::_1;
						if needs_rex {
							machine_code.extend([rex_prefix]);
						}
						machine_code.extend([opcode_byte]);
					}
					let imm_as_bytes = imm_src.to_8_bytes(layout);
					machine_code.extend(&imm_as_bytes[..config.imm_size_in_bytes]);
				}

				machine_code
			},
			AsmInstr::MovDerefReg64ToReg64 { src_size, src_sign, reg_as_ptr_src, reg_dst } => {
				// One of:
				// - `MOV r64, r/m64`
				// - `MOV r32, r/m32`
				// - `MOVSXD r64, r/m32`
				// - `MOVSX r64, r/m8`
				// - `MOVZX r64, r/m8`

				assert!(
					*reg_as_ptr_src != Reg64::Rsp && *reg_as_ptr_src != Reg64::Rbp,
					"The addressing forms with the ModR/M byte look a bit funky \
					for these registers, maybe just move the address to dereference \
					to an other register..."
				);
				assert!(
					*reg_as_ptr_src != Reg64::R12 && *reg_as_ptr_src != Reg64::R13,
					"For some reason MOVing from [r12] [r13] doesn't work for now >_<..."
				);

				// TODO: The issue with RSP,RBP,R12,R13 might be the "Special Cases of REX Encodings"
				// (pages 618-619 of the full Intel manual pdf).

				let (reg_src_id_high_bit, reg_src_id_low_3_bits) =
					separate_bit_b_in_bxxx(reg_as_ptr_src.id());
				let (reg_dst_id_high_bit, reg_dst_id_low_3_bits) = separate_bit_b_in_bxxx(reg_dst.id());
				let mod_rm = mod_rm_byte(U2::new(0b00), reg_dst_id_low_3_bits, reg_src_id_low_3_bits);
				let (rex_w, opcode_bytes): (Bit, &[u8]) = match (src_size, src_sign) {
					(BaseSize::Size64, _) => (Bit::_1, &[0x8b]),
					(BaseSize::Size32, BaseSign::Unsigned) => (Bit::_0, &[0x8b]),
					(BaseSize::Size32, BaseSign::Signed) => (Bit::_1, &[0x63]),
					(BaseSize::Size8, BaseSign::Unsigned) => (Bit::_1, &[0x0f, 0xb6]),
					(BaseSize::Size8, BaseSign::Signed) => (Bit::_1, &[0x0f, 0xbe]),
				};
				let rex_prefix =
					rex_prefix_byte(rex_w, reg_dst_id_high_bit, Bit::_0, reg_src_id_high_bit);
				let mut machine_code = vec![rex_prefix];
				machine_code.extend(opcode_bytes);
				machine_code.extend([mod_rm]);
				machine_code
			},
			AsmInstr::MovReg64ToDerefReg64 { dst_size, reg_src, reg_as_ptr_dst } => {
				// `MOV r/m64, r64` or `MOV r/m32, r32` or `MOV r/m8, r8`
				assert!(
					*reg_as_ptr_dst != Reg64::Rsp && *reg_as_ptr_dst != Reg64::Rbp,
					"The addressing forms with the ModR/M byte look a bit funky \
					for these registers, maybe just move the address to dereference \
					to an other register..."
				);
				let (reg_src_id_high_bit, reg_src_id_low_3_bits) = separate_bit_b_in_bxxx(reg_src.id());
				let (reg_dst_id_high_bit, reg_dst_id_low_3_bits) =
					separate_bit_b_in_bxxx(reg_as_ptr_dst.id());
				let mod_rm = mod_rm_byte(U2::new(0b00), reg_src_id_low_3_bits, reg_dst_id_low_3_bits);
				let (rex_w, opcode_byte) = match dst_size {
					BaseSize::Size64 => (Bit::_1, 0x89),
					BaseSize::Size32 => (Bit::_0, 0x89),
					BaseSize::Size8 => (Bit::_0, 0x88),
				};
				let rex_prefix =
					rex_prefix_byte(rex_w, reg_src_id_high_bit, Bit::_0, reg_dst_id_high_bit);
				vec![rex_prefix, opcode_byte, mod_rm]
			},
			AsmInstr::PushReg64 { reg_src } => {
				// `PUSH r64`
				let (reg_src_id_high_bit, reg_src_id_low_3_bits) = separate_bit_b_in_bxxx(reg_src.id());
				let rex_prefix = rex_prefix_byte(Bit::_1, Bit::_0, Bit::_0, reg_src_id_high_bit);
				let opcode_byte = 0x50 + reg_src_id_low_3_bits.as_u8();
				vec![rex_prefix, opcode_byte]
			},
			AsmInstr::PopToReg64 { reg_dst } => {
				// `POP r64`
				let (reg_dst_id_high_bit, reg_dst_id_low_3_bits) = separate_bit_b_in_bxxx(reg_dst.id());
				let rex_prefix = rex_prefix_byte(Bit::_1, Bit::_0, Bit::_0, reg_dst_id_high_bit);
				let opcode_byte = 0x58 + reg_dst_id_low_3_bits.as_u8();
				vec![rex_prefix, opcode_byte]
			},
			AsmInstr::AddReg64ToReg64 { reg_src, reg_dst } => {
				// `ADD r/m64, r64`
				let (reg_src_id_high_bit, reg_src_id_low_3_bits) = separate_bit_b_in_bxxx(reg_src.id());
				let (reg_dst_id_high_bit, reg_dst_id_low_3_bits) = separate_bit_b_in_bxxx(reg_dst.id());
				let mod_rm = mod_rm_byte(U2::new(0b11), reg_src_id_low_3_bits, reg_dst_id_low_3_bits);
				let rex_prefix =
					rex_prefix_byte(Bit::_1, reg_src_id_high_bit, Bit::_0, reg_dst_id_high_bit);
				let opcode_byte = 0x01;
				vec![rex_prefix, opcode_byte, mod_rm]
			},
			AsmInstr::Syscall => vec![0x0f, 0x05], // `SYSCALL`
			AsmInstr::Illegal => vec![0x0f, 0x0b], // `UD2`
			AsmInstr::Label { .. } => vec![],
			AsmInstr::JumpToLabel { label_name } => {
				// `JMP rel32`
				// Note that the (relative) (signed) displacement is from the address of
				// the instruction that follows the jump instruction.
				let next_instr_address = instr_address + self.machine_code_size();
				let label_address = layout.code_label_address_table[label_name];
				let displacement = (label_address as isize - next_instr_address as isize) as i32;
				let opcode_byte = 0xe9;
				let mut machine_code = vec![opcode_byte];
				machine_code.extend(displacement.to_le_bytes());
				machine_code
			},
		};
		assert_eq!(bytes.len(), self.machine_code_size());
		bytes
	}

	pub(crate) fn machine_code_size(&self) -> usize {
		match self {
			AsmInstr::MovImmToReg64 { imm_src, reg_dst } => {
				let (reg_dst_id_high_bit, _reg_dst_id_low_3_bits) =
					separate_bit_b_in_bxxx(reg_dst.id());
				let need_rex_r_bit = reg_dst_id_high_bit == Bit::_1;
				if imm_src.is_raw_zero() {
					// `XOR r32, r/m32`
					2 + if need_rex_r_bit { 1 } else { 0 }
				} else {
					let config = ConfigForMovImmToReg64::get(imm_src, reg_dst);
					if config.imm_size_in_bytes == 8 {
						// `MOV r64, imm64`
						assert_eq!(config.rex_w, Bit::_1);
						10
					} else if config.imm_size_in_bytes == 4 && config.signed_32 {
						// `MOV r/m64, imm32`
						assert_eq!(config.rex_w, Bit::_1);
						7
					} else if config.imm_size_in_bytes == 4 {
						// `MOV r32, imm32`
						assert_eq!(config.rex_w, Bit::_0);
						5 + if need_rex_r_bit { 1 } else { 0 }
					} else if config.imm_size_in_bytes == 1 {
						// `XOR r32, r/m32` then `MOV r8, imm8`
						assert_eq!(config.rex_w, Bit::_0);
						assert!(!need_rex_r_bit);
						let register_will_be_confused = (4..=7).contains(&reg_dst.id().as_u8());
						4 + if register_will_be_confused { 1 } else { 0 }
					} else {
						unreachable!()
					}
				}
			},
			AsmInstr::MovDerefReg64ToReg64 { src_size, .. } => match src_size {
				BaseSize::Size8 => 4,
				_ => 3,
			},
			AsmInstr::MovReg64ToDerefReg64 { .. } => 3,
			AsmInstr::AddReg64ToReg64 { .. } => 3,
			AsmInstr::PushReg64 { .. } => 2,
			AsmInstr::PopToReg64 { .. } => 2,
			AsmInstr::Syscall => 2,
			AsmInstr::Illegal => 2,
			AsmInstr::Label { .. } => 0,
			AsmInstr::JumpToLabel { .. } => 5,
		}
	}
}

/// Just a helper type used when generating the x86_64 machine code
/// that moves an immediate value to a 64 bits register.
struct ConfigForMovImmToReg64 {
	rex_w: Bit,
	imm_size_in_bytes: usize,
	/// Use the sign extended 32 bits MOV variant.
	signed_32: bool,
	/// Zeroify the register before MOV and use the 8 bits MOV variant.
	zero_before_and_8: bool,
}
impl ConfigForMovImmToReg64 {
	fn get(imm_src: &Imm, reg_dst: &Reg64) -> Self {
		match imm_src {
			Imm::Imm64(imm64) => {
				// `MOV r64, imm64`
				Self {
					rex_w: Bit::_1,
					imm_size_in_bytes: 8,
					signed_32: false,
					zero_before_and_8: false,
				}
			},
			Imm::Imm32(imm32) => {
				if imm32.is_signed() {
					// `MOV r/m64, imm32`, this sign extends the value
					Self {
						rex_w: Bit::_1,
						imm_size_in_bytes: 4,
						signed_32: true,
						zero_before_and_8: false,
					}
				} else {
					// `MOV r32, imm32`, this zero-extends the value
					Self {
						rex_w: Bit::_0,
						imm_size_in_bytes: 4,
						signed_32: false,
						zero_before_and_8: false,
					}
				}
			},
			Imm::Imm8(imm8) => {
				if imm8.is_signed() {
					// `MOV r/m64, imm32`, this sign extends the value
					//
					// Note: The `MOV r/m64, imm8` variant does NOT sign extend the value
					// (see https://stackoverflow.com/q/11177137 for more info on that)
					// and we could use `MOVSX` to then sign extend the value
					// (this one does not have an imm variant) but that instruction is 4 bytes
					// and we only save 3 bytes by using `MOV r/m64, imm8`.
					// In the end it would be one byte longer so it is not worth it.
					Self {
						rex_w: Bit::_1,
						imm_size_in_bytes: 4,
						signed_32: true,
						zero_before_and_8: false,
					}
				} else {
					let (reg_dst_id_high_bit, _reg_dst_id_low_3_bits) =
						separate_bit_b_in_bxxx(reg_dst.id());
					let need_rex_r_bit = reg_dst_id_high_bit == Bit::_1;
					if need_rex_r_bit {
						// `MOV r32, imm32`, this zero-extends the value
						//
						// The two REX prefixes needed in this case if we happened to
						// go with the config of the other branch happen to make is the same size
						// but two instructions instead of one, so it is not worth it.
						// This is better.
						Self {
							rex_w: Bit::_0,
							imm_size_in_bytes: 4,
							signed_32: false,
							zero_before_and_8: false,
						}
					} else {
						// `XOR r32, r/m32` then `MOV r8, imm8`
						//
						// Note: `MOV r8, imm8` does NOT zero extend the value, so we zero the
						// desination register first with the good old xor reg reg.
						// There is no need to use the 64 bits XOR variant because the 32 bits variant
						// zero extends the result anyway, so we can spare the REX prefix if the register
						// doesn't need the REX.R bit. Dependeing on the register, the XOR
						// takes either 2 or 3 bytes, so we actually spare either 0 or 1 byte
						// so it is worth it.
						Self {
							rex_w: Bit::_0,
							imm_size_in_bytes: 1,
							signed_32: false,
							zero_before_and_8: true,
						}
					}
				}
			},
		}
	}
}
