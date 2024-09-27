// Immediate values `Imm8`, `Imm32` and `Imm64` can sometimes represent something (like a memory
// address of something in the data segment for example) that isn't just a raw number.
// Immediate values can also just be a raw number (either signed or unsigned btw).
// We make the difference here, with `Raw8`, `Raw32` and `Raw64` being different types than
// immediate value types, and immediate value types being convertible to raw values given
// some layout information available at the time assembly code is not being generated anymore
// and is ready to be converted to machine code, at the end.
// Unless there is a good reason, assembly instruction variants should hold immediate values
// with the `ImmN` types instead of the `RawN` types or the `uN`/`iN` types.

use crate::elf::Layout;

#[derive(Clone, Copy)]
pub(crate) enum Raw8 {
	Signed(i8),
	Unsigned(u8),
}
#[derive(Clone, Copy)]
pub(crate) enum Raw32 {
	Signed(i32),
	Unsigned(u32),
}
#[derive(Clone, Copy)]
pub(crate) enum Raw64 {
	Signed(i64),
	Unsigned(u64),
}

macro_rules! impl_raw_is_signed {
	($raw_n:ty) => {
		impl $raw_n {
			pub(crate) fn is_signed(self) -> bool {
				match self {
					Self::Signed(_) => true,
					Self::Unsigned(_) => false,
				}
			}
		}
	};
}
impl_raw_is_signed!(Raw8);
impl_raw_is_signed!(Raw32);
impl_raw_is_signed!(Raw64);

macro_rules! impl_raw_is_zero {
	($raw_n:ty) => {
		impl $raw_n {
			pub(crate) fn is_zero(self) -> bool {
				match self {
					Self::Signed(value) => value == 0,
					Self::Unsigned(value) => value == 0,
				}
			}
		}
	};
}
impl_raw_is_zero!(Raw8);
impl_raw_is_zero!(Raw32);
impl_raw_is_zero!(Raw64);

macro_rules! impl_raw_to_bytes {
	($raw_n:ty, $fn_name:ident, $as_unsigned:ty, $as_signed:ty, $size:literal) => {
		impl $raw_n {
			pub(crate) fn $fn_name(self) -> [u8; $size] {
				match self {
					Self::Signed(value) => (value as $as_signed).to_le_bytes(),
					Self::Unsigned(value) => (value as $as_unsigned).to_le_bytes(),
				}
			}
		}
	};
}
impl_raw_to_bytes!(Raw64, to_8_bytes, i64, u64, 8);
impl_raw_to_bytes!(Raw32, to_8_bytes, i64, u64, 8);
impl_raw_to_bytes!(Raw32, to_4_bytes, i32, u32, 4);
impl_raw_to_bytes!(Raw8, to_8_bytes, i64, u64, 8);
impl_raw_to_bytes!(Raw8, to_4_bytes, i32, u32, 4);
impl_raw_to_bytes!(Raw8, to_1_bytes, i8, u8, 1);

pub(crate) enum Imm8 {
	Raw(Raw8),
}

impl Imm8 {
	pub(crate) fn to_raw_8(&self, _layout: &Layout) -> Raw8 {
		match self {
			Imm8::Raw(raw) => *raw,
		}
	}

	pub(crate) fn is_signed(&self) -> bool {
		matches!(self, Imm8::Raw(Raw8::Signed(_)))
	}

	pub(crate) fn is_raw_zero(&self) -> bool {
		matches!(self, Imm8::Raw(raw8) if raw8.is_zero())
	}
}

pub(crate) enum Imm32 {
	DataAddr { offset_in_data_segment: u32 },
	Raw(Raw32),
}

impl Imm32 {
	pub(crate) fn to_raw_32(&self, layout: &Layout) -> Raw32 {
		match self {
			Imm32::DataAddr { offset_in_data_segment } => {
				Raw32::Unsigned(layout.data_segment_address as u32 + offset_in_data_segment)
			},
			Imm32::Raw(raw) => *raw,
		}
	}

	pub(crate) fn is_signed(&self) -> bool {
		matches!(self, Imm32::Raw(Raw32::Signed(_)))
	}

	pub(crate) fn is_raw_zero(&self) -> bool {
		matches!(self, Imm32::Raw(raw32) if raw32.is_zero())
	}
}

pub(crate) enum Imm64 {
	DataAddr { offset_in_data_segment: u64 },
	Raw(Raw64),
}

impl Imm64 {
	pub(crate) fn to_raw_64(&self, layout: &Layout) -> Raw64 {
		match self {
			Imm64::DataAddr { offset_in_data_segment } => {
				Raw64::Unsigned(layout.data_segment_address as u64 + offset_in_data_segment)
			},
			Imm64::Raw(raw) => *raw,
		}
	}

	pub(crate) fn is_signed(&self) -> bool {
		matches!(self, Imm64::Raw(Raw64::Signed(_)))
	}

	pub(crate) fn is_raw_zero(&self) -> bool {
		matches!(self, Imm64::Raw(raw64) if raw64.is_zero())
	}
}

pub(crate) enum Imm {
	Imm8(Imm8),
	Imm32(Imm32),
	Imm64(Imm64),
}

impl Imm {
	pub(crate) fn signed_raw(value: i64) -> Imm {
		if let Ok(value) = value.try_into() {
			Imm::Imm8(Imm8::Raw(Raw8::Signed(value)))
		} else if let Ok(value) = value.try_into() {
			Imm::Imm32(Imm32::Raw(Raw32::Signed(value)))
		} else {
			Imm::Imm64(Imm64::Raw(Raw64::Signed(value)))
		}
	}

	pub(crate) fn unsigned_raw(value: u64) -> Imm {
		if let Ok(value) = value.try_into() {
			Imm::Imm8(Imm8::Raw(Raw8::Unsigned(value)))
		} else if let Ok(value) = value.try_into() {
			Imm::Imm32(Imm32::Raw(Raw32::Unsigned(value)))
		} else {
			Imm::Imm64(Imm64::Raw(Raw64::Unsigned(value)))
		}
	}

	pub(crate) fn is_signed(&self) -> bool {
		match self {
			Imm::Imm8(imm8) => imm8.is_signed(),
			Imm::Imm32(imm32) => imm32.is_signed(),
			Imm::Imm64(imm64) => imm64.is_signed(),
		}
	}

	pub(crate) fn is_raw_zero(&self) -> bool {
		match self {
			Imm::Imm8(imm8) => imm8.is_raw_zero(),
			Imm::Imm32(imm32) => imm32.is_raw_zero(),
			Imm::Imm64(imm64) => imm64.is_raw_zero(),
		}
	}

	pub(crate) fn to_8_bytes(&self, layout: &Layout) -> [u8; 8] {
		match self {
			Imm::Imm8(imm8) => imm8.to_raw_8(layout).to_8_bytes(),
			Imm::Imm32(imm32) => imm32.to_raw_32(layout).to_8_bytes(),
			Imm::Imm64(imm64) => imm64.to_raw_64(layout).to_8_bytes(),
		}
	}
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
	fn id(self) -> U4 {
		match self {
			Reg64::Rax => 0,  Reg64::Rcx => 1,  Reg64::Rdx => 2,  Reg64::Rbx => 3,
			Reg64::Rsp => 4,  Reg64::Rbp => 5,  Reg64::Rsi => 6,  Reg64::Rdi => 7,
			Reg64::R8  => 8,  Reg64::R9  => 9,  Reg64::R10 => 10, Reg64::R11 => 11,
			Reg64::R12 => 12, Reg64::R13 => 13, Reg64::R14 => 14, Reg64::R15 => 15,
		}
	}
}

#[derive(Clone, Copy)]
pub(crate) enum BaseSize {
	Size8,
	Size32,
	Size64,
}

pub(crate) enum AsmInstr {
	MovImmToReg64 {
		imm_src: Imm,
		reg_dst: Reg64,
	},
	/// Does `dst = *src`, with `src` being interpreted as a pointer to a 8, 32 or 64 bits area.
	MovDerefReg64ToReg64 {
		/// How large is the memory region to read from?
		src_size: BaseSize,
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
	Syscall,
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
				// `MOV r64, imm64` or `MOV r32, imm32` or `MOV r/m64, imm32`
				// or (`XOR r32, r/m32` then `MOV r8, imm8`) or `XOR r32, r/m32`

				// Sorry, MOV has a lot of variants and here we try to use one that
				// uses as few bytes as we can (with moderate effort),
				// so there are a lot of cases.

				// If the value is zero, then we just zero the register without the need for
				// moving an immediate value (that would be zero) after.
				let only_zero_no_mov = imm_src.is_raw_zero();

				// If the value is not zero, then we use some variant of MOV that corresponds
				// to what this config says, there is even a case where we prepend a XOR instruction
				// to zero the destination register before the MOV.
				let config = ConfigForMovImmToReg64::get(imm_src, reg_dst);

				let (reg_dst_id_high_bit, reg_dst_id_low_3_bits) = separate_bit_b_in_bxxx(reg_dst.id());
				let mut machine_code = vec![];

				if config.zero_before_and_8 || only_zero_no_mov {
					// `XOR r32, r/m32` (zero extended so it zeros the whole 64 bit register)
					let rex_prefix = rex_prefix_byte(0, reg_dst_id_high_bit, 0, reg_dst_id_high_bit);
					let opcode_byte = 0x33;
					let mod_rm = mod_rm_byte(0b11, reg_dst_id_low_3_bits, reg_dst_id_low_3_bits);
					let needs_rex = reg_dst_id_high_bit == 1;
					if needs_rex {
						machine_code.extend([rex_prefix]);
					}
					machine_code.extend([opcode_byte, mod_rm]);
				}

				let need_mov = !only_zero_no_mov;
				if need_mov {
					let rex_prefix = rex_prefix_byte(config.rex_w, 0, 0, reg_dst_id_high_bit);
					if config.zero_before_and_8 {
						// `MOV r8, imm8`
						assert_eq!(config.rex_w, 0);
						let needs_rex = reg_dst_id_high_bit == 1;
						let opcode_byte = 0xb0 + reg_dst_id_low_3_bits;
						if needs_rex {
							machine_code.extend([rex_prefix]);
						}
						machine_code.extend([opcode_byte]);
					} else if config.signed_32 {
						// `MOV r/m64, imm32`
						assert_eq!(config.rex_w, 1);
						let opcode_byte = 0xc7;
						let mod_rm = mod_rm_byte(0b11, 0, reg_dst_id_low_3_bits);
						machine_code.extend([rex_prefix, opcode_byte, mod_rm]);
					} else {
						// `MOV r64, imm64` or `MOV r32, imm32`
						let opcode_byte = 0xb8 + reg_dst_id_low_3_bits;
						let needs_rex = config.rex_w == 1 || reg_dst_id_high_bit == 1;
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
			AsmInstr::MovDerefReg64ToReg64 { src_size, reg_as_ptr_src, reg_dst } => {
				// `MOV r64, r/m64` or `MOV r32, r/m32` or `MOV r8, r/m8`
				assert!(
					*reg_as_ptr_src != Reg64::Rsp && *reg_as_ptr_src != Reg64::Rbp,
					"The addressing forms with the ModR/M byte look a bit funky \
					for these registers, maybe just move the address to dereference \
					to an other register..."
				);
				let (reg_src_id_high_bit, reg_src_id_low_3_bits) =
					separate_bit_b_in_bxxx(reg_as_ptr_src.id());
				let (reg_dst_id_high_bit, reg_dst_id_low_3_bits) = separate_bit_b_in_bxxx(reg_dst.id());
				let mod_rm = mod_rm_byte(0b00, reg_src_id_low_3_bits, reg_dst_id_low_3_bits);
				let (rex_w, opcode_byte) = match src_size {
					BaseSize::Size64 => (1, 0x8b),
					BaseSize::Size32 => (0, 0x8b),
					BaseSize::Size8 => (0, 0x8a),
				};
				let rex_prefix = rex_prefix_byte(rex_w, reg_src_id_high_bit, 0, reg_dst_id_high_bit);
				vec![rex_prefix, opcode_byte, mod_rm]
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
				let mod_rm = mod_rm_byte(0b00, reg_src_id_low_3_bits, reg_dst_id_low_3_bits);
				let (rex_w, opcode_byte) = match dst_size {
					BaseSize::Size64 => (1, 0x89),
					BaseSize::Size32 => (0, 0x89),
					BaseSize::Size8 => (0, 0x88),
				};
				let rex_prefix = rex_prefix_byte(rex_w, reg_src_id_high_bit, 0, reg_dst_id_high_bit);
				vec![rex_prefix, opcode_byte, mod_rm]
			},
			AsmInstr::PushReg64 { reg_src } => {
				// `PUSH r64`
				let (reg_src_id_high_bit, reg_src_id_low_3_bits) = separate_bit_b_in_bxxx(reg_src.id());
				let rex_prefix = rex_prefix_byte(1, 0, 0, reg_src_id_high_bit);
				let opcode_byte = 0x50 + reg_src_id_low_3_bits;
				vec![rex_prefix, opcode_byte]
			},
			AsmInstr::PopToReg64 { reg_dst } => {
				// `POP r64`
				let (reg_dst_id_high_bit, reg_dst_id_low_3_bits) = separate_bit_b_in_bxxx(reg_dst.id());
				let rex_prefix = rex_prefix_byte(1, 0, 0, reg_dst_id_high_bit);
				let opcode_byte = 0x58 + reg_dst_id_low_3_bits;
				vec![rex_prefix, opcode_byte]
			},
			AsmInstr::AddReg64ToReg64 { reg_src, reg_dst } => {
				// `ADD r/m64, r64`
				let (reg_src_id_high_bit, reg_src_id_low_3_bits) = separate_bit_b_in_bxxx(reg_src.id());
				let (reg_dst_id_high_bit, reg_dst_id_low_3_bits) = separate_bit_b_in_bxxx(reg_dst.id());
				let mod_rm = mod_rm_byte(0b11, reg_src_id_low_3_bits, reg_dst_id_low_3_bits);
				let rex_prefix = rex_prefix_byte(1, reg_src_id_high_bit, 0, reg_dst_id_high_bit);
				let opcode_byte = 0x01;
				vec![rex_prefix, opcode_byte, mod_rm]
			},
			AsmInstr::Syscall => vec![0x0f, 0x05],
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
				let need_rex_r_bit = reg_dst_id_high_bit == 1;
				if imm_src.is_raw_zero() {
					// `XOR r32, r/m32`
					2 + if need_rex_r_bit { 1 } else { 0 }
				} else {
					let config = ConfigForMovImmToReg64::get(imm_src, reg_dst);
					if config.imm_size_in_bytes == 8 {
						// `MOV r64, imm64`
						assert_eq!(config.rex_w, 1);
						10
					} else if config.imm_size_in_bytes == 4 && config.signed_32 {
						// `MOV r/m64, imm32`
						assert_eq!(config.rex_w, 1);
						7
					} else if config.imm_size_in_bytes == 4 {
						// `MOV r32, imm32`
						assert_eq!(config.rex_w, 0);
						5 + if need_rex_r_bit { 1 } else { 0 }
					} else if config.imm_size_in_bytes == 1 {
						// `XOR r32, r/m32` then `MOV r8, imm8`
						assert_eq!(config.rex_w, 0);
						assert!(!need_rex_r_bit);
						4
					} else {
						unreachable!()
					}
				}
			},
			AsmInstr::MovDerefReg64ToReg64 { .. } => 3,
			AsmInstr::MovReg64ToDerefReg64 { .. } => 3,
			AsmInstr::AddReg64ToReg64 { .. } => 3,
			AsmInstr::PushReg64 { .. } => 2,
			AsmInstr::PopToReg64 { .. } => 2,
			AsmInstr::Syscall => 2,
			AsmInstr::Label { .. } => 0,
			AsmInstr::JumpToLabel { .. } => 5,
		}
	}
}

struct ConfigForMovImmToReg64 {
	rex_w: Bit,
	imm_size_in_bytes: usize,
	/// Use the sign extended 32 bits MOV variant.
	signed_32: bool,
	/// Zero the register before and use the 8 bits MOV variant.
	zero_before_and_8: bool,
}
impl ConfigForMovImmToReg64 {
	fn get(imm_src: &Imm, reg_dst: &Reg64) -> Self {
		match imm_src {
			Imm::Imm64(imm64) => {
				// `MOV r64, imm64`
				Self {
					rex_w: 1,
					imm_size_in_bytes: 8,
					signed_32: false,
					zero_before_and_8: false,
				}
			},
			Imm::Imm32(imm32) => {
				if imm32.is_signed() {
					// `MOV r/m64, imm32`, this sign extends the value
					Self {
						rex_w: 1,
						imm_size_in_bytes: 4,
						signed_32: true,
						zero_before_and_8: false,
					}
				} else {
					// `MOV r32, imm32`, this zero-extends the value
					Self {
						rex_w: 0,
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
					// In the end it would be one byte longer so it is not wirth it.
					Self {
						rex_w: 1,
						imm_size_in_bytes: 4,
						signed_32: true,
						zero_before_and_8: false,
					}
				} else {
					let (reg_dst_id_high_bit, _reg_dst_id_low_3_bits) =
						separate_bit_b_in_bxxx(reg_dst.id());
					let need_rex_r_bit = reg_dst_id_high_bit == 1;
					if need_rex_r_bit {
						// `MOV r32, imm32`, this zero-extends the value
						//
						// The two REX prefixes needed in this case if we happened to
						// go with the config of the other branch happen to make is the same size
						// but two instructions instead of one, so it is not worth it.
						// This is better.
						Self {
							rex_w: 0,
							imm_size_in_bytes: 4,
							signed_32: false,
							zero_before_and_8: false,
						}
					} else {
						// `XOR r32, r/m32` then `MOV r8, imm8`
						//
						// Note: `MOV r8, imm8` does NOT zero extend the value, so we zero the
						// desination register first with the good old xor reg reg.
						// There is no need to use the 64-bit XOR variant because it zero extend
						// the result anyway, so we can spare the REX prefix if the register
						// doesn't need the REX.R bit. Dependeing on the register, the XOR
						// takes either 2 or 3 bytes, so we actually spare either 0 or 1 byte
						// so it is worth it.
						Self {
							rex_w: 0,
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

type U4 = u8;
type U3 = u8;
type U2 = u8;
type Bit = u8;

fn set_byte_bit(byte: &mut u8, bit_index: usize, bit_value: Bit) {
	assert!(bit_value <= 1);
	*byte |= bit_value << bit_index;
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
/// with *something* being one of:
///   - ModR/M.r/m
///   - SIB.base
///   - the register in the 3 low bits of the opcode byte.
fn rex_prefix_byte(w: Bit, r: Bit, x: Bit, b: Bit) -> u8 {
	byte_from_bits(&[0, 1, 0, 0, w, r, x, b])
}

/// Okay, the ModR/M byte. It is optional, one byte, and comes just after the opcode bytes
/// (before the optional SIB byte and the optional displacement and the optional immediate).
///
/// Its format is `mod` (2 bits) then `reg` (3 bits) then `r/m` (3 bits) (from high to low), where:
/// - `mod`: if it is 11 it means there is no addressing stuff hapenning (no dereferencing),
/// if it is 00 it means there is *maybe* a simple dereferencing (or maybe not, the Table 2-2
/// "32-Bit Addressing Forms with the ModR/M Byte" in the Intel x86_64 manual says there are
/// some exceptions depending on the registers involved), if it is 01 or 10 it means there is
/// *maybe* a dereferencing of an address added to an immediate offset.
/// ***TODO** explain this better using § 2.1.3 "ModR/M and SIB Bytes" of the x86_64 manual.*
/// - `reg` is either the 3 low bits of a register id that is in one of the operands,
/// or a specific value that complement the opcode bytes.
/// - `r/m` is also the 3 low bits of a register id that is in one of the operands (or not?
/// idk, there may be more to it, ***TODO** explain this using § 2.1.3
/// "ModR/M and SIB Bytes" of the x86_64 manual*).
fn mod_rm_byte(mod_: U2, reg: U3, rm: U3) -> u8 {
	assert!(mod_ <= 3);
	assert!(reg <= 7);
	assert!(rm <= 7);
	mod_ << 6 | reg << 3 | rm
}

fn separate_bit_b_in_bxxx(four_bit_value: U4) -> (Bit, U3) {
	assert!(four_bit_value <= 7);
	let high_bit = four_bit_value >> 3;
	let low_3_bits = four_bit_value & 0b00000111;
	(high_bit, low_3_bits)
}
