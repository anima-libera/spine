use crate::{
	asm::small_uints::{Bit, U2, U3, U4},
	elf::Layout,
	imm::{ImmRich, ImmRich32, Value32},
	x86_64::X8664Instr,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code)]
#[rustfmt::skip]
pub(crate) enum Reg32 {
	Eax, Ecx, Edx, Ebx, Esp, Ebp, Esi, Edi, R8d, R9d, R10d, R11d, R12d, R13d, R14d, R15d,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code)]
#[rustfmt::skip]
pub(crate) enum Reg8 {
	Al, Cl, Dl, Bl, Spl, Bpl, Sil, Dil, R8b, R9b, R10b, R11b, R12b, R13b, R14b, R15b,
	// I dont care about AH, BH, and the others that are not the lowest part of their bigger registers.
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

	#[rustfmt::skip]
	pub(crate) fn to_32(self) -> Reg32 {
		match self {
			Reg64::Rax => Reg32::Eax,  Reg64::Rcx => Reg32::Ecx,  Reg64::Rdx => Reg32::Edx,  Reg64::Rbx => Reg32::Ebx,
			Reg64::Rsp => Reg32::Esp,  Reg64::Rbp => Reg32::Ebp,  Reg64::Rsi => Reg32::Esi,  Reg64::Rdi => Reg32::Edi,
			Reg64::R8  => Reg32::R8d,  Reg64::R9  => Reg32::R9d,  Reg64::R10 => Reg32::R10d, Reg64::R11 => Reg32::R11d,
			Reg64::R12 => Reg32::R12d, Reg64::R13 => Reg32::R13d, Reg64::R14 => Reg32::R14d, Reg64::R15 => Reg32::R15d,
		}
	}

	#[rustfmt::skip]
	pub(crate) fn to_8(self) -> Reg8 {
		match self {
			Reg64::Rax => Reg8::Al,   Reg64::Rcx => Reg8::Cl,   Reg64::Rdx => Reg8::Dl,   Reg64::Rbx => Reg8::Bl,
			Reg64::Rsp => Reg8::Spl,  Reg64::Rbp => Reg8::Bpl,  Reg64::Rsi => Reg8::Sil,  Reg64::Rdi => Reg8::Dil,
			Reg64::R8  => Reg8::R8b,  Reg64::R9  => Reg8::R9b,  Reg64::R10 => Reg8::R10b, Reg64::R11 => Reg8::R11b,
			Reg64::R12 => Reg8::R12b, Reg64::R13 => Reg8::R13b, Reg64::R14 => Reg8::R14b, Reg64::R15 => Reg8::R15b,
		}
	}
}

impl std::fmt::Display for Reg64 {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "%{}", self.name())
	}
}

impl Reg32 {
	#[rustfmt::skip]
	pub(crate) fn id(self) -> U4 {
		U4::new(match self {
			Reg32::Eax  => 0,  Reg32::Ecx  => 1,  Reg32::Edx  => 2,  Reg32::Ebx  => 3,
			Reg32::Esp  => 4,  Reg32::Ebp  => 5,  Reg32::Esi  => 6,  Reg32::Edi  => 7,
			Reg32::R8d  => 8,  Reg32::R9d  => 9,  Reg32::R10d => 10, Reg32::R11d => 11,
			Reg32::R12d => 12, Reg32::R13d => 13, Reg32::R14d => 14, Reg32::R15d => 15,
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
			Reg32::Eax  => "eax",  Reg32::Ecx  => "ecx",  Reg32::Edx  => "edx",  Reg32::Ebx  => "ebx",
			Reg32::Esp  => "esp",  Reg32::Ebp  => "ebp",  Reg32::Esi  => "esi",  Reg32::Edi  => "edi",
			Reg32::R8d  => "r8d",  Reg32::R9d  => "r9d",  Reg32::R10d => "r10d", Reg32::R11d => "r11d",
			Reg32::R12d => "r12d", Reg32::R13d => "r13d", Reg32::R14d => "r14d", Reg32::R15d => "r15d",
		}
	}

	#[rustfmt::skip]
	pub(crate) fn to_64(self) -> Reg64 {
		match self {
			Reg32::Eax  => Reg64::Rax, Reg32::Ecx  => Reg64::Rcx, Reg32::Edx  => Reg64::Rdx, Reg32::Ebx  => Reg64::Rbx,
			Reg32::Esp  => Reg64::Rsp, Reg32::Ebp  => Reg64::Rbp, Reg32::Esi  => Reg64::Rsi, Reg32::Edi  => Reg64::Rdi,
			Reg32::R8d  => Reg64::R8 , Reg32::R9d  => Reg64::R9 , Reg32::R10d => Reg64::R10, Reg32::R11d => Reg64::R11,
			Reg32::R12d => Reg64::R12, Reg32::R13d => Reg64::R13, Reg32::R14d => Reg64::R14, Reg32::R15d => Reg64::R15,
		}
	}
}

impl std::fmt::Display for Reg32 {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "%{}", self.name())
	}
}

impl Reg8 {
	#[rustfmt::skip]
	pub(crate) fn id(self) -> U4 {
		U4::new(match self {
			Reg8::Al   => 0,  Reg8::Cl   => 1,  Reg8::Dl   => 2,  Reg8::Bl   => 3,
			Reg8::Spl  => 4,  Reg8::Bpl  => 5,  Reg8::Sil  => 6,  Reg8::Dil  => 7,
			Reg8::R8b  => 8,  Reg8::R9b  => 9,  Reg8::R10b => 10, Reg8::R11b => 11,
			Reg8::R12b => 12, Reg8::R13b => 13, Reg8::R14b => 14, Reg8::R15b => 15,
		})
	}

	/// Instructions sometimes (often? always?) require the mere presence of a REX prefix
	/// to allow refering to SPL, DIL, BPL or SIL.
	///
	/// See for example the spec for `MOV r8, imm8`: it says that if there is a REX prefix
	/// (even without any paylod bit set) it will change the meaning of register codes 4-7 (including)
	/// to mean SPL,DIL,BPL,SIL instead of AH,BH,CH,DH.
	pub(crate) fn is_rex_required(self) -> bool {
		(4..=7).contains(&self.id().as_u8())
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
			Reg8::Al   => "al",   Reg8::Cl   => "cl",   Reg8::Dl   => "dl",   Reg8::Bl   => "bl",
			Reg8::Spl  => "spl",  Reg8::Bpl  => "bpl",  Reg8::Sil  => "sil",  Reg8::Dil  => "dil",
			Reg8::R8b  => "r8b",  Reg8::R9b  => "r9b",  Reg8::R10b => "r10b", Reg8::R11b => "r11b",
			Reg8::R12b => "r12b", Reg8::R13b => "r13b", Reg8::R14b => "r14b", Reg8::R15b => "r15b",
		}
	}

	#[rustfmt::skip]
	pub(crate) fn to_64(self) -> Reg64 {
		match self {
			Reg8::Al   => Reg64::Rax, Reg8::Cl   => Reg64::Rcx, Reg8::Dl   => Reg64::Rdx, Reg8::Bl   => Reg64::Rbx,
			Reg8::Spl  => Reg64::Rsp, Reg8::Bpl  => Reg64::Rbp, Reg8::Sil  => Reg64::Rsi, Reg8::Dil  => Reg64::Rdi,
			Reg8::R8b  => Reg64::R8 , Reg8::R9b  => Reg64::R9 , Reg8::R10b => Reg64::R10, Reg8::R11b => Reg64::R11,
			Reg8::R12b => Reg64::R12, Reg8::R13b => Reg64::R13, Reg8::R14b => Reg64::R14, Reg8::R15b => Reg64::R15,
		}
	}
}

impl std::fmt::Display for Reg8 {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "%{}", self.name())
	}
}

pub(crate) enum RegOrMem64 {
	/// Access the register.
	Reg64(Reg64),
	/// Access memory for which the address is the value contained in the register.
	DerefReg64(Reg64),
	// TODO
}

impl std::fmt::Display for RegOrMem64 {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Reg64(reg) => write!(f, "{reg}"),
			Self::DerefReg64(reg) => write!(f, "[{reg}]"),
		}
	}
}

pub(crate) enum RegOrMem32 {
	/// Access the register.
	Reg32(Reg32),
	/// Access memory for which the address is the value contained in the register.
	DerefReg32(Reg32),
	// TODO
}

impl std::fmt::Display for RegOrMem32 {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Reg32(reg) => write!(f, "{reg}"),
			Self::DerefReg32(reg) => write!(f, "[{reg}]"),
		}
	}
}

pub(crate) enum RegOrMem8 {
	/// Access the register.
	Reg8(Reg8),
	/// Access memory for which the address is the value contained in the register.
	DerefReg8(Reg8),
	// TODO
}

impl std::fmt::Display for RegOrMem8 {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Reg8(reg) => write!(f, "{reg}"),
			Self::DerefReg8(reg) => write!(f, "[{reg}]"),
		}
	}
}

/// Immediate relative offset for `JMP rel32` instruction.
#[derive(Clone, Copy)]
pub(crate) struct Rel32(i32);

impl Rel32 {
	pub(crate) fn to_u32(self) -> u32 {
		self.0.cast_unsigned()
	}
}

impl std::fmt::Display for Rel32 {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{:+}", self.0)
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BaseSize {
	Size8,
	Size32,
	Size64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BaseSign {
	Signed,
	Unsigned,
}

#[derive(Debug)]
pub(crate) enum AsmInstr {
	/// Sets the register to the immediate value,
	/// being careful about the zero/sign extentions when needed.
	MovImmToReg64 {
		imm_src: ImmRich,
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
	/// The only registers that are modified are RCX, R11, RAX, and in a niche case RDX.
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
	pub(crate) fn to_machine_code(&self, layout: &Layout, instr_address: usize) -> Vec<X8664Instr> {
		match self {
			AsmInstr::MovImmToReg64 { imm_src, reg_dst } => {
				if imm_src.is_value_zero() {
					vec![X8664Instr::XorRegOrMem32ToReg32 {
						src: RegOrMem32::Reg32(reg_dst.to_32()),
						dst: reg_dst.to_32(),
					}]
				} else {
					match imm_src {
						ImmRich::Imm64(imm) => {
							vec![X8664Instr::MovImm64ToReg64 { src: imm.to_imm64(layout), dst: *reg_dst }]
						},
						ImmRich::Imm32(imm) => {
							if imm.is_signed() {
								vec![X8664Instr::MovImm32ToRegOrMem64 {
									src: imm.to_imm32(layout),
									dst: RegOrMem64::Reg64(*reg_dst),
								}]
							} else {
								vec![X8664Instr::MovImm32ToReg32 {
									src: imm.to_imm32(layout),
									dst: reg_dst.to_32(),
								}]
							}
						},
						ImmRich::Imm8(imm) => {
							if imm.is_signed() {
								// Note: The `MOV r/m64, imm8` variant does NOT sign extend the value
								// (see https://stackoverflow.com/q/11177137 for more info on that)
								// and we could use `MOVSX` to then sign extend the value
								// (this one does not have an imm variant) but that instruction is 4 bytes
								// and we only save 3 bytes by using `MOV r/m64, imm8`.
								// In the end it would be one byte longer so it is not worth it.
								vec![X8664Instr::MovImm32ToRegOrMem64 {
									src: imm.to_imm32(layout),
									dst: RegOrMem64::Reg64(*reg_dst),
								}]
							} else {
								let (reg_dst_id_high_bit, _reg_dst_id_low_3_bits) =
									separate_bit_b_in_bxxx(reg_dst.id());
								let need_rex_r_bit = reg_dst_id_high_bit == Bit::_1;
								if need_rex_r_bit {
									// The two REX prefixes needed in this case if we happened to
									// do here like in the last case happen to make is the same size
									// but two instructions instead of one, so it is not worth it.
									// This is better.
									vec![X8664Instr::MovImm32ToReg32 {
										src: imm.to_imm32(layout),
										dst: reg_dst.to_32(),
									}]
								} else {
									// Note: `MOV r8, imm8` does NOT zero extend the value, so we zero the
									// desination register first with the good old xor reg reg.
									// There is no need to use the 64 bits XOR variant because the 32 bits variant
									// zero extends the result anyway, so we can spare the REX prefix if the register
									// doesn't need the REX.R bit. Dependeing on the register, the XOR
									// takes either 2 or 3 bytes, so we actually spare either 0 or 1 byte
									// so it is worth it.
									vec![
										X8664Instr::XorRegOrMem32ToReg32 {
											src: RegOrMem32::Reg32(reg_dst.to_32()),
											dst: reg_dst.to_32(),
										},
										X8664Instr::MovImm8ToReg8 {
											src: imm.to_imm8(layout),
											dst: reg_dst.to_8(),
										},
									]
								}
							}
						},
					}
				}
			},
			AsmInstr::MovDerefReg64ToReg64 { src_size, src_sign, reg_as_ptr_src, reg_dst } => {
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

				let instr: X8664Instr = match (src_size, src_sign) {
					(BaseSize::Size64, _) => X8664Instr::MovRegOrMem64ToReg64 {
						src: RegOrMem64::DerefReg64(*reg_as_ptr_src),
						dst: *reg_dst,
					},
					(BaseSize::Size32, BaseSign::Unsigned) => X8664Instr::MovRegOrMem32ToReg32 {
						src: RegOrMem32::DerefReg32(reg_as_ptr_src.to_32()),
						dst: reg_dst.to_32(),
					},
					(BaseSize::Size32, BaseSign::Signed) => X8664Instr::MovsxdRegOrMem32ToReg64 {
						src: RegOrMem32::DerefReg32(reg_as_ptr_src.to_32()),
						dst: *reg_dst,
					},
					(BaseSize::Size8, BaseSign::Unsigned) => X8664Instr::MovsxRegOrMem8ToReg64 {
						src: RegOrMem8::DerefReg8(reg_as_ptr_src.to_8()),
						dst: *reg_dst,
					},
					(BaseSize::Size8, BaseSign::Signed) => X8664Instr::MovzxRegOrMem8ToReg64 {
						src: RegOrMem8::DerefReg8(reg_as_ptr_src.to_8()),
						dst: *reg_dst,
					},
				};
				vec![instr]
			},
			AsmInstr::MovReg64ToDerefReg64 { dst_size, reg_src, reg_as_ptr_dst } => {
				assert!(
					*reg_as_ptr_dst != Reg64::Rsp && *reg_as_ptr_dst != Reg64::Rbp,
					"The addressing forms with the ModR/M byte look a bit funky \
					for these registers, maybe just move the address to dereference \
					to an other register..."
				);
				// TODO: Deal with RSP and RBP here if it is feasable

				let instr = match dst_size {
					BaseSize::Size64 => X8664Instr::MovReg64ToRegOrMem64 {
						src: *reg_src,
						dst: RegOrMem64::DerefReg64(*reg_as_ptr_dst),
					},
					BaseSize::Size32 => X8664Instr::MovReg32ToRegOrMem32 {
						src: reg_src.to_32(),
						dst: RegOrMem32::DerefReg32(reg_as_ptr_dst.to_32()),
					},
					BaseSize::Size8 => X8664Instr::MovReg8ToRegOrMem8 {
						src: reg_src.to_8(),
						dst: RegOrMem8::DerefReg8(reg_as_ptr_dst.to_8()),
					},
				};
				vec![instr]
			},
			AsmInstr::PushReg64 { reg_src } => vec![X8664Instr::PushReg64(*reg_src)],
			AsmInstr::PopToReg64 { reg_dst } => vec![X8664Instr::PopReg64(*reg_dst)],
			AsmInstr::AddReg64ToReg64 { reg_src, reg_dst } => {
				vec![X8664Instr::AddReg64ToRegOrMem64 {
					src: *reg_src,
					dst: RegOrMem64::Reg64(*reg_dst),
				}]
			},
			AsmInstr::Syscall => vec![X8664Instr::Syscall],
			AsmInstr::Illegal => vec![X8664Instr::Ud2],
			AsmInstr::Label { .. } => vec![],
			AsmInstr::JumpToLabel { label_name } => {
				// The (relative) (signed) displacement is from the address of
				// the instruction that follows the jump instruction.
				let next_instr_address = instr_address + self.machine_code_size();
				let label_address = layout.code_label_address_table[label_name];
				let displacement = (label_address as isize - next_instr_address as isize) as i32;
				vec![X8664Instr::JmpRel32(Rel32(displacement))]
			},
		}
	}

	// TODO: make the size and the instr emitting at the same place! its duplicated logic! aaaaa
	pub(crate) fn machine_code_size(&self) -> usize {
		match self {
			AsmInstr::MovImmToReg64 { imm_src, reg_dst } => {
				let need_rex_r_bit = reg_dst.id_higher_bit() == Bit::_1;
				if imm_src.is_value_zero() {
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
			AsmInstr::PushReg64 { reg_src: reg } | AsmInstr::PopToReg64 { reg_dst: reg } => {
				let need_rex_r_bit = reg.id_higher_bit() == Bit::_1;
				1 + if need_rex_r_bit { 1 } else { 0 }
			},
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
	fn get(imm_src: &ImmRich, reg_dst: &Reg64) -> Self {
		match imm_src {
			ImmRich::Imm64(imm64) => {
				// `MOV r64, imm64`
				Self {
					rex_w: Bit::_1,
					imm_size_in_bytes: 8,
					signed_32: false,
					zero_before_and_8: false,
				}
			},
			ImmRich::Imm32(imm32) => {
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
			ImmRich::Imm8(imm8) => {
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
