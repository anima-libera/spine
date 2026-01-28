use crate::{
	asm::{
		Reg8, Reg32, Reg64, RegOrMem32, RegOrMem64, separate_bit_b_in_bxxx,
		small_uints::{Bit, U2, U3, U4},
	},
	imm::{ImmRich64, Value64},
	x86_64::{modrm_byte::ModRmByte, opcode_with_reg::OpcodeWithU3Reg, rex_prefix::RexPrefix},
};

/// Exactly one x86_64 instruction, with arguments and the choice of a specific variant and all.
///
/// It is ready to be encoded in its binary machine code representation,
/// of a known fixed size,
/// without additional infirmation (meaning it already has all the info it needs).
enum X8664Instr {
	/// - Mnemonic: `PUSH`
	/// - Variant: `PUSH r64`
	/// - Opcode: `50+rd`
	/// - No need for a REX.W bit since default operand size is 64 bits
	///   (it is impossible to encode `PUSH r32` in 64-bit mode).
	///
	/// Pushes the content of the register on top of the stack, making the stack 64 bits taller.
	PushReg64(Reg64),
	/// - Mnemonic: `POP`
	/// - Variant: `POP r64`
	/// - Opcode: `58+rd`
	/// - No need for a REX.W bit since default operand size is 64 bits
	///   (it is impossible to encode `POP r32` in 64-bit mode).
	///
	/// Pops the top 64 bits value from the top of the stack and writes it in the register,
	/// making the stack 64 bits smaller.
	PopReg64(Reg64),
	/// - Mnemonic: `XOR`
	/// - Variant: `XOR r32, r/m32` (dst, src)
	/// - Opcode: `33 /r`
	/// - What-extended: **zero-extended** (if destination is a register)
	/// - Can be used to zero a 64 bits register since it zero-extends the destination register.
	///
	/// Does a bitwise xor of the 32 bits arguments and writes it in the 32 bits destination register/area.
	/// If the destination is a 32 bits register then the result is
	/// zero-extended in the encompassing 64 bits register.
	XorRegOrMem32ToReg32 { src: RegOrMem32, dst: Reg32 },
	/// - Mnemonic: `XOR`
	/// - Variant: `XOR r64, r/m64` (dst, src)
	/// - Opcode: `REX.W + 33 /r`
	///
	/// Does a bitwise xor of the arguments and writes it in the destination register.
	XorRegOrMem64ToReg64 { src: RegOrMem64, dst: Reg64 },
	/// - Mnemonic: `MOV`
	/// - Variant: `MOV r64, imm64` (dst, src)
	/// - Opcode: `REX.W + B8+ ro io`
	///
	/// Sets the register to the immediate value.
	MovImm64ToReg64 { src: Imm64, dst: Reg64 },
	/// - Mnemonic: `MOV`
	/// - Variant: `MOV r32, imm32` (dst, src)
	/// - Opcode: `B8+ rd id`
	/// - What-extended: **zero-extended**
	///
	/// Sets the 32 bits register to the immediate value,
	/// zero-extending the value in the encompassing 64 bits register.
	MovImm32ToReg32 { src: Imm32, dst: Reg32 },
	/// - Mnemonic: `MOV`
	/// - Variant: `MOV r8, imm8`
	/// - Opcode: `B0+ rb ib`
	///
	/// Sets the 8 bits register to the immediate value.
	MovImm8ToReg8 { src: Imm8, dst: Reg8 },
	/// - Mnemonic: `MOV`
	/// - Variant: `MOV r/m64, imm32`
	/// - Opcode: `REX.W + C7 /0 id`
	/// - What-extended: **sign-extended**
	///
	/// Sets the 64 bits register/area to the 32 bits immediate value sign-extended to 64 bits.
	MovImm32ToRegOrMem64 { src: Imm32, dst: RegOrMem64 },
	// TODO: get all of `AsmInstr` variants in here.
}

impl X8664Instr {
	fn to_machine_code(&self) -> X8664InstrAsMachineCode {
		match self {
			X8664Instr::PushReg64(reg) | X8664Instr::PopReg64(reg) => {
				let rex_w = Bit::_0;
				let opcode_without_reg = match self {
					X8664Instr::PushReg64(_) => 0x50,
					X8664Instr::PopReg64(_) => 0x58,
					_ => unreachable!(),
				};
				let opcode = Opcode::from_opcode_and_reg(opcode_without_reg, reg.id_lower_u3());
				let rex = RexPrefix::new(rex_w, Bit::_0, Bit::_0, reg.id_higher_bit()).keep_if_useful();
				X8664InstrAsMachineCode { rex, opcode, modrm: None, imm: None }
			},
			X8664Instr::XorRegOrMem32ToReg32 { src, dst } => {
				let rex_w = Bit::_0;
				let opcode = Opcode::from_byte(0x33);
				let RegOrMem32::Reg32(src) = src; // deref not implemented yet
				let modrm = Some(ModRmByte::new(
					U2::new(0b11),
					dst.id_lower_u3(),
					src.id_lower_u3(),
				));
				let rex = RexPrefix::new(rex_w, dst.id_higher_bit(), Bit::_0, src.id_higher_bit())
					.keep_if_useful();
				X8664InstrAsMachineCode { rex, opcode, modrm, imm: None }
			},
			X8664Instr::XorRegOrMem64ToReg64 { src, dst } => {
				let rex_w = Bit::_1;
				let opcode = Opcode::from_byte(0x33);
				let RegOrMem64::Reg64(src) = src; // deref not implemented yet
				let modrm = Some(ModRmByte::new(
					U2::new(0b11),
					dst.id_lower_u3(),
					src.id_lower_u3(),
				));
				let rex = RexPrefix::new(rex_w, dst.id_higher_bit(), Bit::_0, src.id_higher_bit())
					.keep_if_useful();
				X8664InstrAsMachineCode { rex, opcode, modrm, imm: None }
			},
			X8664Instr::MovImm64ToReg64 { src, dst } => {
				let rex_w = Bit::_1;
				let opcode_without_reg = 0xb8;
				let opcode = Opcode::from_opcode_and_reg(opcode_without_reg, dst.id_lower_u3());
				let imm = Some(Imm::Imm64(*src));
				let rex = RexPrefix::new(rex_w, Bit::_0, Bit::_0, dst.id_higher_bit()).keep_if_useful();
				X8664InstrAsMachineCode { rex, opcode, modrm: None, imm }
			},
			X8664Instr::MovImm32ToReg32 { src, dst } => {
				let rex_w = Bit::_0;
				let opcode_without_reg = 0xb8;
				let opcode = Opcode::from_opcode_and_reg(opcode_without_reg, dst.id_lower_u3());
				let imm = Some(Imm::Imm32(*src));
				let rex = RexPrefix::new(rex_w, Bit::_0, Bit::_0, dst.id_higher_bit()).keep_if_useful();
				X8664InstrAsMachineCode { rex, opcode, modrm: None, imm }
			},
			X8664Instr::MovImm8ToReg8 { src, dst } => {
				let rex_w = Bit::_0;
				let opcode_without_reg = 0xb0;
				let opcode = Opcode::from_opcode_and_reg(opcode_without_reg, dst.id_lower_u3());
				let imm = Some(Imm::Imm8(*src));
				let rex = RexPrefix::new_maybe_required_for_8bit_reg(
					rex_w,
					Bit::_0,
					Bit::_0,
					dst.id_higher_bit(),
					dst.is_rex_required(),
				)
				.keep_if_useful();
				X8664InstrAsMachineCode { rex, opcode, modrm: None, imm }
			},
			X8664Instr::MovImm32ToRegOrMem64 { src, dst } => {
				let rex_w = Bit::_1;
				let opcode = Opcode::from_byte(0xc7);
				let RegOrMem64::Reg64(dst) = dst; // deref not implemented yet
				let modrm = Some(ModRmByte::new(
					U2::new(0b11),
					U3::new(0), // `/0` in the "opcode" encoding spec
					dst.id_lower_u3(),
				));
				let imm = Some(Imm::Imm32(*src));
				let rex = RexPrefix::new(rex_w, Bit::_0, Bit::_0, dst.id_higher_bit()).keep_if_useful();
				X8664InstrAsMachineCode { rex, opcode, modrm, imm }
			},
		}
	}
}

impl std::fmt::Display for X8664Instr {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		// Format is `mnemonic arguments...`, like `push reg q %rax`.
		//
		// Size indications are:
		// - `b` for 8 bits (Byte)
		// - `w` for 16 bits (Word)
		// - `d` for 32 bits (Double-word)
		// - `q` for 64 bits (Quad-word)
		//
		// Arguments are like `reg q %rax`, `reg/mem d %r11d`
		// We mention the operand type (reg, r/m, etc.) as it actually is
		// for the instruction encoding variant that is actually used;
		// simply "mov %rbx -> %rcx" would be ambiguous
		// in which variant is used (r/m -> reg or reg -> r/m).
		//
		// We use an arrow `->` to make it clear which operand is the destination,
		// because im tired of intel syntax vs at&t syntax so here is an actually clear syntax instead.
		//
		// When a value is zero-extended or sign-extended it is clearly indicated
		// by `zx` or `sx` respectively.
		// - If writing to a 32 bits register actually writes to the corresponding 64 bits register
		//   with zero-extension or sign-extension it is written with the name of the 64 bits register
		//   like `... -> reg d %eax zx q %rax`.
		// - If an immediate value is extended before being used in some operation it is written too
		//   like `imm d 0xffffffff sx q -> ...`.
		match self {
			X8664Instr::PushReg64(reg) => write!(f, "push reg q {reg}"),
			X8664Instr::PopReg64(reg) => write!(f, "pop reg q {reg}"),
			X8664Instr::XorRegOrMem32ToReg32 { src, dst } => {
				let dst64 = dst.to_64_bits();
				write!(f, "xor reg/mem d {src} -> reg d {dst} zx q {dst64}")
			},
			X8664Instr::XorRegOrMem64ToReg64 { src, dst } => {
				write!(f, "xor reg/mem q {src} -> reg q {dst}")
			},
			X8664Instr::MovImm64ToReg64 { src, dst } => {
				let src_value = src.0;
				write!(f, "mov imm q {src_value:#016x} -> reg q {dst}")
			},
			X8664Instr::MovImm32ToReg32 { src, dst } => {
				let src_value = src.0;
				let dst64 = dst.to_64_bits();
				write!(f, "mov imm d {src_value:#08x} -> reg d {dst} zx q {dst64}")
			},
			X8664Instr::MovImm8ToReg8 { src, dst } => {
				let src_value = src.0;
				write!(f, "mov imm b {src_value:#02x} -> reg b {dst}")
			},
			X8664Instr::MovImm32ToRegOrMem64 { src, dst } => {
				let src_value = src.0;
				write!(f, "mov imm d {src_value:#08x} sx q -> reg/mem q {dst}")
			},
		}
	}
}

mod rex_prefix {
	use crate::asm::small_uints::{Bit, U4};

	/// REX prefix. It is optional, one byte, and comes just before the opcode bytes (last prefix).
	///
	/// Its format is `0100wrxb` (from high to low), where:
	/// - `w`: 1 means the instruction uses 64 bits operands, 0 means default size (not always 32 bits),
	/// - `r` is an extra high bit to expand ModR/M.reg from 3 to 4 bits,
	/// - `x` is an extra high bit to expand SIB.index from 3 to 4 bits,
	/// - `b` is an extra high bit to expand *something* from 3 to 4 bits, which is one of:
	///   - ModR/M.r/m
	///   - SIB.base
	///   - the register in the 3 low bits of the opcode byte.
	///
	/// Sometimes a REX prefix can change the meaning of register codes (for example for `MOV r8, imm8`
	/// the spec says that if there is a REX prefix (even without any paylod bit set) it will change
	/// the meaning of register codes 4-7 (including) to mean SPL,DIL,BPL,SIL instead of AH,BH,CH,DH).
	/// If this is the case, this information is contained in here too, as it is used to determine
	/// if the REX prefix is useful at all or can be safely omitted.
	#[derive(Clone, Copy)]
	pub(crate) struct RexPrefix {
		wrxb: U4,
		required_for_8bit_reg: bool,
	}

	impl RexPrefix {
		pub(crate) fn new(w: Bit, r: Bit, x: Bit, b: Bit) -> RexPrefix {
			RexPrefix {
				wrxb: U4::new((w.as_u8() << 3) | (r.as_u8() << 2) | (x.as_u8() << 1) | b.as_u8()),
				required_for_8bit_reg: false,
			}
		}

		pub(crate) fn new_maybe_required_for_8bit_reg(
			w: Bit,
			r: Bit,
			x: Bit,
			b: Bit,
			required_for_8bit_reg: bool,
		) -> RexPrefix {
			let mut rex = RexPrefix::new(w, r, x, b);
			rex.required_for_8bit_reg = required_for_8bit_reg;
			rex
		}

		pub(crate) fn to_byte(self) -> u8 {
			(0b0100 << 4) | self.wrxb.as_u8()
		}

		/// If `false` then it is safe to just omit this REX prefix as it doesn't do anything
		/// (when all 4 bits of the payload are 0, and when a REX prefix presence is not required).
		pub(crate) fn is_useful(self) -> bool {
			self.wrxb.as_u8() != 0 || self.required_for_8bit_reg
		}

		pub(crate) fn keep_if_useful(self) -> Option<RexPrefix> {
			self.is_useful().then_some(self)
		}

		pub(crate) fn w(self) -> Bit {
			Bit::new(self.wrxb.as_u8() >> 3)
		}
		pub(crate) fn r(self) -> Bit {
			Bit::new((self.wrxb.as_u8() >> 2) & 1)
		}
		pub(crate) fn x(self) -> Bit {
			Bit::new((self.wrxb.as_u8() >> 1) & 1)
		}
		pub(crate) fn b(self) -> Bit {
			Bit::new(self.wrxb.as_u8() & 1)
		}

		pub(crate) fn is_required_for_8bit_reg(self) -> bool {
			self.required_for_8bit_reg
		}
	}
}

mod modrm_byte {
	use crate::asm::small_uints::{U2, U3};

	// TODO: Add SIB byte thing, and couple it with Mod R/M byte thing, they make more sense together!

	/// Mod R/M byte. It is optional, one byte, and comes just after the opcode bytes
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
	#[derive(Clone, Copy)]
	pub(crate) struct ModRmByte {
		mod_: U2,
		reg: U3,
		rm: U3,
	}

	impl ModRmByte {
		pub(crate) fn new(mod_: U2, reg: U3, rm: U3) -> ModRmByte {
			ModRmByte { mod_, reg, rm }
		}

		pub(crate) fn to_byte(self) -> u8 {
			(self.mod_.as_u8() << 6) | (self.reg.as_u8() << 3) | self.rm.as_u8()
		}

		pub(crate) fn mod_(self) -> U2 {
			self.mod_
		}
		pub(crate) fn reg(self) -> U3 {
			self.reg
		}
		pub(crate) fn rm(self) -> U3 {
			self.rm
		}
	}
}

#[derive(Clone, Copy)]
struct OpcodeOneByte(u8);

impl OpcodeOneByte {
	fn to_byte(self) -> u8 {
		self.0
	}
}

mod opcode_with_reg {
	use crate::asm::small_uints::U3;

	/// Opcode that fits in 5 bits and the 3 bits (lower bits) of a register code, in one byte.
	///
	/// The bits are `ooooorrr`.
	#[derive(Clone, Copy)]
	pub(crate) struct OpcodeWithU3Reg(u8);

	impl OpcodeWithU3Reg {
		pub(crate) fn from_opcode_and_reg(
			opcode_with_reg_as_zero: u8,
			reg_code_lower_u3: U3,
		) -> OpcodeWithU3Reg {
			assert!((opcode_with_reg_as_zero & 0b111) == 0);
			OpcodeWithU3Reg(opcode_with_reg_as_zero | reg_code_lower_u3.as_u8())
		}

		pub(crate) fn to_byte(self) -> u8 {
			self.0
		}
	}
}

#[derive(Clone, Copy)]
enum Opcode {
	OneByte(OpcodeOneByte),
	WithU3Reg(OpcodeWithU3Reg),
}

impl Opcode {
	fn from_byte(opcode: u8) -> Opcode {
		Opcode::OneByte(OpcodeOneByte(opcode))
	}

	fn from_opcode_and_reg(opcode_with_reg_as_zero: u8, reg_code_lower_u3: U3) -> Opcode {
		Opcode::WithU3Reg(OpcodeWithU3Reg::from_opcode_and_reg(
			opcode_with_reg_as_zero,
			reg_code_lower_u3,
		))
	}

	fn to_byte(self) -> u8 {
		match self {
			Opcode::OneByte(o) => o.to_byte(),
			Opcode::WithU3Reg(o) => o.to_byte(),
		}
	}
}

#[derive(Clone, Copy)]
struct Imm64(u64);
#[derive(Clone, Copy)]
struct Imm32(u32);
#[derive(Clone, Copy)]
struct Imm8(u8);

impl Imm64 {
	fn to_bytes(self) -> Vec<u8> {
		Vec::from(self.0.to_le_bytes())
	}
}
impl Imm32 {
	fn to_bytes(self) -> Vec<u8> {
		Vec::from(self.0.to_le_bytes())
	}
}
impl Imm8 {
	fn to_bytes(self) -> Vec<u8> {
		Vec::from(self.0.to_le_bytes())
	}
}

/// An immediate value that is stripped of all details regarding its origin, no sign no nothing,
/// just the final value whose size and bytes are all we know and that will end up as-is in the binary.
#[derive(Clone, Copy)]
enum Imm {
	Imm64(Imm64),
	Imm32(Imm32),
	Imm8(Imm8),
}

impl Imm {
	fn to_bytes(self) -> Vec<u8> {
		match self {
			Imm::Imm64(imm) => imm.to_bytes(),
			Imm::Imm32(imm) => imm.to_bytes(),
			Imm::Imm8(imm) => imm.to_bytes(),
		}
	}

	fn to_u64(self) -> u64 {
		match self {
			Imm::Imm64(imm) => imm.0,
			Imm::Imm32(imm) => imm.0 as u64,
			Imm::Imm8(imm) => imm.0 as u64,
		}
	}
}

struct X8664InstrAsMachineCode {
	rex: Option<RexPrefix>,
	opcode: Opcode,
	modrm: Option<ModRmByte>,
	imm: Option<Imm>,
}

impl X8664InstrAsMachineCode {
	fn to_binary(&self) -> Vec<u8> {
		let mut binary = vec![];
		if let Some(rex) = self.rex {
			binary.push(rex.to_byte());
		}
		binary.push(self.opcode.to_byte());
		if let Some(modrm) = self.modrm {
			binary.push(modrm.to_byte());
		}
		if let Some(imm) = self.imm {
			binary.append(&mut imm.to_bytes());
		}
		binary
	}
}
