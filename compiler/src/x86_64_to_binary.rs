use crate::{
	highasm::{
		Reg8, Reg32, Reg64, RegOrMem8, RegOrMem32, RegOrMem64,
		small_uints::{Bit, U2, U3},
	},
	imm::Value32,
	x86_64::{Imm, Imm32, X8664Instr},
	x86_64_to_binary::{
		modrm_byte::ModRmByte, opcode_with_reg::OpcodeWithU3Reg, rex_prefix::RexPrefix,
	},
};

impl X8664Instr {
	pub(crate) fn to_machine_code(&self) -> X8664InstrAsMachineCode {
		match self {
			X8664Instr::PushReg64(reg) => {
				let rex_w = Bit::_0;
				let opcode_without_reg = 0x50;
				let opcode = Opcode::from_opcode_and_reg(opcode_without_reg, reg.id_lower_u3());
				let rex = RexPrefix::new(rex_w, Bit::_0, Bit::_0, reg.id_higher_bit()).keep_if_useful();
				X8664InstrAsMachineCode { rex, opcode, modrm: None, imm: None }
			},
			X8664Instr::PopReg64(reg) => {
				let rex_w = Bit::_0;
				let opcode_without_reg = 0x58;
				let opcode = Opcode::from_opcode_and_reg(opcode_without_reg, reg.id_lower_u3());
				let rex = RexPrefix::new(rex_w, Bit::_0, Bit::_0, reg.id_higher_bit()).keep_if_useful();
				X8664InstrAsMachineCode { rex, opcode, modrm: None, imm: None }
			},
			X8664Instr::XorRegOrMem32ToReg32 { src, dst } => {
				let rex_w = Bit::_0;
				let opcode = Opcode::from_byte(0x33);
				let RegOrMem32::Reg32(src) = src else {
					unimplemented!("deref not implemented yet here");
				};
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
				let RegOrMem64::Reg64(src) = src else {
					unimplemented!("deref not implemented yet here");
				};
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
				let RegOrMem64::Reg64(dst) = dst else {
					unimplemented!("deref not implemented yet here");
				};
				let modrm = Some(ModRmByte::new(
					U2::new(0b11),
					U3::new(0), // `/0` in the "opcode" encoding spec
					dst.id_lower_u3(),
				));
				let imm = Some(Imm::Imm32(*src));
				let rex = RexPrefix::new(rex_w, Bit::_0, Bit::_0, dst.id_higher_bit()).keep_if_useful();
				X8664InstrAsMachineCode { rex, opcode, modrm, imm }
			},
			X8664Instr::MovRegOrMem64ToReg64 { src, dst } => {
				let rex_w = Bit::_1;
				let opcode = Opcode::from_byte(0x8b);
				let RegOrMem64::DerefReg64(src) = src else {
					unimplemented!("NON-deref not implemented yet here");
				};
				assert!(
					![Reg64::Rsp, Reg64::Rbp, Reg64::R12, Reg64::R13].contains(src),
					"RSP,RBP,R12,R13 are not supported yet, ill cook some SIB byte thing with 0 disp or something"
				);
				let modrm = Some(ModRmByte::new(
					U2::new(0b00),
					dst.id_lower_u3(),
					src.id_lower_u3(),
				));
				let rex = RexPrefix::new(rex_w, dst.id_higher_bit(), Bit::_0, src.id_higher_bit())
					.keep_if_useful();
				X8664InstrAsMachineCode { rex, opcode, modrm, imm: None }
			},
			X8664Instr::MovRegOrMem32ToReg32 { src, dst } => {
				let rex_w = Bit::_0;
				let opcode = Opcode::from_byte(0x8b);
				let RegOrMem32::DerefReg32(src) = src else {
					unimplemented!("NON-deref not implemented yet here");
				};
				assert!(
					![Reg32::Esp, Reg32::Ebp, Reg32::R12d, Reg32::R13d].contains(src),
					"ESP,EBP,R12D,R13D are not supported yet, ill cook some SIB byte thing with 0 disp or something"
				);
				let modrm = Some(ModRmByte::new(
					U2::new(0b00),
					dst.id_lower_u3(),
					src.id_lower_u3(),
				));
				let rex = RexPrefix::new(rex_w, dst.id_higher_bit(), Bit::_0, src.id_higher_bit())
					.keep_if_useful();
				X8664InstrAsMachineCode { rex, opcode, modrm, imm: None }
			},
			X8664Instr::MovsxdRegOrMem32ToReg64 { src, dst } => {
				let rex_w = Bit::_1;
				let opcode = Opcode::from_byte(0x63);
				let RegOrMem32::DerefReg32(src) = src else {
					unimplemented!("NON-deref not implemented yet here");
				};
				assert!(
					![Reg32::Esp, Reg32::Ebp, Reg32::R12d, Reg32::R13d].contains(src),
					"ESP,EBP,R12D,R13D are not supported yet, ill cook some SIB byte thing with 0 disp or something"
				);
				let modrm = Some(ModRmByte::new(
					U2::new(0b00),
					dst.id_lower_u3(),
					src.id_lower_u3(),
				));
				let rex = RexPrefix::new(rex_w, dst.id_higher_bit(), Bit::_0, src.id_higher_bit())
					.keep_if_useful();
				X8664InstrAsMachineCode { rex, opcode, modrm, imm: None }
			},
			X8664Instr::MovsxRegOrMem8ToReg64 { src, dst } => {
				let rex_w = Bit::_1;
				let opcode = Opcode::from_two_bytes([0x0f, 0xbe]);
				let RegOrMem8::DerefReg8(src) = src else {
					unimplemented!("NON-deref not implemented yet here");
				};
				assert!(
					![Reg8::Spl, Reg8::Bpl, Reg8::R12b, Reg8::R13b].contains(src),
					"SPL,BPL,R12B,R13B are not supported yet, ill cook some SIB byte thing with 0 disp or something"
				);
				let modrm = Some(ModRmByte::new(
					U2::new(0b00),
					dst.id_lower_u3(),
					src.id_lower_u3(),
				));
				let rex = RexPrefix::new(rex_w, dst.id_higher_bit(), Bit::_0, src.id_higher_bit())
					.keep_if_useful();
				X8664InstrAsMachineCode { rex, opcode, modrm, imm: None }
			},
			X8664Instr::MovzxRegOrMem8ToReg64 { src, dst } => {
				let rex_w = Bit::_1;
				let opcode = Opcode::from_two_bytes([0x0f, 0xb6]);
				let RegOrMem8::DerefReg8(src) = src else {
					unimplemented!("NON-deref not implemented yet here");
				};
				assert!(
					![Reg8::Spl, Reg8::Bpl, Reg8::R12b, Reg8::R13b].contains(src),
					"SPL,BPL,R12B,R13B are not supported yet, ill cook some SIB byte thing with 0 disp or something"
				);
				let modrm = Some(ModRmByte::new(
					U2::new(0b00),
					dst.id_lower_u3(),
					src.id_lower_u3(),
				));
				let rex = RexPrefix::new(rex_w, dst.id_higher_bit(), Bit::_0, src.id_higher_bit())
					.keep_if_useful();
				X8664InstrAsMachineCode { rex, opcode, modrm, imm: None }
			},
			X8664Instr::MovReg64ToRegOrMem64 { src, dst } => {
				let rex_w = Bit::_1;
				let opcode = Opcode::from_byte(0x89);
				let RegOrMem64::DerefReg64(dst) = dst else {
					unimplemented!("NON-deref not implemented yet here");
				};
				assert!(
					![Reg64::Rsp, Reg64::Rbp, Reg64::R12, Reg64::R13].contains(dst),
					"RSP,RBP,R12,R13 are not supported yet, ill cook some SIB byte thing with 0 disp or something"
				);
				let modrm = Some(ModRmByte::new(
					U2::new(0b00),
					src.id_lower_u3(),
					dst.id_lower_u3(),
				));
				let rex = RexPrefix::new(rex_w, src.id_higher_bit(), Bit::_0, dst.id_higher_bit())
					.keep_if_useful();
				X8664InstrAsMachineCode { rex, opcode, modrm, imm: None }
			},
			X8664Instr::MovReg32ToRegOrMem32 { src, dst } => {
				let rex_w = Bit::_0;
				let opcode = Opcode::from_byte(0x89);
				let RegOrMem32::DerefReg32(dst) = dst else {
					unimplemented!("NON-deref not implemented yet here");
				};
				assert!(
					![Reg32::Esp, Reg32::Ebp, Reg32::R12d, Reg32::R13d].contains(dst),
					"ESP,EBP,R12D,R13D are not supported yet, ill cook some SIB byte thing with 0 disp or something"
				);
				let modrm = Some(ModRmByte::new(
					U2::new(0b00),
					src.id_lower_u3(),
					dst.id_lower_u3(),
				));
				let rex = RexPrefix::new(rex_w, src.id_higher_bit(), Bit::_0, dst.id_higher_bit())
					.keep_if_useful();
				X8664InstrAsMachineCode { rex, opcode, modrm, imm: None }
			},
			X8664Instr::MovReg8ToRegOrMem8 { src, dst } => {
				let rex_w = Bit::_0;
				let opcode = Opcode::from_byte(0x88);
				let RegOrMem8::DerefReg8(dst) = dst else {
					unimplemented!("NON-deref not implemented yet here");
				};
				assert!(
					![Reg8::Spl, Reg8::Bpl, Reg8::R12b, Reg8::R13b].contains(dst),
					"SPL,BPL,R12B,R13B are not supported yet, ill cook some SIB byte thing with 0 disp or something"
				);
				let modrm = Some(ModRmByte::new(
					U2::new(0b00),
					src.id_lower_u3(),
					dst.id_lower_u3(),
				));
				let rex = RexPrefix::new(rex_w, src.id_higher_bit(), Bit::_0, dst.id_higher_bit())
					.keep_if_useful();
				X8664InstrAsMachineCode { rex, opcode, modrm, imm: None }
			},
			X8664Instr::AddReg64ToRegOrMem64 { src, dst } => {
				let rex_w = Bit::_1;
				let opcode = Opcode::from_byte(0x01);
				let RegOrMem64::Reg64(dst) = dst else {
					unimplemented!("deref not implemented yet here");
				};
				let modrm = Some(ModRmByte::new(
					U2::new(0b11),
					src.id_lower_u3(),
					dst.id_lower_u3(),
				));
				let rex = RexPrefix::new(rex_w, src.id_higher_bit(), Bit::_0, dst.id_higher_bit())
					.keep_if_useful();
				X8664InstrAsMachineCode { rex, opcode, modrm, imm: None }
			},
			X8664Instr::Syscall => {
				let opcode = Opcode::from_two_bytes([0x0f, 0x05]);
				X8664InstrAsMachineCode { rex: None, opcode, modrm: None, imm: None }
			},
			X8664Instr::Ud2 => {
				let opcode = Opcode::from_two_bytes([0x0f, 0x0b]);
				X8664InstrAsMachineCode { rex: None, opcode, modrm: None, imm: None }
			},
			X8664Instr::JmpRel32(offset) => {
				let opcode = Opcode::from_byte(0xe9);
				let imm = Some(Imm::Imm32(Imm32::from_u32(offset.to_u32())));
				X8664InstrAsMachineCode { rex: None, opcode, modrm: None, imm }
			},
		}
	}
}

mod rex_prefix {
	use crate::highasm::small_uints::{Bit, U4};

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
	use crate::highasm::small_uints::{U2, U3};

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
	use crate::highasm::small_uints::U3;

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
struct OpcodeTwoBytes([u8; 2]);

impl OpcodeTwoBytes {
	fn to_bytes(self) -> [u8; 2] {
		self.0
	}
}

#[derive(Clone, Copy)]
enum Opcode {
	OneByte(OpcodeOneByte),
	WithU3Reg(OpcodeWithU3Reg),
	TwoBytes(OpcodeTwoBytes),
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

	fn from_two_bytes(opcode_bytes: [u8; 2]) -> Opcode {
		Opcode::TwoBytes(OpcodeTwoBytes(opcode_bytes))
	}

	fn to_bytes(self) -> Vec<u8> {
		match self {
			Opcode::OneByte(o) => vec![o.to_byte()],
			Opcode::WithU3Reg(o) => vec![o.to_byte()],
			Opcode::TwoBytes(o) => Vec::from(o.to_bytes()),
		}
	}
}

pub(crate) struct X8664InstrAsMachineCode {
	rex: Option<RexPrefix>,
	opcode: Opcode,
	modrm: Option<ModRmByte>,
	imm: Option<Imm>,
}

impl X8664InstrAsMachineCode {
	pub(crate) fn to_binary(&self) -> Vec<u8> {
		let mut binary = vec![];
		if let Some(rex) = self.rex {
			binary.push(rex.to_byte());
		}
		binary.append(&mut self.opcode.to_bytes());
		if let Some(modrm) = self.modrm {
			binary.push(modrm.to_byte());
		}
		if let Some(imm) = self.imm {
			binary.append(&mut imm.to_bytes());
		}
		binary
	}
}
