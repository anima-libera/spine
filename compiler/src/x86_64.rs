use crate::{
	asm::{
		Reg64, separate_bit_b_in_bxxx,
		small_uints::{Bit, U3, U4},
	},
	x86_64::{opcode_with_reg::OpcodeWithU3Reg, rex_prefix::RexPrefix},
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
	// TODO: get all of `AsmInstr` variants in here.
}

impl X8664Instr {
	fn to_machine_code(&self) -> X8664InstrAsMachineCode {
		match self {
			X8664Instr::PushReg64(reg) | X8664Instr::PopReg64(reg) => {
				let rex =
					RexPrefix::new(Bit::_0, Bit::_0, Bit::_0, reg.id_higher_bit()).keep_if_useful();
				let opcode_without_reg = match self {
					X8664Instr::PushReg64(_) => 0x50,
					X8664Instr::PopReg64(_) => 0x58,
					_ => unreachable!(),
				};
				let opcode = Opcode::from_opcode_and_reg(opcode_without_reg, reg.id_lower_u3());
				X8664InstrAsMachineCode { rex, opcode }
			},
		}
	}
}

impl std::fmt::Display for X8664Instr {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			X8664Instr::PushReg64(reg) => write!(f, "push q %{reg}"),
			X8664Instr::PopReg64(reg) => write!(f, "pop q %{reg}"),
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
	#[derive(Clone, Copy)]
	pub(crate) struct RexPrefix {
		wrxb: U4,
	}

	impl RexPrefix {
		pub(crate) fn new(w: Bit, r: Bit, x: Bit, b: Bit) -> RexPrefix {
			RexPrefix {
				wrxb: U4::new((w.as_u8() << 3) | (r.as_u8() << 2) | (x.as_u8() << 1) | b.as_u8()),
			}
		}

		pub(crate) fn to_byte(self) -> u8 {
			(0b0100 << 4) | self.wrxb.as_u8()
		}

		/// If `false` then it is (in most cases) safe to just omit this REX prefix as it doesn't do anything
		/// (when all 4 bits of the payload are 0).
		///
		/// This is not *always* the case though, some instructions (operating with 8 bits operands)
		/// react to the presence of a REX prefix independently of its payload
		/// (it changes which registers are represented by some register codes, the effect is somewhat niche).
		pub(crate) fn is_useful(self) -> bool {
			self.wrxb.as_u8() != 0
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

struct X8664InstrAsMachineCode {
	rex: Option<RexPrefix>,
	opcode: Opcode,
}

impl X8664InstrAsMachineCode {
	fn to_binary(&self) -> Vec<u8> {
		let mut binary = vec![];
		if let Some(rex) = self.rex {
			binary.push(rex.to_byte());
		}
		binary.push(self.opcode.to_byte());
		binary
	}
}
