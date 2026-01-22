use crate::{
	asm::{Bit, Reg64, U3, U4, separate_bit_b_in_bxxx},
	x86_64::{opcode_with_reg::OpcodeWithU3Reg, rex_prefix::RexPrefix},
};

/// Exactly one x86_64 instruction, with arguments and the choice of a specific variant and all.
///
/// It is ready, in a vacuum, to be encoded in its binary machine code representation,
/// of a known fixed size.
enum X8664Instr {
	/// - Variant: `PUSH r64`
	/// - Opcode: `50+rd`
	/// - No need for a REX.W bit since default operand size is 64 bits
	///   (it is impossible to encode `PUSH r32` in 64-bit mode).
	PushReg64(Reg64),
	// TODO: get all of `AsmInstr` variants in here.
}

impl X8664Instr {
	fn to_machine_code(&self) -> X8664InstrAsMachineCode {
		match self {
			X8664Instr::PushReg64(reg) => {
				let (reg_high_bit, reg_lower_u3) = separate_bit_b_in_bxxx(reg.id());
				let rex = RexPrefix::from_bits(0, 0, 0, reg_high_bit);
				let rex = Some(rex).filter(|&rex| RexPrefix::is_useful(rex));
				let opcode = Opcode::from_opcode_and_reg(0x50, reg_lower_u3);
				X8664InstrAsMachineCode { rex, opcode }
			},
		}
	}
}

impl std::fmt::Display for X8664Instr {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			X8664Instr::PushReg64(reg) => {
				write!(f, "push q %{reg}")
			},
		}
	}
}

mod rex_prefix {
	use crate::asm::{Bit, U4};

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
		pub(crate) fn from_bits(w: Bit, r: Bit, x: Bit, b: Bit) -> RexPrefix {
			assert!(w <= 1);
			assert!(r <= 1);
			assert!(x <= 1);
			assert!(b <= 1);
			RexPrefix { wrxb: (w << 3) | (r << 2) | (x << 1) | b }
		}

		pub(crate) fn to_byte(self) -> u8 {
			(0b0100 << 4) | self.wrxb
		}

		/// If `false` then it is (in most cases) safe to just omit this REX prefix as it doesn't do anything
		/// (when all 4 bits of the payload are 0).
		///
		/// This is not *always* the case though, some instructions (operating with 8 bits operands)
		/// react to the presence of a REX prefix independently of its payload
		/// (it changes which registers are represented by some register codes, the effect is somewhat niche).
		pub(crate) fn is_useful(self) -> bool {
			self.wrxb != 0
		}

		pub(crate) fn w(self) -> Bit {
			self.wrxb >> 3
		}
		pub(crate) fn r(self) -> Bit {
			(self.wrxb >> 2) & 1
		}
		pub(crate) fn x(self) -> Bit {
			(self.wrxb >> 1) & 1
		}
		pub(crate) fn b(self) -> Bit {
			self.wrxb & 1
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
	use crate::asm::U3;

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
			assert!(reg_code_lower_u3 <= 0b111);
			OpcodeWithU3Reg(opcode_with_reg_as_zero | reg_code_lower_u3)
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
