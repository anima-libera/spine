use crate::{
	highasm::{Reg8, Reg32, Reg64, RegOrMem8, RegOrMem32, RegOrMem64, Rel32},
	imm::{Value8, Value32, Value64},
};

/// Exactly one x86_64 instruction, with arguments and the choice of a specific variant and all.
///
/// It is ready to be encoded in its binary machine code representation,
/// of a known fixed size,
/// without additional infirmation (meaning it already has all the info it needs).
#[derive(Clone)]
pub enum X8664Instr {
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
	/// - Touches flags.
	/// - Can be used to zero a 64 bits register since it zero-extends the destination register.
	///
	/// Does a bitwise xor of the 32 bits arguments and writes it in the 32 bits destination register,
	/// zero-extending the result in the encompassing 64 bits register.
	XorRegOrMem32ToReg32 { src: RegOrMem32, dst: Reg32 },
	/// - Mnemonic: `XOR`
	/// - Variant: `XOR r64, r/m64` (dst, src)
	/// - Opcode: `REX.W + 33 /r`
	/// - Touches flags.
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
	/// - Variant: `MOV r8, imm8` (dst, src)
	/// - Opcode: `B0+ rb ib`
	///
	/// Sets the 8 bits register to the immediate value.
	MovImm8ToReg8 { src: Imm8, dst: Reg8 },
	/// - Mnemonic: `MOV`
	/// - Variant: `MOV r/m64, imm32` (dst, src)
	/// - Opcode: `REX.W + C7 /0 id`
	/// - What-extended: **sign-extended**
	///
	/// Sets the 64 bits register/area to the 32 bits immediate value sign-extended to 64 bits.
	MovImm32ToRegOrMem64 { src: Imm32, dst: RegOrMem64 },
	/// - Mnemonic: `MOV`
	/// - Variant: `MOV r64, r/m64` (dst, src)
	/// - Opcode: `REX.W + 8B /r`
	///
	/// Sets the destination register to the 64 bits value in the source register/area.
	MovRegOrMem64ToReg64 { src: RegOrMem64, dst: Reg64 },
	/// - Mnemonic: `MOV`
	/// - Variant: `MOV r32, r/m32` (dst, src)
	/// - Opcode: `8B /r`
	/// - What-extended: **zero-extended**
	///
	/// Sets the 32 bits destination register to the 32 bits value in the source register/area,
	/// zero-extending the value in the encompassing 64 bits destination register.
	MovRegOrMem32ToReg32 { src: RegOrMem32, dst: Reg32 },
	/// - Mnemonic: `MOVSXD`
	/// - Variant: `MOVSXD r64, r/m32`
	/// - Opcode: `REX.W + 63 /r`
	/// - What-extended: **sign-extended**
	///
	/// Sets the 64 bits destination register to the sign-extended value of the 32 bits source register/area.
	MovsxdRegOrMem32ToReg64 { src: RegOrMem32, dst: Reg64 },
	/// - Mnemonic: `MOVSX`
	/// - Variant: `MOVSX r64, r/m8`
	/// - Opcode: `REX.W + 0F BE /r`
	/// - What-extended: **sign-extended**
	///
	/// Sets the 64 bits destination register to the sign-extended value of the 8 bits source register/area.
	MovsxRegOrMem8ToReg64 { src: RegOrMem8, dst: Reg64 },
	/// - Mnemonic: `MOVZX`
	/// - Variant: `MOVZX r64, r/m8`
	/// - Opcode: `REX.W + 0F B6 /r`
	/// - What-extended: **zero-extended**
	///
	/// Sets the 64 bits destination register to the zero-extended value of the 8 bits source register/area.
	MovzxRegOrMem8ToReg64 { src: RegOrMem8, dst: Reg64 },
	/// - Mnemonic: `MOV`
	/// - Variant: `MOV r/m64, r64`
	/// - Opcode: `REX.W + 89 /r`
	///
	/// Sets the 64 bits destination register/area to the value of the source 64 bits register.
	MovReg64ToRegOrMem64 { src: Reg64, dst: RegOrMem64 },
	/// - Mnemonic: `MOV`
	/// - Variant: `MOV r/m32, r32`
	/// - Opcode: `89 /r`
	///
	/// Sets the 32 bits destination register/area to the value of the source 32 bits register.
	MovReg32ToRegOrMem32 { src: Reg32, dst: RegOrMem32 },
	/// - Mnemonic: `MOV`
	/// - Variant: `MOV r/m8, r8`
	/// - Opcode: `88 /r`
	///
	/// Sets the 8 bits destination register/area to the value of the source 8 bits register.
	MovReg8ToRegOrMem8 { src: Reg8, dst: RegOrMem8 },
	/// - Mnemonic: `ADD`
	/// - Variant: `ADD r/m64, r64`
	/// - Opcode: `REX.W + 01 /r`
	/// - Touches flags.
	///
	/// Does the addition of the 64 bits arguments and writes it in the destination 64 bits register/area.
	AddReg64ToRegOrMem64 { src: Reg64, dst: RegOrMem64 },
	/// - Mnemonic: `SYSCALL`
	/// - Variant: `SYSCALL`
	/// - Opcode: `0F 05`
	///
	/// Does a syscall!
	/// Syscall number is in RAX.
	/// Arguments are passed via registers in that order: RDI, RSI, RDX, R10, R8, R9.
	/// The return value is in RAX,
	/// the second return value (only used by the pipe syscall on some architectures) is in RDX.
	/// The only registers that are modified are RCX, R11, RAX, and in a niche case RDX.
	Syscall,
	/// - Mnemonic: `UD2` or `UD`
	/// - Variant: `UD2`
	/// - Opcode: `0F 0B`
	///
	/// "Undefined Instruction", raises an "invalid opcode" exception.
	Ud2,
	/// - Mnemonic: `JMP`
	/// - Variant: `JMP rel32`
	/// - Opcode: `E9 cd`
	///
	/// Jumps to code at the address that is
	/// the address of the following instruction added to the signed 32 bits immediate offset.
	JmpRel32(Rel32),
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
				let dst64 = dst.to_64();
				write!(f, "xor reg/mem d {src} -> reg d {dst} zx q {dst64}")
			},
			X8664Instr::XorRegOrMem64ToReg64 { src, dst } => {
				write!(f, "xor reg/mem q {src} -> reg q {dst}")
			},
			X8664Instr::MovImm64ToReg64 { src, dst } => {
				write!(f, "mov imm q {src} -> reg q {dst}")
			},
			X8664Instr::MovImm32ToReg32 { src, dst } => {
				let dst64 = dst.to_64();
				write!(f, "mov imm d {src} -> reg d {dst} zx q {dst64}")
			},
			X8664Instr::MovImm8ToReg8 { src, dst } => {
				write!(f, "mov imm b {src} -> reg b {dst}")
			},
			X8664Instr::MovImm32ToRegOrMem64 { src, dst } => {
				write!(f, "mov imm d {src} sx q -> reg/mem q {dst}")
			},
			X8664Instr::MovRegOrMem64ToReg64 { src, dst } => {
				write!(f, "mov reg/mem q {src} -> reg q {dst}")
			},
			X8664Instr::MovRegOrMem32ToReg32 { src, dst } => {
				let dst64 = dst.to_64();
				write!(f, "mov reg/mem d {src} -> reg d {dst} zx q {dst64}")
			},
			X8664Instr::MovsxdRegOrMem32ToReg64 { src, dst } => {
				write!(f, "movsxd reg/mem d {src} sx q -> reg q {dst}")
			},
			X8664Instr::MovsxRegOrMem8ToReg64 { src, dst } => {
				write!(f, "movsx reg/mem b {src} sx q -> reg q {dst}")
			},
			X8664Instr::MovzxRegOrMem8ToReg64 { src, dst } => {
				write!(f, "movzx reg/mem b {src} zx q -> reg q {dst}")
			},
			X8664Instr::MovReg64ToRegOrMem64 { src, dst } => {
				write!(f, "mov reg q {src} -> reg/mem q {dst}")
			},
			X8664Instr::MovReg32ToRegOrMem32 { src, dst } => {
				write!(f, "mov reg d {src} -> reg/mem d {dst}")
			},
			X8664Instr::MovReg8ToRegOrMem8 { src, dst } => {
				write!(f, "mov reg b {src} -> reg/mem b {dst}")
			},
			X8664Instr::AddReg64ToRegOrMem64 { src, dst } => {
				write!(f, "add reg q {src} -> reg/mem q {dst}")
			},
			X8664Instr::Syscall => write!(f, "syscall"),
			X8664Instr::Ud2 => write!(f, "ud2"),
			X8664Instr::JmpRel32(offset) => write!(f, "jmp rel d {offset}"),
		}
	}
}

#[derive(Clone, Copy)]
pub struct Imm64(u64);
#[derive(Clone, Copy)]
pub struct Imm32(u32);
#[derive(Clone, Copy)]
pub struct Imm8(u8);

impl Imm64 {
	pub(crate) fn from_value(value: Value64) -> Imm64 {
		Imm64(value.to_u64())
	}
	pub(crate) fn from_u64(value: u64) -> Imm64 {
		Imm64(value)
	}
	fn to_bytes(self) -> Vec<u8> {
		Vec::from(self.0.to_le_bytes())
	}
}
impl Imm32 {
	pub(crate) fn from_value(value: Value32) -> Imm32 {
		Imm32(value.to_u32())
	}
	pub(crate) fn from_u32(value: u32) -> Imm32 {
		Imm32(value)
	}
	fn to_bytes(self) -> Vec<u8> {
		Vec::from(self.0.to_le_bytes())
	}
}
impl Imm8 {
	pub(crate) fn from_value(value: Value8) -> Imm8 {
		Imm8(value.to_u8())
	}
	pub(crate) fn from_u8(value: u8) -> Imm8 {
		Imm8(value)
	}
	fn to_bytes(self) -> Vec<u8> {
		Vec::from(self.0.to_le_bytes())
	}
}

impl std::fmt::Display for Imm64 {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{:#016x}", self.0)
	}
}
impl std::fmt::Display for Imm32 {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{:#08x}", self.0)
	}
}
impl std::fmt::Display for Imm8 {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{:#02x}", self.0)
	}
}

/// An immediate value that is stripped of all details regarding its origin, no sign no nothing,
/// just the final value whose size and bytes are all we know and that will end up as-is in the binary.
#[derive(Clone, Copy)]
pub(crate) enum Imm {
	Imm64(Imm64),
	Imm32(Imm32),
	Imm8(Imm8),
}

impl Imm {
	pub(crate) fn to_bytes(self) -> Vec<u8> {
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
