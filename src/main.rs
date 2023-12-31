#![allow(unused)]

use std::collections::HashMap;

struct ByteBuffer {
	bytes: Vec<u8>,
}
impl ByteBuffer {
	fn new() -> ByteBuffer {
		ByteBuffer { bytes: vec![] }
	}
	fn into_bytes(self) -> Vec<u8> {
		self.bytes
	}

	fn write_bytes(&mut self, bytes: &[u8]) {
		self.bytes.extend(bytes);
	}
}

macro_rules! byte_buffer_fn_write {
	($func:ident, $type:ty) => {
		impl ByteBuffer {
			fn $func(&mut self, value: $type) {
				self.bytes.extend(value.to_le_bytes());
			}
		}
	};
}
byte_buffer_fn_write!(write_u8, u8);
byte_buffer_fn_write!(write_u16, u16);
byte_buffer_fn_write!(write_u32, u32);
byte_buffer_fn_write!(write_u64, u64);

// Okay so here we must not be confused about *offsets in the binary* and *addresses in the memory*.
// The binary is an array of bytes, and anything that is in the binary has an offset in the binary
// (its index in that array of bytes).
// When the binary gets loaded in the memory to be executed, some stuff that is written in it
// get copied into the memory, at some address (that depends on the offset of the stuff in the
// binary but also on weather that stuff is code or data or whatever and some other stuff).
// The offset in the binary and the address in the memory are related but are not to be confused
// with each other. These may be refered to as the *offset* and the *address* respectively.

struct Binary {
	entry_point_offset_in_code: usize,
	/// Address in memory of where we want to put the code
	/// (but it actually ends up at some address that is this value added to
	/// the offset of the code in the binary).
	code_segment_address_without_offset: usize,
	/// Address in memory of where we want to put the data
	/// (but it actually ends up at some address that is this value added to
	/// the offset of the data in the binary).
	data_segment_address_without_offset: usize,
	asm_instrs: Vec<AsmInstr>,
	data_bytes: Vec<u8>,
}

struct Layout {
	code_segment_address: usize,
	data_segment_address: usize,
	/// The memory address of every code label.
	code_label_address_table: HashMap<String, usize>,
}

impl Binary {
	fn new() -> Binary {
		Binary {
			entry_point_offset_in_code: 0,
			code_segment_address_without_offset: 0x400000,
			data_segment_address_without_offset: 0x600000,
			asm_instrs: vec![],
			data_bytes: vec![],
		}
	}

	fn layout(&self) -> Layout {
		let code_segment_address =
			self.code_segment_address_without_offset + Binary::CODE_OFFSET_IN_BINARY;

		let mut code_label_address_table = HashMap::new();
		let mut instr_address = code_segment_address;
		for asm_instr in self.asm_instrs.iter() {
			if let AsmInstr::Label { name } = asm_instr {
				code_label_address_table.insert(name.clone(), instr_address);
			}
			instr_address += asm_instr.machine_code_size();
		}

		let data_offset_in_binary = Binary::CODE_OFFSET_IN_BINARY + self.code_size_in_binary();
		let data_segment_address = self.data_segment_address_without_offset + data_offset_in_binary;

		Layout {
			code_segment_address,
			data_segment_address,
			code_label_address_table,
		}
	}

	fn code_segment_binary_machine_code(&self) -> Vec<u8> {
		let layout = self.layout();
		let mut instr_address = layout.code_segment_address;
		let mut machine_code_bytes = Vec::new();
		for asm_instr in self.asm_instrs.iter() {
			machine_code_bytes.extend(asm_instr.to_machine_code(&layout, instr_address));
			instr_address += asm_instr.machine_code_size();
		}
		machine_code_bytes
	}

	fn code_size_in_binary(&self) -> usize {
		self
			.asm_instrs
			.iter()
			.map(AsmInstr::machine_code_size)
			.sum()
	}

	fn data_segment_binary_content(&self) -> Vec<u8> {
		self.data_bytes.clone()
	}

	fn data_size_in_binary(&self) -> usize {
		self.data_bytes.len()
	}

	const ELF_HEADER_SIZE: usize = 0x40;
	const PROGRAM_HEADER_TABLE_ENTRY_SIZE: usize = 0x38;
	const PROGRAM_HEADER_TABLE_LENGTH: usize = 2; // Code and data are enough for us
	const CODE_OFFSET_IN_BINARY: usize =
		Binary::ELF_HEADER_SIZE + Binary::PROGRAM_HEADER_TABLE_ENTRY_SIZE * 2;

	fn to_binary(&self) -> Vec<u8> {
		let mut buf = ByteBuffer::new();

		// See https://en.wikipedia.org/wiki/Executable_and_Linkable_Format
		// Also see https://github.com/vishen/go-x64-executable/blob/master/main.go
		// Beware! This is a certified ELF moment!
		// 64 bits

		let entry_point_address = Binary::CODE_OFFSET_IN_BINARY
			+ self.entry_point_offset_in_code
			+ self.code_segment_address_without_offset;

		// ELF header
		buf.write_bytes(&[0x7f, b'E', b'L', b'F']); // ELF magic number
		buf.write_u8(2); // 1 -> 32-bits, 2 -> 64-bits
		buf.write_u8(1); // 1 -> little endian, 2 -> big endian
		buf.write_u8(1); // ELF format version (still 1 in 2023)
		buf.write_u8(3); // Target Linux
		buf.write_u8(0); // Required dynamic linker version (we don't care)
		buf.write_bytes(&[0, 0, 0, 0, 0, 0, 0]); // Padding
		buf.write_u16(2); // This is an executable
		buf.write_u16(0x3e); // Target x86-64
		buf.write_u32(1); // ELF format version (again??)
		buf.write_u64(entry_point_address as u64); // Entry point address
		buf.write_u64(Binary::ELF_HEADER_SIZE as u64); // Program header table offset in binary
		buf.write_u64(0); // Section header table offset in binary (we don't have one)
		buf.write_u32(0); // Target architecture dependent flags
		buf.write_u16(Binary::ELF_HEADER_SIZE as u16); // Size of this header
		buf.write_u16(Binary::PROGRAM_HEADER_TABLE_ENTRY_SIZE as u16); // Size of a prog entry
		buf.write_u16(Binary::PROGRAM_HEADER_TABLE_LENGTH as u16); // Number of prog entries in table
		buf.write_u16(0); // Size of a section header table entry (we don't have one)
		buf.write_u16(0); // Number of entries in section header table
		buf.write_u16(0); // Index of the section header table entry with the section names
		assert_eq!(buf.bytes.len(), Binary::ELF_HEADER_SIZE);

		// Program header table
		let mut program_header_table_entry_count = 0;
		const FLAG_READABLE: u32 = 1 << 0;
		const FLAG_WRITABLE: u32 = 1 << 1;
		const FLAG_EXECUTABLE: u32 = 1 << 2;
		{
			// Code segment
			let offset = Binary::CODE_OFFSET_IN_BINARY as u64;
			let address_without_offset = self.code_segment_address_without_offset as u64;
			let address = address_without_offset + offset;
			let size = self.code_size_in_binary() as u64;

			buf.write_u32(1); // Loadable segment
			buf.write_u32(FLAG_READABLE | FLAG_WRITABLE | FLAG_EXECUTABLE); // Flags
			buf.write_u64(offset); // Offset in binary
			buf.write_u64(address); // Address in virtual memory
			buf.write_u64(address); // Address in physical memory (wtf)
			buf.write_u64(size); // Size in binary
			buf.write_u64(size); // Size in memory
			buf.write_u64(0); // Alignment (0 means no alignment)
			assert_eq!(
				buf.bytes.len(),
				Binary::ELF_HEADER_SIZE + Binary::PROGRAM_HEADER_TABLE_ENTRY_SIZE
			);
		}
		program_header_table_entry_count += 1;
		{
			// Data segment
			let offset = (Binary::CODE_OFFSET_IN_BINARY + self.code_size_in_binary()) as u64;
			let address_without_offset = self.data_segment_address_without_offset as u64;
			let address = address_without_offset + offset;
			let size = self.data_size_in_binary() as u64;

			buf.write_u32(1); // Loadable segment
			buf.write_u32(FLAG_READABLE | FLAG_WRITABLE | FLAG_EXECUTABLE); // Flags
			buf.write_u64(offset); // Offset in binary
			buf.write_u64(address); // Address in virtual memory
			buf.write_u64(address); // Address in physical memory (wtf)
			buf.write_u64(size); // Size in binary
			buf.write_u64(size); // Size in memory
			buf.write_u64(0); // Alignment (0 means no alignment)
			assert_eq!(
				buf.bytes.len(),
				Binary::ELF_HEADER_SIZE + Binary::PROGRAM_HEADER_TABLE_ENTRY_SIZE * 2
			);
		}
		program_header_table_entry_count += 1;
		assert_eq!(
			program_header_table_entry_count,
			Binary::PROGRAM_HEADER_TABLE_LENGTH
		);

		// Code
		assert_eq!(buf.bytes.len(), Binary::CODE_OFFSET_IN_BINARY);
		let machine_code = self.code_segment_binary_machine_code();
		assert_eq!(machine_code.len(), self.code_size_in_binary());
		buf.write_bytes(&machine_code);

		// Data
		let data_bytes = self.data_segment_binary_content();
		assert_eq!(data_bytes.len(), self.data_size_in_binary());
		buf.write_bytes(&data_bytes);

		// Definitely one of the ELF executables of all times!
		buf.into_bytes()

		// Thank you for using/reading my compiler~ <3
	}
}

// Immediate values `Imm8`, `Imm32` and `Imm64` can sometimes represent something (like a memory
// address of something in the data segment for example) that isn't just a raw number.
// Immediate values can also just be a raw number (either signed or unsigned btw).
// We make the difference here, with `Raw8`, `Raw32` and `Raw64` being different types than
// immediate value types, and immediate value types being convertible to raw values given
// some layout information available at the time assembly code is not being generated anymore
// and is ready to be converted to machine code, at the end.
// Unless there is a good reason, assembly instruction variants should hold immediate values
// with the `ImmN` types instead of the `RawN` types or the `uN`/`iN` types.

#[derive(Clone, Copy)]
enum Raw8 {
	Signed(i8),
	Unsigned(u8),
}
#[derive(Clone, Copy)]
enum Raw32 {
	Signed(i32),
	Unsigned(u32),
}
#[derive(Clone, Copy)]
enum Raw64 {
	Signed(i64),
	Unsigned(u64),
}

macro_rules! impl_raw_is_signed {
	($raw_n:ty) => {
		impl $raw_n {
			fn is_signed(self) -> bool {
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

macro_rules! impl_raw_to_bytes {
	($raw_n:ty, $fn_name:ident, $as_unsigned:ty, $as_signed:ty, $size:literal) => {
		impl $raw_n {
			fn $fn_name(self) -> [u8; $size] {
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

enum Imm8 {
	Raw(Raw8),
}

impl Imm8 {
	fn to_raw_8(&self, _layout: &Layout) -> Raw8 {
		match self {
			Imm8::Raw(raw) => *raw,
		}
	}
}

enum Imm32 {
	DataAddr { offset_in_data_segment: u32 },
	Raw(Raw32),
}

impl Imm32 {
	fn to_raw_32(&self, layout: &Layout) -> Raw32 {
		match self {
			Imm32::DataAddr { offset_in_data_segment } => {
				Raw32::Unsigned(layout.data_segment_address as u32 + offset_in_data_segment)
			},
			Imm32::Raw(raw) => *raw,
		}
	}
}

enum Imm64 {
	DataAddr { offset_in_data_segment: u64 },
	Raw(Raw64),
}

impl Imm64 {
	fn to_raw_64(&self, layout: &Layout) -> Raw64 {
		match self {
			Imm64::DataAddr { offset_in_data_segment } => {
				Raw64::Unsigned(layout.data_segment_address as u64 + offset_in_data_segment)
			},
			Imm64::Raw(raw) => *raw,
		}
	}
}

enum Imm {
	Imm8(Imm8),
	Imm32(Imm32),
	Imm64(Imm64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code)]
#[rustfmt::skip]
enum Reg64 {
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
enum BaseSize {
	Size8,
	Size32,
	Size64,
}

enum AsmInstr {
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
	fn to_machine_code(&self, layout: &Layout, instr_address: usize) -> Vec<u8> {
		let bytes = match self {
			AsmInstr::MovImmToReg64 { imm_src, reg_dst } => {
				// `MOV r64, imm64`

				// TODO: Use variants that take up less bytes when possible.
				// Beware sign extension vs zero extension stuff tho!
				// Here is a relic of the past to help:
				//
				// if imm_src.is_signed() {
				//    // MOV r/m64, imm32
				//    // This MOV variant sign-extends the imm32, which is only fine for signed values.
				//    let (reg_dst_id_high_bit, reg_dst_id_low_3_bits) =
				//       separate_bit_b_in_bxxx(reg_dst.id());
				//    let mod_rm = mod_rm_byte(0b11, 0, reg_dst_id_low_3_bits);
				//    let rex_prefix = rex_prefix_byte(1, reg_dst_id_high_bit, 0, 0);
				//    let opcode_byte = 0xc7;
				//    let mut machine_code = vec![rex_prefix, opcode_byte, mod_rm];
				//    machine_code.extend(imm_src.to_binary(layout));
				//    machine_code
				// } else {
				//    // MOV r32, imm32
				//    // This MOV variant zero-extends the imm32 (but it doesn't work for MOV r8, imm8,
				//    // see https://stackoverflow.com/q/11177137 for details).
				//    let (reg_dst_id_high_bit, reg_dst_id_low_3_bits) =
				//       separate_bit_b_in_bxxx(reg_dst.id());
				//    let rex_prefix = rex_prefix_byte(0, reg_dst_id_high_bit, 0, 0);
				//    let opcode_byte = 0xb8 + reg_dst_id_low_3_bits;
				//    let mut machine_code = vec![rex_prefix, opcode_byte];
				//    machine_code.extend(imm_src.to_binary(layout));
				//    machine_code
				// }

				let imm_as_8_bytes = match imm_src {
					Imm::Imm64(imm64) => imm64.to_raw_64(layout).to_8_bytes(),
					Imm::Imm32(imm32) => imm32.to_raw_32(layout).to_8_bytes(),
					Imm::Imm8(imm8) => imm8.to_raw_8(layout).to_8_bytes(),
				};
				let (reg_dst_id_high_bit, reg_dst_id_low_3_bits) = separate_bit_b_in_bxxx(reg_dst.id());
				let rex_prefix = rex_prefix_byte(1, 0, 0, reg_dst_id_high_bit);
				let opcode_byte = 0xb8 + reg_dst_id_low_3_bits;
				let mut machine_code = vec![rex_prefix, opcode_byte];
				machine_code.extend(imm_as_8_bytes);
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

	fn machine_code_size(&self) -> usize {
		match self {
			AsmInstr::MovImmToReg64 { .. } => 10,
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

enum SpineType {
	I64,
}

enum SpineValue {
	I64(i64),
}

enum SpineInstr {
	PushConst(SpineValue),
	PopI64AndPrintAsChar,
	Exit,
}

struct SpineProgram {
	instrs: Vec<SpineInstr>,
}

fn main() {
	let program = SpineProgram {
		instrs: vec![
			SpineInstr::PushConst(SpineValue::I64(10)),
			SpineInstr::PushConst(SpineValue::I64(97)),
			SpineInstr::PopI64AndPrintAsChar,
			SpineInstr::PopI64AndPrintAsChar,
			SpineInstr::Exit,
		],
	};

	let mut bin = Binary::new();

	use AsmInstr::*;

	for instr in program.instrs.iter() {
		match instr {
			SpineInstr::PushConst(SpineValue::I64(value)) => {
				bin.asm_instrs.extend([
					MovImmToReg64 {
						imm_src: Imm::Imm64(Imm64::Raw(Raw64::Signed(*value))),
						reg_dst: Reg64::Rax,
					},
					PushReg64 { reg_src: Reg64::Rax },
				]);
			},
			SpineInstr::PopI64AndPrintAsChar => {
				bin.asm_instrs.extend([
					// Write(message) syscall
					MovImmToReg64 {
						imm_src: Imm::Imm64(Imm64::Raw(Raw64::Unsigned(1))),
						reg_dst: Reg64::Rax, // Syscall number
					},
					MovImmToReg64 {
						imm_src: Imm::Imm64(Imm64::Raw(Raw64::Unsigned(1))),
						reg_dst: Reg64::Rdi, // Stdout file descriptor
					},
					PushReg64 { reg_src: Reg64::Rsp },
					PopToReg64 { reg_dst: Reg64::Rsi }, // String address
					MovImmToReg64 {
						imm_src: Imm::Imm64(Imm64::Raw(Raw64::Unsigned(1))),
						reg_dst: Reg64::Rdx, // String length
					},
					Syscall,
					// Pop
					PopToReg64 { reg_dst: Reg64::Rsi },
				]);
			},
			SpineInstr::Exit => {
				bin.asm_instrs.extend([
					// Exit(0) syscall
					MovImmToReg64 {
						imm_src: Imm::Imm64(Imm64::Raw(Raw64::Unsigned(60))),
						reg_dst: Reg64::Rax, // Syscall number
					},
					MovImmToReg64 {
						imm_src: Imm::Imm64(Imm64::Raw(Raw64::Unsigned(0))),
						reg_dst: Reg64::Rdi, // Exit code, 0 means all good
					},
					Syscall,
				]);
			},
		}
	}

	for byte in bin.code_segment_binary_machine_code() {
		print!("{byte:02x}");
	}
	println!();

	std::fs::write("binary", bin.to_binary()).unwrap();
}

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn test_1() {
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

		std::fs::write("binary", bin.to_binary()).unwrap();

		let binary_execution_result = std::process::Command::new("./binary").output().unwrap();
		let binary_execution_output =
			std::str::from_utf8(binary_execution_result.stdout.as_slice()).unwrap();
		assert_eq!(binary_execution_output, "mewwo :3\n");
	}
}
