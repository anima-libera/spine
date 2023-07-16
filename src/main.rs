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

	fn make_sure_index_exists(&mut self, index: usize) {
		if self.bytes.len() <= index {
			self.bytes.resize(index + 1, 0);
		}
	}

	fn write_bytes(&mut self, index: usize, bytes: &[u8]) -> usize {
		self.make_sure_index_exists(index + bytes.len() - 1);
		self.bytes[index..].clone_from_slice(bytes);
		index + bytes.len()
	}
}

macro_rules! byte_buffer_fn_write {
	($func:ident, $type:ty) => {
		impl ByteBuffer {
			fn $func(&mut self, index: usize, value: $type) -> usize {
				self.make_sure_index_exists(index + std::mem::size_of::<$type>() - 1);
				self.bytes[index..].clone_from_slice(&value.to_le_bytes());
				index + std::mem::size_of::<$type>()
			}
		}
	};
}
byte_buffer_fn_write!(write_u8, u8);
byte_buffer_fn_write!(write_u16, u16);
byte_buffer_fn_write!(write_u32, u32);
byte_buffer_fn_write!(write_u64, u64);

struct Binary {
	entry_point_offset_in_code: usize,
	/// Address in memory. Beware: one often has to add the offset in the binary to this!
	code_segment_address_without_offset: usize,
	/// Address in memory. Beware: one often has to add the offset in the binary to this!
	data_segment_address_without_offset: usize,
	asm_instrs: Vec<AsmInstr>,
	data: Vec<u8>,
}

impl Binary {
	fn new() -> Binary {
		Binary {
			entry_point_offset_in_code: 0,
			code_segment_address_without_offset: 0x400000,
			data_segment_address_without_offset: 0x600000,
			asm_instrs: vec![],
			data: vec![],
		}
	}

	fn code_segment_binary_machine_code(&self) -> Vec<u8> {
		let mut buf = ByteBuffer::new();
		let mut i = 0;
		let data_offset_in_binary = Binary::CODE_OFFSET_IN_BINARY + self.code_size_in_binary();
		let data_segment_address = self.data_segment_address_without_offset + data_offset_in_binary;
		for asm_instr in self.asm_instrs.iter() {
			i = buf.write_bytes(i, &asm_instr.to_machine_code(data_segment_address));
		}
		buf.into_bytes()
	}

	fn code_size_in_binary(&self) -> usize {
		self
			.asm_instrs
			.iter()
			.map(AsmInstr::machine_code_size)
			.sum()
	}

	fn data_segment_binary_content(&self) -> Vec<u8> {
		self.data.clone()
	}

	fn data_size_in_binary(&self) -> usize {
		self.data_segment_binary_content().len()
	}

	const ELF_HEADER_SIZE: usize = 0x40;
	const PROGRAM_HEADER_TABLE_ENTRY_SIZE: usize = 0x38;
	const PROGRAM_HEADER_TABLE_LENGTH: usize = 2; // Code and data are enough for us
	const CODE_OFFSET_IN_BINARY: usize =
		Binary::ELF_HEADER_SIZE + Binary::PROGRAM_HEADER_TABLE_ENTRY_SIZE * 2;

	fn to_binary(&self) -> ByteBuffer {
		let mut buf = ByteBuffer::new();
		let mut i = 0;

		// See https://en.wikipedia.org/wiki/Executable_and_Linkable_Format
		// Also see https://github.com/vishen/go-x64-executable/blob/master/main.go
		// Beware! This is a certified ELF moment!
		// 64 bits

		let entry_point_address = Binary::CODE_OFFSET_IN_BINARY
			+ self.entry_point_offset_in_code
			+ self.code_segment_address_without_offset;

		// ELF header
		i = buf.write_bytes(i, &[0x7f, b'E', b'L', b'F']); // ELF magic number
		i = buf.write_u8(i, 2); // 1 -> 32-bits, 2 -> 64-bits
		i = buf.write_u8(i, 1); // 1 -> little endian, 2 -> big endian
		i = buf.write_u8(i, 1); // ELF format version (still 1 in 2023)
		i = buf.write_u8(i, 3); // Target Linux
		i = buf.write_u8(i, 0); // Required dynamic linker version (we don't care)
		i = buf.write_bytes(i, &[0, 0, 0, 0, 0, 0, 0]); // Padding
		i = buf.write_u16(i, 2); // This is an executable
		i = buf.write_u16(i, 0x3e); // Target x86-64
		i = buf.write_u32(i, 1); // ELF format version (again??)
		i = buf.write_u64(i, entry_point_address as u64); // Entry point address
		i = buf.write_u64(i, Binary::ELF_HEADER_SIZE as u64); // Program header table offset in binary
		i = buf.write_u64(i, 0); // Section header table offset in binary (we don't have one)
		i = buf.write_u32(i, 0); // Target architecture dependent flags
		i = buf.write_u16(i, Binary::ELF_HEADER_SIZE as u16); // Size of this header
		i = buf.write_u16(i, Binary::PROGRAM_HEADER_TABLE_ENTRY_SIZE as u16); // Size of a prog entry
		i = buf.write_u16(i, Binary::PROGRAM_HEADER_TABLE_LENGTH as u16); // Number of prog entries in table
		i = buf.write_u16(i, 0); // Size of a section header table entry (we don't have one)
		i = buf.write_u16(i, 0); // Number of entries in section header table
		i = buf.write_u16(i, 0); // Index of the section header table entry with the section names
		assert_eq!(i, Binary::ELF_HEADER_SIZE);

		// Program header table
		let mut program_header_table_entry_count = 0;
		{
			// Code segment
			let offset = Binary::CODE_OFFSET_IN_BINARY as u64;
			let address_without_offset = self.code_segment_address_without_offset as u64;
			let address = address_without_offset + offset;
			let size = self.code_size_in_binary() as u64;

			i = buf.write_u32(i, 1); // Loadable segment
			i = buf.write_u32(
				i,
				(1 << 0/*Readable*/) | (1 << 1/*Writable*/) | (1 << 2/*Executable*/),
			); // Flags
			i = buf.write_u64(i, offset); // Offset in binary
			i = buf.write_u64(i, address); // Address in virtual memory
			i = buf.write_u64(i, address); // Address in physical memory (wtf)
			i = buf.write_u64(i, size); // Size in binary
			i = buf.write_u64(i, size); // Size in memory
			i = buf.write_u64(i, 0); // Alignment (0 means no alignment)
			assert_eq!(
				i,
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

			i = buf.write_u32(i, 1); // Loadable segment
			i = buf.write_u32(
				i,
				(1 << 0/*Readable*/) | (1 << 1/*Writable*/) | (1 << 2/*Executable*/),
			); // Flags
			i = buf.write_u64(i, offset); // Offset in binary
			i = buf.write_u64(i, address); // Address in virtual memory
			i = buf.write_u64(i, address); // Address in physical memory (wtf)
			i = buf.write_u64(i, size); // Size in binary
			i = buf.write_u64(i, size); // Size in memory
			i = buf.write_u64(i, 0); // Alignment (0 means no alignment)
			assert_eq!(
				i,
				Binary::ELF_HEADER_SIZE + Binary::PROGRAM_HEADER_TABLE_ENTRY_SIZE * 2
			);
		}
		program_header_table_entry_count += 1;
		assert_eq!(
			program_header_table_entry_count,
			Binary::PROGRAM_HEADER_TABLE_LENGTH
		);

		// Code
		i = buf.write_bytes(i, self.code_segment_binary_machine_code().as_slice());

		// Data
		i = buf.write_bytes(i, self.data_segment_binary_content().as_slice());

		assert_eq!(i, buf.bytes.len());

		buf
	}
}

enum Imm32 {
	DataAddr { offset_in_data_segment: u32 },
	Const(u32),
}

impl Imm32 {
	fn to_binary(&self, data_segment_address: usize) -> [u8; 4] {
		match self {
			Imm32::DataAddr { offset_in_data_segment } => {
				(data_segment_address as u32 + offset_in_data_segment).to_le_bytes()
			},
			Imm32::Const(value) => value.to_le_bytes(),
		}
	}
}

type U4 = u8;
type U3 = u8;
type U2 = u8;
type Bit = u8;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

enum AsmInstr {
	MovImm32ToReg64 { imm_src: Imm32, reg_dst: Reg64 },
	Syscall,
}

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
/// ***TODO** explain each field, using the paragraph 2.1.3 "ModR/M and SIB Bytes" of the x86_64
/// manual.*
fn mod_rm_byte(mod_: U2, reg: U3, rm: U3) -> u8 {
	assert!(mod_ <= 3);
	assert!(reg <= 7);
	assert!(rm <= 7);
	mod_ << 6 | reg << 3 | rm
}

impl AsmInstr {
	fn to_machine_code(&self, data_segment_address: usize) -> Vec<u8> {
		let bytes = match self {
			AsmInstr::MovImm32ToReg64 { imm_src, reg_dst } => {
				let reg_dst_id = reg_dst.id();
				let reg_dst_id_high_bit = reg_dst_id >> 3;
				let reg_dst_id_low_3_bits = reg_dst_id & 0b00000111;
				let mod_rm = mod_rm_byte(0b11, 0, reg_dst_id_low_3_bits);
				let rex_prefix = rex_prefix_byte(1, reg_dst_id_high_bit, 0, 0);
				let opcode_byte = 0xc7;
				let mut machine_code: Vec<u8> = vec![];
				machine_code.push(rex_prefix);
				machine_code.push(opcode_byte);
				machine_code.push(mod_rm);
				machine_code.extend(imm_src.to_binary(data_segment_address));
				machine_code
			},
			AsmInstr::Syscall => vec![0x0f, 0x05],
		};
		assert_eq!(bytes.len(), self.machine_code_size());
		bytes
	}

	fn machine_code_size(&self) -> usize {
		match self {
			AsmInstr::MovImm32ToReg64 { .. } => 7,
			AsmInstr::Syscall => 2,
		}
	}
}

fn main() {
	let mut bin = Binary::new();

	bin.data.extend(0..255);

	bin.asm_instrs
		.push(AsmInstr::MovImm32ToReg64 { imm_src: Imm32::Const(60), reg_dst: Reg64::Rax });
	bin.asm_instrs
		.push(AsmInstr::MovImm32ToReg64 { imm_src: Imm32::Const(0), reg_dst: Reg64::Rdi });
	bin.asm_instrs.push(AsmInstr::Syscall);

	for byte in bin.code_segment_binary_machine_code() {
		print!("{byte:02x}");
	}
	println!();

	std::fs::write("binary", bin.to_binary().bytes).unwrap();
}
