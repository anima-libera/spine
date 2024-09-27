use std::{collections::HashMap, os::unix::fs::PermissionsExt};

use crate::asm::AsmInstr;

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

pub(crate) struct Binary {
	entry_point_offset_in_code: usize,
	/// Address in memory of where we want to put the code
	/// (but it actually ends up at some address that is this value added to
	/// the offset of the code in the binary).
	code_segment_address_without_offset: usize,
	/// Address in memory of where we want to put the data
	/// (but it actually ends up at some address that is this value added to
	/// the offset of the data in the binary).
	data_segment_address_without_offset: usize,
	pub(crate) asm_instrs: Vec<AsmInstr>,
	pub(crate) data_bytes: Vec<u8>,
}

pub(crate) struct Layout {
	pub(crate) code_segment_address: usize,
	pub(crate) data_segment_address: usize,
	/// The memory address of every code label.
	pub(crate) code_label_address_table: HashMap<String, usize>,
}

impl Binary {
	pub(crate) fn new() -> Binary {
		Binary {
			entry_point_offset_in_code: 0,
			code_segment_address_without_offset: 0x400000,
			data_segment_address_without_offset: 0x600000,
			asm_instrs: vec![],
			data_bytes: vec![],
		}
	}

	pub(crate) fn layout(&self) -> Layout {
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

	pub(crate) fn code_segment_binary_machine_code(&self) -> Vec<u8> {
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

	pub(crate) fn to_binary(&self) -> Vec<u8> {
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

pub(crate) fn chmod_x(path: impl AsRef<std::path::Path>) {
	let mut permissions = std::fs::metadata(&path).unwrap().permissions();
	let permission_flags = permissions.mode();
	let executable_mask = 0b0001001001; // drwxrwxrwx, we set the xs to 1
	permissions.set_mode(permission_flags | executable_mask);
	std::fs::set_permissions(path, permissions).unwrap();
}
