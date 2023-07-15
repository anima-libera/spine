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
	code_segment_address: usize,
	/// Address in memory. Beware: one often has to add the offset in the binary to this!
	data_segment_address: usize,
	asm_instrs: Vec<AsmInstr>,
}

impl Binary {
	fn new() -> Binary {
		Binary {
			entry_point_offset_in_code: 0,
			code_segment_address: 0x400000,
			data_segment_address: 0x600000,
			asm_instrs: vec![],
		}
	}

	fn code_segment_binary_machine_code(&self) -> Vec<u8> {
		let mut buf = ByteBuffer::new();
		let mut i = 0;
		for asm_instr in self.asm_instrs.iter() {
			i = buf.write_bytes(i, &asm_instr.to_machine_code().1.unwrap());
		}
		buf.into_bytes()
	}

	fn code_size_in_binary(&self) -> usize {
		self.code_segment_binary_machine_code().len()
	}

	fn data_segment_binary_content(&self) -> Vec<u8> {
		ByteBuffer::new().into_bytes()
	}

	fn data_size_in_binary(&self) -> usize {
		self.data_segment_binary_content().len()
	}

	fn to_binary(&self) -> ByteBuffer {
		let mut buf = ByteBuffer::new();
		let mut i = 0;

		// See https://en.wikipedia.org/wiki/Executable_and_Linkable_Format
		// Also see https://github.com/vishen/go-x64-executable/blob/master/main.go
		// Beware! This is a certified ELF moment!
		// 64 bits

		const ELF_HEADER_SIZE: usize = 0x40;
		const PROGRAM_HEADER_TABLE_ENTRY_SIZE: usize = 0x38;
		const PROGRAM_HEADER_TABLE_LENGTH: usize = 2; // Code and data are enough for us
		const CODE_OFFSET_IN_BINARY: usize = ELF_HEADER_SIZE + PROGRAM_HEADER_TABLE_ENTRY_SIZE * 2;

		let entry_point_address =
			CODE_OFFSET_IN_BINARY + self.entry_point_offset_in_code + self.code_segment_address;

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
		i = buf.write_u64(i, ELF_HEADER_SIZE as u64); // Program header table offset in binary
		i = buf.write_u64(i, 0); // Section header table offset in binary (we don't have one)
		i = buf.write_u32(i, 0); // Target architecture dependent flags
		i = buf.write_u16(i, ELF_HEADER_SIZE as u16); // Size of this header
		i = buf.write_u16(i, PROGRAM_HEADER_TABLE_ENTRY_SIZE as u16); // Size of a prog entry
		i = buf.write_u16(i, PROGRAM_HEADER_TABLE_LENGTH as u16); // Number of entries in program header table
		i = buf.write_u16(i, 0); // Size of a section header table entry (we don't have one)
		i = buf.write_u16(i, 0); // Number of entries in section header table
		i = buf.write_u16(i, 0); // Index of the section header table entry that has the section names
		assert_eq!(i, ELF_HEADER_SIZE);

		// Program header table
		let mut program_header_table_entry_count = 0;
		{
			// Code segment
			let bin_offset = CODE_OFFSET_IN_BINARY as u64;
			let addr_offset = self.code_segment_address as u64;
			let size = self.code_size_in_binary() as u64;

			i = buf.write_u32(i, 1); // Loadable segment
			i = buf.write_u32(
				i,
				(1 << 0/*Readable*/) | (1 << 1/*Writable*/) | (1 << 2/*Executable*/),
			); // Flags
			i = buf.write_u64(i, bin_offset); // Offset in binary
			i = buf.write_u64(i, addr_offset + bin_offset); // Address in virtual memory
			i = buf.write_u64(i, addr_offset + bin_offset); // Address in physical memory (wtf)
			i = buf.write_u64(i, size); // Size in binary
			i = buf.write_u64(i, size); // Size in memory
			i = buf.write_u64(i, 0); // Alignment (0 means no alignment)
			assert_eq!(i, ELF_HEADER_SIZE + PROGRAM_HEADER_TABLE_ENTRY_SIZE);
		}
		program_header_table_entry_count += 1;
		{
			// Data segment
			let bin_offset = (CODE_OFFSET_IN_BINARY + self.code_size_in_binary()) as u64;
			let addr_offset = self.data_segment_address as u64;
			let size = self.data_size_in_binary() as u64;

			i = buf.write_u32(i, 1); // Loadable segment
			i = buf.write_u32(
				i,
				(1 << 0/*Readable*/) | (1 << 1/*Writable*/) | (1 << 2/*Executable*/),
			); // Flags
			i = buf.write_u64(i, bin_offset); // Offset in binary
			i = buf.write_u64(i, addr_offset + bin_offset); // Address in virtual memory
			i = buf.write_u64(i, addr_offset + bin_offset); // Address in physical memory (wtf)
			i = buf.write_u64(i, size); // Size in binary
			i = buf.write_u64(i, size); // Size in memory
			i = buf.write_u64(i, 0); // Alignment (0 means no alignment)
			assert_eq!(i, ELF_HEADER_SIZE + PROGRAM_HEADER_TABLE_ENTRY_SIZE * 2);
		}
		program_header_table_entry_count += 1;
		assert_eq!(
			program_header_table_entry_count,
			PROGRAM_HEADER_TABLE_LENGTH
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
	//DataAddr { offset_in_data_segment: u32 },
	Const(u32),
}

impl Imm32 {
	fn to_binary(&self) -> [u8; 4] {
		match self {
			Imm32::Const(value) => value.to_le_bytes(),
		}
	}
}

#[derive(Debug, PartialEq, Eq)]
enum Reg64 {
	Rax,
	//Rbx,
	//Rcx,
	//Rdx,
	//Rbp,
	//Rsp,
	//Rsi,
	Rdi,
	//R8,
	//R9,
	//R10,
	//R11,
	//R12,
	//R13,
	//R14,
	//R15,
}

enum AsmInstr {
	MovImm32ToReg64 { imm_src: Imm32, reg_dst: Reg64 },
	Syscall,
}

impl AsmInstr {
	fn to_machine_code(&self) -> (usize, Option<Vec<u8>>) {
		match self {
			AsmInstr::MovImm32ToReg64 { imm_src, reg_dst } => {
				let size = 7;
				let mut machine_code = match reg_dst {
					Reg64::Rax => vec![0x48, 0xc7, 0xc0],
					Reg64::Rdi => vec![0x48, 0xc7, 0xc7],
					//_ => todo!(),
				};
				machine_code.extend(imm_src.to_binary());
				(size, Some(machine_code))
			},
			AsmInstr::Syscall => (2, Some(vec![0x0f, 0x05])),
		}
	}
}

fn main() {
	let mut bin = Binary::new();

	bin.asm_instrs
		.push(AsmInstr::MovImm32ToReg64 { imm_src: Imm32::Const(60), reg_dst: Reg64::Rax });
	bin.asm_instrs
		.push(AsmInstr::MovImm32ToReg64 { imm_src: Imm32::Const(0), reg_dst: Reg64::Rdi });
	bin.asm_instrs.push(AsmInstr::Syscall);

	std::fs::write("binary", bin.to_binary().bytes).unwrap();
}
