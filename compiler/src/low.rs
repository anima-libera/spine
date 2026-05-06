use crate::high_to_low::{SpineType, SpineValue};

/// Low level instruction.
#[derive(Debug)]
pub(crate) enum LowInstr {
	PushConst(SpineValue),
	PushString(String),
	PopI64AndPrintAsChar,
	PopI64AndPtrAndPrintAsString,
	AddI64AndI64,
	Exit,
	Syscall,
	Illegal,
	/// Nop that just disappears in the codegen.
	NopZeroBytes,
	PopI64AndDiscard,
}

impl LowInstr {
	/// Order:
	/// - If operand types are `[A, B]` then it means `B` will be popped before `A`.
	/// - If return types are `[A, B]` then it means `A` will be pushed before `B`.
	pub(crate) fn operand_and_return_types(&self) -> (Vec<SpineType>, Vec<SpineType>) {
		match self {
			LowInstr::PushConst(value) => (vec![], vec![value.get_type()]),
			LowInstr::PushString(_) => (vec![], vec![SpineType::DataAddr, SpineType::I64]),
			LowInstr::PopI64AndPrintAsChar => (vec![SpineType::I64], vec![]),
			LowInstr::PopI64AndPtrAndPrintAsString => {
				(vec![SpineType::DataAddr, SpineType::I64], vec![])
			},
			LowInstr::AddI64AndI64 => (vec![SpineType::I64, SpineType::I64], vec![SpineType::I64]),
			LowInstr::Exit => (vec![], vec![]),
			LowInstr::Syscall => (
				std::iter::repeat_n(SpineType::I64, 7).collect(),
				vec![SpineType::I64, SpineType::I64],
			),
			LowInstr::Illegal => (vec![], vec![]),
			LowInstr::NopZeroBytes => (vec![], vec![]),
			LowInstr::PopI64AndDiscard => (vec![SpineType::I64], vec![]),
		}
	}
}

/// Low level statement.
#[derive(Debug)]
pub(crate) enum LowStatement {
	Code {
		/// In the order that they are executed, so the reverse of the order in the source code.
		instrs: Vec<LowInstr>,
	},
}

/// Low level program.
pub struct LowProgram {
	pub(crate) statements: Vec<LowStatement>,
}
