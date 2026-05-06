use crate::{
	high::{HighInstruction, HighProgram, HighScopeStack, HighStatement, WipDef},
	keywords::KeywordWhich,
	low::{LowInstr, LowProgram, LowStatement},
	tokens::{CharacterLiteral, IntegerLiteral, Keyword, StringLiteral},
};

pub(crate) struct OperandAndReturnTypes {
	/// If operand types are `[A, B]` then it means `B` will be popped before `A`.
	pub(crate) operand_types: Vec<SpineType>,
	/// If return types are `[A, B]` then it means `A` will be pushed before `B`.
	pub(crate) return_types: Vec<SpineType>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SpineType {
	I64,
	DataAddr,
}

#[derive(Debug)]
pub(crate) enum SpineValue {
	I64(i64),
	DataAddr { offset_in_data_segment: u64 },
}

impl SpineValue {
	pub(crate) fn get_type(&self) -> SpineType {
		match self {
			SpineValue::I64(_) => SpineType::I64,
			SpineValue::DataAddr { .. } => SpineType::DataAddr,
		}
	}
}

fn compile_statement_to_low_level_statements(
	statement: &HighStatement,
	low_statements: &mut Vec<LowStatement>,
	scope_stack: &mut HighScopeStack,
) {
	match statement {
		HighStatement::Empty { .. } => {},
		HighStatement::SomeUnexpectedCharacters { .. } => panic!(),
		HighStatement::UnexpectedClosingCurly { .. } => panic!(),
		HighStatement::Block { statements, .. } => {
			scope_stack.with_pushed_empty_scope(|scope_stack| {
				for statement in statements {
					compile_statement_to_low_level_statements(statement, low_statements, scope_stack);
				}
			});
		},
		HighStatement::WipDef { identifier, value, .. } => {
			if let Some(IntegerLiteral { value: Some(Ok(value)), .. }) = value.as_deref()
				&& let Some(identifier) = identifier
			{
				scope_stack.add_wip_def_in_current_scope(WipDef {
					name: identifier.name.clone(),
					value: *value,
				});
			}
		},
		HighStatement::Code { instructions, .. } => {
			// Typecheking.
			let mut excpected_type_stack = vec![];
			for instr in instructions.iter() {
				let OperandAndReturnTypes { mut operand_types, mut return_types } =
					instr.operand_and_return_types();
				while let Some(top_return_type) = return_types.pop() {
					if let Some(top_excpected_type) = excpected_type_stack.pop() {
						assert_eq!(top_excpected_type, top_return_type, "type mismatch");
					} else {
						panic!(
							"a value of type {:?} is pushed but there is no instruction to pop it",
							top_return_type
						);
					}
				}
				excpected_type_stack.append(&mut operand_types);
			}
			assert!(
				excpected_type_stack.is_empty(),
				"values of types {:?} are expected but there is no instruction to push them",
				excpected_type_stack,
			);

			let instrs: Vec<_> = instructions
				.iter()
				.rev()
				.map(|instruction| match instruction {
					HighInstruction::IntegerLiteral(IntegerLiteral { value, .. }) => {
						LowInstr::PushConst(SpineValue::I64(*value.as_ref().unwrap().as_ref().unwrap()))
					},
					HighInstruction::CharacterLiteral(CharacterLiteral { value, .. }) => {
						LowInstr::PushConst(SpineValue::I64(*value.as_ref().unwrap() as i64))
					},
					HighInstruction::StringLiteral(StringLiteral { value, .. }) => {
						LowInstr::PushString(value.as_ref().unwrap().clone())
					},
					HighInstruction::Keyword(Keyword { keyword, .. }) => {
						match keyword.as_ref().unwrap() {
							KeywordWhich::PrintChar => LowInstr::PopI64AndPrintAsChar,
							KeywordWhich::PrintStr => LowInstr::PopI64AndPtrAndPrintAsString,
							KeywordWhich::Add => LowInstr::AddI64AndI64,
							KeywordWhich::Exit => LowInstr::Exit,
							KeywordWhich::DiscardI64 => LowInstr::PopI64AndDiscard,
							KeywordWhich::CastPointerToI64 => LowInstr::NopZeroBytes,
							KeywordWhich::Syscall => LowInstr::Syscall,
							KeywordWhich::Illegal => LowInstr::Illegal,
							KeywordWhich::WipDef => panic!(),
						}
					},
					HighInstruction::Identifier(identifier) => {
						if let Some(value) = scope_stack
							.get_wip_def(&identifier.name)
							.map(|def| def.value)
						{
							LowInstr::PushConst(SpineValue::I64(value))
						} else {
							unimplemented!("error: undefined identifier \"{}\"", identifier.name)
						}
					},
				})
				.collect();
			low_statements.push(LowStatement::Code { instrs });
		},
	}
}

pub fn high_to_low(program: &HighProgram) -> LowProgram {
	let mut low_statements = vec![];
	let mut scope_stack = HighScopeStack::new_with_one_empty_scope();
	for statement in program.statements.iter() {
		compile_statement_to_low_level_statements(statement, &mut low_statements, &mut scope_stack);
	}
	LowProgram { statements: low_statements }
}
