use std::{collections::HashMap, sync::Arc};

use crate::{
	err::UnexpectedCharacter,
	high_to_low::{OperandAndReturnTypes, SpineType},
	keywords::KeywordWhich,
	parse_to_high::{CharacterLiteral, Identifier, IntegerLiteral, Keyword, StringLiteral},
	src::{Pos, SourceCode, Span},
};

#[derive(Debug)]
pub struct HighProgram {
	pub(crate) source: Arc<SourceCode>,
	pub statements: Vec<HighStatement>,
}

#[derive(Debug)]
pub enum HighStatement {
	/// This statement contains code (computer programming computation waow)
	/// that actually does something when executed (so NOT a declarative statement).
	Code {
		instructions: Vec<HighInstruction>,
		semicolon: Option<Pos>,
	},
	/// WIP definition of an identifier to which is associated a value given as an integer literal.
	WipDef {
		wip_def_kw_span: Span,
		identifier: Option<Identifier>,
		value: Option<Box<IntegerLiteral>>,
		semicolon: Option<Pos>,
	},
	/// A block statement containing more statements.
	Block {
		statements: Vec<HighStatement>,
		curly_open: Pos,
		curly_close: Option<Pos>,
	},
	/// A semicolon with nothing between it and the previous one or the start of file.
	/// It is valid syntax and does nothing.
	Empty {
		semicolon: Pos,
	},
	/// The compiler could not parse this piece of source code into a proper statement.
	SomeUnexpectedCharacters {
		span: Span,
		unexpected_characters: Vec<UnexpectedCharacter>,
		semicolon: Option<Pos>,
	},
	UnexpectedClosingCurly {
		pos: Pos,
	},
}

impl HighStatement {
	pub fn span(&self) -> Span {
		match self {
			HighStatement::Code { instructions, semicolon } => {
				let start = instructions.first().unwrap().span().start_pos();
				let end = if let Some(semicolon) = semicolon {
					semicolon
				} else {
					&instructions.last().unwrap().span().end_pos()
				};
				start.span_to(end).unwrap()
			},
			HighStatement::WipDef { wip_def_kw_span, identifier, value, semicolon } => {
				let start = wip_def_kw_span.start_pos();
				let end = if let Some(semicolon) = semicolon {
					semicolon
				} else if let Some(value) = value {
					&value.span.end_pos()
				} else if let Some(identifier) = identifier {
					&identifier.span.end_pos()
				} else {
					&wip_def_kw_span.end_pos()
				};
				start.span_to(end).unwrap()
			},
			HighStatement::Block { statements, curly_open, curly_close } => {
				let end = if let Some(curly_close) = curly_close {
					curly_close
				} else if let Some(last_statement) = statements.last() {
					&last_statement.span().end_pos()
				} else {
					curly_open
				};
				curly_open.span_to(end).unwrap()
			},
			HighStatement::Empty { semicolon } => semicolon.clone().one_char_span(),
			HighStatement::SomeUnexpectedCharacters { span, .. } => span.clone(),
			HighStatement::UnexpectedClosingCurly { pos, .. } => pos.clone().one_char_span(),
		}
	}
}

#[derive(Debug)]
pub enum HighInstruction {
	IntegerLiteral(IntegerLiteral),
	CharacterLiteral(CharacterLiteral),
	StringLiteral(StringLiteral),
	Keyword(Keyword),
	Identifier(Identifier),
}

impl HighInstruction {
	pub fn span(&self) -> &Span {
		match self {
			HighInstruction::IntegerLiteral(t) => &t.span,
			HighInstruction::CharacterLiteral(t) => &t.span,
			HighInstruction::StringLiteral(t) => &t.span,
			HighInstruction::Keyword(t) => &t.span,
			HighInstruction::Identifier(t) => &t.span,
		}
	}

	/// Order:
	/// - If operand types are `[A, B]` then it means `B` will be popped before `A`.
	/// - If return types are `[A, B]` then it means `A` will be pushed before `B`.
	pub(crate) fn operand_and_return_types(&self) -> OperandAndReturnTypes {
		match self {
			HighInstruction::IntegerLiteral(_) => {
				OperandAndReturnTypes { operand_types: vec![], return_types: vec![SpineType::I64] }
			},
			HighInstruction::CharacterLiteral(_) => {
				OperandAndReturnTypes { operand_types: vec![], return_types: vec![SpineType::I64] }
			},
			HighInstruction::StringLiteral(_) => OperandAndReturnTypes {
				operand_types: vec![],
				return_types: vec![SpineType::DataAddr, SpineType::I64],
			},
			HighInstruction::Keyword(Keyword { keyword, .. }) => match keyword.as_ref().unwrap() {
				KeywordWhich::PrintChar => {
					OperandAndReturnTypes { operand_types: vec![SpineType::I64], return_types: vec![] }
				},
				KeywordWhich::PrintStr => OperandAndReturnTypes {
					operand_types: vec![SpineType::DataAddr, SpineType::I64],
					return_types: vec![],
				},
				KeywordWhich::Add => OperandAndReturnTypes {
					operand_types: vec![SpineType::I64, SpineType::I64],
					return_types: vec![SpineType::I64],
				},
				KeywordWhich::Exit => {
					OperandAndReturnTypes { operand_types: vec![], return_types: vec![] }
				},
				KeywordWhich::DiscardI64 => {
					OperandAndReturnTypes { operand_types: vec![SpineType::I64], return_types: vec![] }
				},
				KeywordWhich::CastPointerToI64 => OperandAndReturnTypes {
					operand_types: vec![SpineType::DataAddr],
					return_types: vec![SpineType::I64],
				},
				KeywordWhich::Syscall => OperandAndReturnTypes {
					operand_types: std::iter::repeat_n(SpineType::I64, 7).collect(),
					return_types: vec![SpineType::I64, SpineType::I64],
				},
				KeywordWhich::Illegal => {
					OperandAndReturnTypes { operand_types: vec![], return_types: vec![] }
				},
				KeywordWhich::WipDef => {
					panic!("defintion keyword does not have a type signature")
				},
			},
			HighInstruction::Identifier(_) => {
				// WIP: For now the only definition statement possible allows only integers,
				// so the only thing that an indentifier can evaluate to is an integer.
				OperandAndReturnTypes { operand_types: vec![], return_types: vec![SpineType::I64] }
			},
		}
	}
}

pub(crate) struct WipDef {
	pub(crate) name: String,
	// WIP!
	pub(crate) value: i64,
}

pub(crate) struct HighScopeContext {
	pub(crate) wip_defs: HashMap<String, WipDef>,
}

pub(crate) struct HighScopeStack {
	/// Scope stack!
	/// Last element is the current scope, second last element is the closest enclosing scope,
	/// first element is the outermost enclosing scope.
	pub(crate) scopes: Vec<HighScopeContext>,
}

impl HighScopeContext {
	fn new() -> HighScopeContext {
		HighScopeContext { wip_defs: HashMap::default() }
	}
}

impl HighScopeStack {
	pub(crate) fn new_with_one_empty_scope() -> HighScopeStack {
		HighScopeStack { scopes: vec![HighScopeContext::new()] }
	}

	pub(crate) fn with_pushed_empty_scope<T>(
		&mut self,
		f: impl FnOnce(&mut HighScopeStack) -> T,
	) -> T {
		self.scopes.push(HighScopeContext::new());
		let res = f(self);
		self.scopes.pop();
		res
	}

	pub(crate) fn add_wip_def_in_current_scope(&mut self, def: WipDef) {
		self
			.scopes
			.last_mut()
			.unwrap()
			.wip_defs
			.insert(def.name.clone(), def);
	}

	pub(crate) fn get_wip_def(&self, name: &String) -> Option<&WipDef> {
		self
			.scopes
			.iter()
			.rev()
			.find_map(|scope| scope.wip_defs.get(name))
	}
}
