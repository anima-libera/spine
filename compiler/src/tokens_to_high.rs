use std::sync::Arc;

use crate::{
	high::{HighInstruction, HighProgram, HighStatement},
	keywords::KeywordWhich,
	src::{Reader, SourceCode},
	src_to_tokens::Tokenizer,
	tokens::{Keyword, Token},
};

fn parse_statement(tokenizer: &mut Tokenizer) -> HighStatement {
	let first_token = tokenizer.peek_token().unwrap();

	if matches!(first_token, Token::CurlyOpen(_)) {
		return parse_block_statement(tokenizer);
	}

	if matches!(
		first_token,
		Token::Keyword(Keyword { keyword: Some(KeywordWhich::WipDef), .. })
	) {
		return parse_wip_def_statement(tokenizer);
	}

	let mut instructions = vec![];
	let mut unexpected_characters = vec![];
	let semicolon = 'instructions: loop {
		if matches!(tokenizer.peek_token(), Some(Token::CurlyClose(_))) {
			// Missing terminating semicolon.
			break 'instructions None;
		}
		match tokenizer.pop_token() {
			Some(Token::IntegerLiteral(integer_literal)) => {
				instructions.push(HighInstruction::IntegerLiteral(integer_literal));
			},
			Some(Token::CharacterLiteral(character_literal)) => {
				instructions.push(HighInstruction::CharacterLiteral(character_literal));
			},
			Some(Token::StringLiteral(string_literal)) => {
				instructions.push(HighInstruction::StringLiteral(string_literal))
			},
			Some(Token::Keyword(keyword)) => {
				instructions.push(HighInstruction::Keyword(keyword));
			},
			Some(Token::Identifier(identifier)) => {
				instructions.push(HighInstruction::Identifier(identifier));
			},
			Some(Token::Comment(_)) => {},
			Some(Token::Whitespace(_)) => {},
			Some(Token::Semicolon(span)) => break 'instructions Some(span),
			Some(Token::CurlyOpen(_span)) => unreachable!(),
			Some(Token::CurlyClose(_span)) => unreachable!(),
			Some(Token::UnexpectedCharacter(unexpected)) => {
				unexpected_characters.push(unexpected);
			},
			None => {
				if instructions.is_empty() {
					panic!("expected statement but found end-of-file");
				} else {
					// Missing terminating semicolon.
					break 'instructions None;
				}
			},
		};
	};

	if !unexpected_characters.is_empty() {
		let mut start = unexpected_characters.first().unwrap().pos.clone();
		let mut end = unexpected_characters.last().unwrap().pos.clone();
		if !unexpected_characters.is_empty() {
			start = start.min(&unexpected_characters.first().unwrap().pos);
			end = end.max(&unexpected_characters.last().unwrap().pos);
		}
		if let Some(semicolon) = &semicolon {
			end = semicolon.clone();
		}
		let span = start.span_to(&end).unwrap();
		HighStatement::SomeUnexpectedCharacters { span, unexpected_characters, semicolon }
	} else if instructions.is_empty() {
		HighStatement::Empty { semicolon: semicolon.unwrap() }
	} else {
		HighStatement::Code { instructions, semicolon }
	}
}

fn parse_block_statement(tokenizer: &mut Tokenizer) -> HighStatement {
	let Token::CurlyOpen(curly_open) = tokenizer.pop_token().unwrap() else {
		panic!()
	};
	let mut statements = vec![];
	let curly_close = loop {
		let first_token = tokenizer.peek_token();
		if let Some(Token::CurlyClose(curly_close)) = first_token {
			let curly_close = curly_close.clone();
			tokenizer.pop_token();
			break Some(curly_close.clone());
		} else if first_token.is_none() {
			break None;
		}
		let statement = parse_statement(tokenizer);
		statements.push(statement);
	};
	HighStatement::Block { statements, curly_open, curly_close }
}

fn parse_wip_def_statement(tokenizer: &mut Tokenizer) -> HighStatement {
	let Token::Keyword(Keyword {
		keyword: Some(KeywordWhich::WipDef), span: wip_def_kw_span, ..
	}) = tokenizer.pop_token().unwrap()
	else {
		panic!()
	};

	let identifier = if matches!(tokenizer.peek_token(), Some(Token::Identifier(_))) {
		let Some(Token::Identifier(identifier)) = tokenizer.pop_token() else {
			panic!()
		};
		Some(identifier)
	} else {
		None
	};

	let value = if matches!(tokenizer.peek_token(), Some(Token::IntegerLiteral(_))) {
		let Some(Token::IntegerLiteral(value)) = tokenizer.pop_token() else {
			panic!()
		};
		Some(Box::new(value))
	} else {
		None
	};

	let semicolon = if matches!(tokenizer.peek_token(), Some(Token::Semicolon(_))) {
		let Some(Token::Semicolon(semicolon)) = tokenizer.pop_token() else {
			panic!()
		};
		Some(semicolon)
	} else {
		None
	};

	HighStatement::WipDef { wip_def_kw_span, identifier, value, semicolon }
}

fn parse_program(tokenizer: &mut Tokenizer) -> HighProgram {
	let mut statements = vec![];
	while tokenizer.peek_token().is_some() {
		if let Some(Token::CurlyClose(curly_close)) = tokenizer.peek_token() {
			let curly_close = curly_close.clone();
			tokenizer.pop_token();
			statements.push(HighStatement::UnexpectedClosingCurly { pos: curly_close });
		} else {
			let statement = parse_statement(tokenizer);
			statements.push(statement);
		}
	}
	let source = Arc::clone(tokenizer.reader.source());
	HighProgram { source, statements }
}

pub fn parse_to_high(source: Arc<SourceCode>) -> HighProgram {
	let reader = Reader::new(Arc::clone(&source));
	let mut tokenizer = Tokenizer::new(reader);
	parse_program(&mut tokenizer)
}
