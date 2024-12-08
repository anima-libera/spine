use std::{sync::Arc, time::Duration};

use crate::{
	elf::chmod_x,
	lang::{compile_to_binary, compile_to_low_level, parse, SourceCode},
};

fn compile_and_outputs(unique_binary_name: &str, code: impl Into<String>) -> String {
	let source_code = Arc::new(SourceCode::from_string(
		code.into(),
		"<raw source>".to_string(),
	));
	let high_program = parse(Arc::clone(&source_code));
	let low_program = compile_to_low_level(&high_program);
	let bin = compile_to_binary(&low_program);
	std::fs::create_dir("test_binaries");
	let dot_path = format!("./test_binaries/{unique_binary_name}");
	std::fs::write(&dot_path, bin.to_binary()).unwrap();
	chmod_x(&dot_path);

	// Waiting a bit makes sure that we do not get `ExecutableFileBusy` errors
	// when executing the binary so soon after generating and chmoding it.
	std::thread::sleep(Duration::from_millis(20));

	let binary_execution_result = std::process::Command::new(&dot_path).output().unwrap();
	let binary_execution_output = String::from_utf8(binary_execution_result.stdout);
	binary_execution_output.unwrap()
}

#[test]
fn print_string() {
	let name = "print_string";
	let code = "kwprintstr \"hello\\n\"; kwexit;";
	let expected_output = "hello\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char() {
	let name = "print_char";
	let code = "kwprintchar 'a'; kwprintchar '\\n'; kwexit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_integer_decimal() {
	let name = "print_char_from_integer_decimal";
	let code = "kwprintchar 97; kwprintchar '\\n'; kwexit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_add() {
	let name = "print_char_from_add";
	let code = "kwprintchar kwadd 90 7; kwprintchar '\\n'; kwexit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_integer_hexadecimal() {
	let name = "print_char_from_integer_hexadecimal";
	let code = "kwprintchar 0x61; kwprintchar '\\n'; kwexit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_integer_binary() {
	let name = "print_char_from_integer_binary";
	let code = "kwprintchar 0b1100001; kwprintchar '\\n'; kwexit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_integer_arbitrary_radix() {
	let name = "print_char_from_integer_arbitrary_radix";
	let code = "kwprintchar 0r{8}141; kwprintchar '\\n'; kwexit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_escape_two_hexadecimal_digits() {
	let name = "print_char_from_escape_two_hexadecimal_digits";
	let code = "kwprintchar '\\x61'; kwprintchar '\\n'; kwexit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_escape_any_hexadecimal_digits() {
	let name = "print_char_from_escape_any_hexadecimal_digits";
	let code = "kwprintchar '\\u{61}'; kwprintchar '\\n'; kwexit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_escape_any_decimal_digits() {
	let name = "print_char_from_escape_any_decimal_digits";
	let code = "kwprintchar '\\d{97}'; kwprintchar '\\n'; kwexit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}
