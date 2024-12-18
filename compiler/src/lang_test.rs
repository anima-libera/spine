use std::{sync::Arc, time::Duration};

use crate::{
	elf::chmod_x,
	lang::{compile_to_binary, compile_to_low_level, parse},
	src::SourceCode,
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
	let code = "kwps \"hello\\n\"; kwexit;";
	let expected_output = "hello\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char() {
	let name = "print_char";
	let code = "kwpc 'a'; kwpc '\\n'; kwexit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_integer_decimal() {
	let name = "print_char_from_integer_decimal";
	let code = "kwpc 97; kwpc '\\n'; kwexit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_add() {
	let name = "print_char_from_add";
	let code = "kwpc kwadd 90 7; kwpc '\\n'; kwexit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_integer_hexadecimal() {
	let name = "print_char_from_integer_hexadecimal";
	let code = "kwpc 0x61; kwpc '\\n'; kwexit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_integer_binary() {
	let name = "print_char_from_integer_binary";
	let code = "kwpc 0b1100001; kwpc '\\n'; kwexit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_integer_arbitrary_radix() {
	let name = "print_char_from_integer_arbitrary_radix";
	let code = "kwpc 0r{8}141; kwpc '\\n'; kwexit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_escape_two_hexadecimal_digits() {
	let name = "print_char_from_escape_two_hexadecimal_digits";
	let code = "kwpc '\\x61'; kwpc '\\n'; kwexit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_escape_any_hexadecimal_digits() {
	let name = "print_char_from_escape_any_hexadecimal_digits";
	let code = "kwpc '\\u{61}'; kwpc '\\n'; kwexit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_escape_any_decimal_digits() {
	let name = "print_char_from_escape_any_decimal_digits";
	let code = "kwpc '\\d{97}'; kwpc '\\n'; kwexit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}
