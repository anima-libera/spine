use std::{sync::Arc, time::Duration};

use crate::{
	elf::chmod_x, high_to_low::high_to_low, low_to_highasm::low_to_binary_plan, src::SourceCode,
	tokens_to_high::parse_to_high,
};

fn compile_and_outputs(unique_binary_name: &str, code: impl Into<String>) -> String {
	let source_code = Arc::new(SourceCode::from_string(
		code.into(),
		"<raw source>".to_string(),
	));
	let high_program = parse_to_high(Arc::clone(&source_code));
	let low_program = high_to_low(&high_program);
	let bin = low_to_binary_plan(&low_program);
	std::fs::create_dir("test_binaries").unwrap();
	let dot_path = format!("./test_binaries/{unique_binary_name}");
	std::fs::write(&dot_path, bin.to_binary()).unwrap();
	chmod_x(&dot_path).unwrap();

	// Waiting a bit makes sure that we do not get `ExecutableFileBusy` errors
	// when executing the binary so soon after generating and chmoding it.
	std::thread::sleep(Duration::from_millis(20));

	let binary_execution_result = std::process::Command::new(&dot_path).output().unwrap();
	assert!(
		binary_execution_result.status.success(),
		"binary execution status indicates failure"
	);
	let binary_execution_output = String::from_utf8(binary_execution_result.stdout);
	binary_execution_output.unwrap()
}

#[test]
fn print_string() {
	let name = "print_string";
	let code = "ps \"hello\\n\"; exit;";
	let expected_output = "hello\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char() {
	let name = "print_char";
	let code = "pc 'a'; pc '\\n'; exit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_integer_decimal() {
	let name = "print_char_from_integer_decimal";
	let code = "pc 97; pc '\\n'; exit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_add() {
	let name = "print_char_from_add";
	let code = "pc add 90 7; pc '\\n'; exit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_integer_hexadecimal() {
	let name = "print_char_from_integer_hexadecimal";
	let code = "pc 0x61; pc '\\n'; exit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_integer_binary() {
	let name = "print_char_from_integer_binary";
	let code = "pc 0b1100001; pc '\\n'; exit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_integer_arbitrary_radix() {
	let name = "print_char_from_integer_arbitrary_radix";
	let code = "pc 0r{8}141; pc '\\n'; exit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_escape_two_hexadecimal_digits() {
	let name = "print_char_from_escape_two_hexadecimal_digits";
	let code = "pc '\\x61'; pc '\\n'; exit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_escape_any_hexadecimal_digits() {
	let name = "print_char_from_escape_any_hexadecimal_digits";
	let code = "pc '\\u{61}'; pc '\\n'; exit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_char_from_escape_any_decimal_digits() {
	let name = "print_char_from_escape_any_decimal_digits";
	let code = "pc '\\d{97}'; pc '\\n'; exit;";
	let expected_output = "a\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn print_string_with_manual_syscall() {
	let name = "print_string_with_manual_syscall";
	let code = "di di sys 0 0 0 6 cpi di \"hello\\n\" 1 1; exit;";
	let expected_output = "hello\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}

#[test]
fn addition() {
	let name = "addition";
	let code = "pc add 'a' 1; pc '\\n'; exit;";
	let expected_output = "b\n";
	assert_eq!(compile_and_outputs(name, code), expected_output);
}
