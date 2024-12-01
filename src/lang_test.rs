use std::sync::Arc;

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

	let binary_execution_result = std::process::Command::new(&dot_path).output().unwrap();
	let binary_execution_output = String::from_utf8(binary_execution_result.stdout);
	binary_execution_output.unwrap()
}

#[test]
fn print_string() {
	let name = "print_string";
	assert_eq!(
		compile_and_outputs(name, "kwprintstr \"hello\n\"; kwexit;"),
		"hello\n"
	);
}
