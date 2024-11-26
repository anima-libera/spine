#![allow(unused)]

mod asm;
mod elf;
mod imm;
mod lang;

#[cfg(test)]
mod asm_test;

use std::rc::Rc;

use elf::chmod_x;
use lang::{compile_to_binary, parse, SourceCode};

fn main() {
	let mut source_file_path = None;
	let mut raw_source = None;
	let mut output_file_path = "b".to_string();
	let mut verbose = false;
	let mut help = false;

	let args: Vec<_> = std::env::args().collect();
	if let Some(source_file_option_index) = args
		.iter()
		.position(|arg| arg == "-f" || arg == "--source-file")
	{
		source_file_path = Some(args[source_file_option_index + 1].clone());
	}
	if let Some(source_raw_option_index) = args
		.iter()
		.position(|arg| arg == "-r" || arg == "--raw-source")
	{
		raw_source = Some(args[source_raw_option_index + 1].clone());
	}
	if let Some(output_file_option_index) = args
		.iter()
		.position(|arg| arg == "-o" || arg == "--output-file")
	{
		output_file_path = args[output_file_option_index + 1].clone();
	}
	if args.iter().any(|arg| arg == "-v" || arg == "--verbose") {
		verbose = true;
	}
	if args.iter().any(|arg| arg == "-h" || arg == "--help") {
		help = true;
	}

	if help {
		println!("Options:");
		println!("  -f --source-file   Path to the source file to compile.");
		println!("  -r --raw-source    Source code to compile.");
		println!("  -o --output-file   Path to the binary to be produced (default is \"b\").");
		println!("  -v --verbose       (flag) Compiler will print more stuff.");
		println!("  -h --help          (flag) Print this help message.");
		return;
	}

	if source_file_path.is_some() && raw_source.is_some() {
		panic!("Got both a source file (-f) and raw source (-r), need at most one of them");
	}
	let source_code = if let Some(source_file_path) = source_file_path {
		if verbose {
			println!("Reading source file \"{source_file_path}\"");
		}
		Rc::new(SourceCode {
			text: std::fs::read_to_string(&source_file_path).unwrap(),
			name: source_file_path.clone(),
		})
	} else if let Some(raw_source) = raw_source {
		if verbose {
			println!("Reading raw source from command line arguments");
		}
		Rc::new(SourceCode { text: raw_source.clone(), name: "<raw source>".to_string() })
	} else {
		panic!("No source code provided")
	};

	if verbose {
		println!("Compiling to intermediate representation");
	}
	let program = parse(source_code);
	if verbose {
		println!("Compiling to machine code");
	}
	let bin = compile_to_binary(program);

	if verbose {
		println!("Machine code:");
		for byte in bin.code_segment_binary_machine_code() {
			print!("{byte:02x}");
		}
		println!();
	}

	if verbose {
		println!("Writing compiled binary to file \"{output_file_path}\"");
	}
	std::fs::write(&output_file_path, bin.to_binary()).unwrap();
	chmod_x(&output_file_path);
}
