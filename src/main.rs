#![allow(unused)]

mod asm;
#[cfg(test)]
mod asm_test;
mod elf;
mod imm;
mod lang;
#[cfg(feature = "lsp")]
mod lsp;

use std::sync::Arc;

use elf::chmod_x;
use lang::{compile_to_binary, parse, parse_to_ast, LineStartTable, SourceCode};
#[cfg(feature = "lsp")]
use lsp::run_lsp;

fn main() {
	let mut source_file_path = None;
	let mut raw_source = None;
	let mut output_file_path = "b".to_string();
	let mut verbose = false;
	let mut help = false;
	let mut license = false;
	#[cfg(feature = "lsp")]
	let mut lsp = false;

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
	if args.iter().any(|arg| arg == "--license") {
		license = true;
	}
	#[cfg(feature = "lsp")]
	if args.iter().any(|arg| arg == "--lsp") {
		lsp = true;
	}

	#[cfg(feature = "lsp")]
	if lsp {
		run_lsp();
		return;
	}

	if help {
		println!("Spine compiler for the Spine programming language");
		println!();
		#[cfg(not(feature = "lsp"))]
		{
			println!("This build does not include the language server feature");
			println!("and thus does not support the --lsp option.");
			println!();
		}
		println!("Options:");
		println!("  -f --source-file   Path to the source file to compile.");
		println!("  -r --raw-source    Source code to compile.");
		println!("  -o --output-file   Path to the binary to be produced (default is \"b\").");
		println!("  -v --verbose       (flag) Compiler will print more stuff.");
		println!("     --license       (flag) Compiler will print licensing information.");
		println!("  -h --help          (flag) Print this help message.");
		#[cfg(feature = "lsp")]
		println!("     --lsp           (flag) Be a language server, communicate via LSP.");
		return;
	}

	if license {
		println!("Copyright (C) 2024 Jeanne DEMOUSSEL");
		println!("https://github.com/anima-libera/spine");
		print!("The Spine compiler and its VSCode extension ");
		println!("(both in source code and packaged form)");
		println!("are licensed under either of");
		println!(
			"- the Apache License, Version 2.0\
			\n  see https://www.apache.org/licenses/LICENSE-2.0"
		);
		println!(
			"- the MIT license\
			\n  see https://opensource.org/licenses/MIT"
		);
		println!("at your option.");
		return;
	}

	if source_file_path.is_some() && raw_source.is_some() {
		panic!("Got both a source file (-f) and raw source (-r), need at most one of them");
	}
	let source_code = if let Some(source_file_path) = source_file_path {
		if verbose {
			println!("Reading source file \"{source_file_path}\"");
		}
		let text = std::fs::read_to_string(&source_file_path).unwrap();
		let line_starts = LineStartTable::compute_for_text(&text);
		Arc::new(SourceCode { text, name: source_file_path.clone(), line_starts })
	} else if let Some(raw_source) = raw_source {
		if verbose {
			println!("Reading raw source from command line arguments");
		}
		let text = raw_source.clone();
		let line_starts = LineStartTable::compute_for_text(&text);
		Arc::new(SourceCode { text, name: "<raw source>".to_string(), line_starts })
	} else {
		println!("No source code provided, nothing to do.");
		println!("Run with `--help` to see the command line interface usage.");
		return;
	};

	// The good stuff starts here ^^

	if verbose {
		println!("Compiling to intermediate representation");
	}
	let program = parse(Arc::clone(&source_code));
	if verbose {
		println!("Compiling to machine code");
	}
	let bin = compile_to_binary(program);

	if verbose {
		let ast = parse_to_ast(source_code);
		dbg!(ast);
	}

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
