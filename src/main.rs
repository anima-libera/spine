#![allow(unused)] // For now, WIP stuff gets too yellow for my taste

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
	let args: Vec<_> = std::env::args().collect();
	let has_flag = |names: &[&str]| -> bool { args.iter().any(|arg| names.contains(&arg.as_str())) };
	let option_value = |names: &[&str]| -> Option<&str> {
		args
			.iter()
			.position(|arg| names.contains(&arg.as_str()))
			.map(|name_index| args[name_index + 1].as_str())
	};

	let source_file_path = option_value(&["-f", "--source-file"]);
	let raw_source = option_value(&["-r", "--raw-source"]);
	let output_file_path = option_value(&["-o", "--output-file"]).unwrap_or("b");
	let verbose = has_flag(&["-v", "--verbose"]);
	let license = has_flag(&["--license"]);
	let help = has_flag(&["-h", "--help"]);
	#[cfg(feature = "lsp")]
	let lsp = has_flag(&["--lsp"]);

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
		Arc::new(SourceCode::from_file(source_file_path))
	} else if let Some(raw_source) = raw_source {
		if verbose {
			println!("Reading raw source from command line arguments");
		}
		Arc::new(SourceCode::from_string(
			raw_source.to_string(),
			"<raw source>".to_string(),
		))
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
	std::fs::write(output_file_path, bin.to_binary()).unwrap();
	chmod_x(output_file_path);
}
