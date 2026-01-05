use std::sync::Arc;

use spine_compiler::{
	elf::chmod_x,
	lang::{compile_to_binary, compile_to_low_level, parse},
	src::SourceCode,
};
#[cfg(feature = "lsp")]
use spine_language_server::run_lsp;

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
	let run = has_flag(&["--run"]);
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
		println!("     --run           (flag) Run the binary if successfully compiled.");
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
		let Some(source_code) = SourceCode::from_file(source_file_path) else {
			println!("Failed to read source file \"{source_file_path}\"");
			return;
		};
		Arc::new(source_code)
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
		println!("Parsing to high level internal representation");
	}
	let high_program = parse(Arc::clone(&source_code));

	let (errors, warnings) = high_program.get_errors_and_warnings();
	if !errors.is_empty() {
		if verbose {
			println!("There are compile-time errors, compilation is aborted");
		}
		for error in errors {
			error.print();
		}
		return;
	}
	if !warnings.is_empty() && verbose {
		println!("There are compile-time warnings but it is no big deal");
	}
	for warning in warnings {
		warning.print();
	}

	if verbose {
		println!("Compiling to low level internal representation");
	}
	let low_program = compile_to_low_level(&high_program);
	if verbose {
		println!("Compiling to quasi machine code");
	}
	let bin = compile_to_binary(&low_program);
	if verbose {
		println!("Machine code:");
		for byte in bin.code_segment_binary_machine_code() {
			print!("{byte:02x}");
		}
		println!();
	}

	if verbose {
		println!("Writing binary to file \"{output_file_path}\"");
	}
	std::fs::write(output_file_path, bin.to_binary()).unwrap();
	chmod_x(output_file_path);

	if run {
		let command = format!("./{output_file_path}");
		let _ = std::process::Command::new(command).spawn();
	}
}
