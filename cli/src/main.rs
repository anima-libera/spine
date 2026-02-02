#[cfg(target_family = "unix")]
use std::os::unix::process::ExitStatusExt;
use std::{process::ExitCode, sync::Arc};

use spine_compiler::{
	elf::chmod_x,
	lang::{compile_to_binary, compile_to_low_level, parse},
	src::SourceCode,
};
#[cfg(feature = "lsp")]
use spine_language_server::run_lsp;

use crate::cmd_line::{CmdArgsCases, OutputFile, PrintPid, Run, Source, process_args};

mod cmd_line;

fn main() -> ExitCode {
	let args_result = process_args();
	let args_cases = match args_result {
		Err(exit_code) => return exit_code,
		Ok(args_cases) => args_cases,
	};

	let args = match args_cases {
		#[cfg(feature = "lsp")]
		CmdArgsCases::Lsp => {
			run_lsp();
			return ExitCode::SUCCESS;
		},
		CmdArgsCases::CompilingAndRunning(args) => args,
	};

	// All the simple cases and command line argument stuff has been taken care of.
	// What remains is the real code, the compiling and running!

	let source_code = match args.source {
		Some(Source::FilePath(path)) => {
			if args.verbose {
				println!("Reading source file \"{path}\"");
			}
			let Some(source_code) = SourceCode::from_file(&path) else {
				println!("Failed to read source file \"{path}\"");
				return ExitCode::FAILURE;
			};
			Arc::new(source_code)
		},
		Some(Source::Raw(raw)) => {
			if args.verbose {
				println!("Reading raw source from command line arguments");
			}
			Arc::new(SourceCode::from_string(
				raw.to_string(),
				"<raw source>".to_string(),
			))
		},
		None => {
			println!("No source code provided, nothing to do.");
			println!("Run with `--help` to see the command line interface usage.");
			return ExitCode::SUCCESS;
		},
	};

	// The good stuff starts here
	// Compiling to machine code in an ELF

	if args.verbose {
		println!("Parsing to high level internal representation");
	}
	let high_program = parse(Arc::clone(&source_code));

	let (errors, warnings) = high_program.get_errors_and_warnings();
	if !errors.is_empty() {
		if args.verbose {
			println!("There are compile-time errors, compilation is aborted");
		}
		for error in errors {
			error.print();
		}
		return ExitCode::FAILURE;
	}
	if !warnings.is_empty() && args.verbose {
		println!("There are compile-time warnings but it is no big deal");
	}
	for warning in warnings {
		warning.print();
	}

	if args.verbose {
		println!("Compiling to low level internal representation");
	}
	let low_program = compile_to_low_level(&high_program);

	if args.verbose {
		println!("Compiling to almost machine code");
	}
	let bin = compile_to_binary(&low_program);

	if args.verbose {
		println!("Generating the ELF x86_64 executable and the machine code");
	}
	let elf = bin.to_binary();

	if args.print_machine_code && !args.print_asm {
		// Just print the machine code, raw, no annotations.
		println!("Machine code:");
		for byte in bin.code_segment_binary_machine_code() {
			print!("{byte:02x}");
		}
		println!();
	}

	if args.print_asm && !args.print_machine_code {
		// Just print the assembly-ish, without the corresponding machine code.
		println!("Assembly-ish representation of machine code:");
		for (_instr_binary, instr) in bin.code_segment_binary_and_asm_machine_code() {
			println!("{instr}");
		}
	}

	if args.print_machine_code && args.print_asm {
		// Print the machine code annotated with corresponding assembly-ish instructions.
		println!("Machine code and assembly-ish:");
		let instr_vec = bin.code_segment_binary_and_asm_machine_code();
		if let Some(instr_binary_max) = instr_vec
			.iter()
			.map(|(instr_binary, _instr)| instr_binary.len())
			.max()
		{
			let padding = instr_binary_max * 2;
			for (instr_binary, instr) in instr_vec {
				let mut binary_as_str = String::new();
				for byte in instr_binary {
					binary_as_str += &format!("{byte:02x}");
				}
				println!("{binary_as_str:padding$}  {instr}");
			}
		}
	}

	// Emitting the ELF in an executable file

	let Some(args_output_file) = args.output_file else {
		if args.verbose {
			println!("Not writing to a file");
		}
		return ExitCode::SUCCESS;
	};

	let output_file_path = match args_output_file {
		OutputFile::SpecifiedPath(ref path) => path,
		OutputFile::DefaultPath => &String::from("b"),
	};
	if args.verbose {
		println!(
			"Writing binary to file \"{output_file_path}\"{}",
			if matches!(args_output_file, OutputFile::DefaultPath) {
				" (defualt name)"
			} else {
				""
			}
		);
	}
	let write_result = std::fs::write(output_file_path, elf);
	if let Err(error) = write_result {
		println!("Error when writing to file \"{output_file_path}\": {error}");
		return ExitCode::FAILURE;
	}
	let chmod_result = chmod_x(output_file_path);
	if let Err(error) = chmod_result {
		println!("Error when making the file \"{output_file_path}\" executable: {error}");
		return ExitCode::FAILURE;
	}

	// Running the generated executable

	let Some(args_run) = args.run else {
		return ExitCode::SUCCESS;
	};

	if args.verbose {
		println!("Running \"{output_file_path}\"");
	}
	let command = format!("./{output_file_path}");
	println!("\x1b[36m{command}\x1b[39m");
	let process = std::process::Command::new(command).spawn();
	let mut process = match process {
		Err(error) => {
			println!("Error when attempting to run \"{output_file_path}\": {error}");
			return ExitCode::FAILURE;
		},
		Ok(process) => process,
	};
	let pid = process.id();
	if let Run::YesAndPrintPid(PrintPid::Whenever) = args_run {
		println!("\x1b[32mRunning with pid {}\x1b[39m", pid);
	}
	let status = process.wait();
	// The process has ended
	if let Run::YesAndPrintPid(PrintPid::AtTheEnd) = args_run {
		println!("\x1b[32mRan with pid {}\x1b[39m", pid);
	}
	let status = match status {
		Err(error) => {
			println!("Error when running \"{output_file_path}\": {error}");
			return ExitCode::FAILURE;
		},
		Ok(status) => status,
	};
	if status.success() {
		return ExitCode::SUCCESS;
	}
	// Print whats wrong in red (blood!)
	if let Some(exit_code) = status.code() {
		println!("\x1b[31mExit code {exit_code}\x1b[39m")
	}
	#[cfg(target_family = "unix")]
	#[allow(clippy::manual_map)]
	{
		enum TermOrStop {
			Terminated,
			Stopped,
		}
		if let Some((signal_code, term_or_stop)) = {
			if let Some(signal_code) = status.signal() {
				Some((signal_code, TermOrStop::Terminated))
			} else if let Some(signal_code) = status.stopped_signal() {
				Some((signal_code, TermOrStop::Stopped))
			} else {
				None
			}
		} {
			let signal = if let Some(signal_name) = signal_name(signal_code) {
				signal_name.to_string()
			} else {
				signal_code.to_string()
			};
			let term_or_stop = match term_or_stop {
				TermOrStop::Terminated => "Terminated",
				TermOrStop::Stopped => "Stopped",
			};
			println!("\x1b[31m{term_or_stop} by signal {signal}\x1b[39m");
		}
	}
	ExitCode::FAILURE
}

fn signal_name(signal_code: i32) -> Option<&'static str> {
	match signal_code {
		1 => Some("SIGHUP"),
		2 => Some("SIGINT"),
		3 => Some("SIGQUIT"),
		4 => Some("SIGILL"),
		5 => Some("SIGTRAP"),
		6 => Some("SIGABRT"),
		7 => Some("SIGBUS"),
		8 => Some("SIGFPE"),
		9 => Some("SIGKILL"),
		10 => Some("SIGUSR1"),
		11 => Some("SIGSEGV"),
		12 => Some("SIGUSR2"),
		13 => Some("SIGPIPE"),
		14 => Some("SIGALRM"),
		15 => Some("SIGTERM"),
		16 => Some("SIGSTKFLT"),
		17 => Some("SIGCHLD"),
		18 => Some("SIGCONT"),
		19 => Some("SIGSTOP"),
		20 => Some("SIGTSTP"),
		21 => Some("SIGTTIN"),
		22 => Some("SIGTTOU"),
		23 => Some("SIGURG"),
		24 => Some("SIGXCPU"),
		25 => Some("SIGXFSZ"),
		26 => Some("SIGVTALRM"),
		27 => Some("SIGPROF"),
		28 => Some("SIGWINCH"),
		29 => Some("SIGIO"),
		30 => Some("SIGPWR"),
		31 => Some("SIGSYS"),
		_ => None,
	}
}
