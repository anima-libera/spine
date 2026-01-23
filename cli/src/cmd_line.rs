use std::process::ExitCode;

pub(crate) fn process_args() -> Result<CmdArgsCases, ExitCode> {
	/// Definition of one possible command line parameter.
	struct CmdParam {
		short_name: Option<char>,
		long_name: &'static str,
		description: &'static str,
		/// Just a function that sets the parameter flag/value in `CmdArgsRaw`.
		/// Also says if the parameter is a flag or expects a string as value.
		handling: CmdParamHandling,
		/// Used to make sure there are no duplicates.
		already_seen: bool,
	}
	enum CmdParamHandling {
		Flag(&'static dyn Fn(&mut CmdArgsRaw)),
		Value(&'static dyn Fn(&mut CmdArgsRaw, String)),
	}
	macro_rules! param_value {
		(($short:expr, $long:expr, $field:ident), $description:expr) => {
			CmdParam {
				short_name: $short,
				long_name: $long,
				description: $description,
				handling: CmdParamHandling::Value(&|args: &mut CmdArgsRaw, value: String| {
					args.$field = Some(value);
				}),
				already_seen: false,
			}
		};
	}
	macro_rules! param_flag {
		(($short:expr, $long:expr, $field:ident), $description:expr) => {
			CmdParam {
				short_name: $short,
				long_name: $long,
				description: $description,
				handling: CmdParamHandling::Flag(&|args: &mut CmdArgsRaw| {
					args.$field = true;
				}),
				already_seen: false,
			}
		};
	}
	// Peak command line parameter definitions, linking names to fields of `CmdArgsRaw`.
	let mut params = [
		param_value!(
			(Some('f'), "--source-file", source_file_path),
			"Path to the source file to compile."
		),
		param_value!(
			(Some('r'), "--raw-source", raw_source),
			"Source code to compile."
		),
		param_value!(
			(Some('o'), "--output-file", output_file_path),
			"Path to the binary to be produced (default is \"b\")."
		),
		param_flag!(
			(None, "--no-output-file", no_output_file),
			"No binary file is produced."
		),
		param_flag!(
			(None, "--run", run),
			"Run the binary if successfully compiled."
		),
		param_flag!(
			(None, "--pid", pid),
			"When running the binary, print its pid."
		),
		param_flag!(
			(None, "--pid-whenever", pid_whenever),
			"Like --pid but whenever (dont wait the end)."
		),
		param_flag!((Some('v'), "--verbose", verbose), "Print more stuff."),
		param_flag!(
			(None, "--machine-code", machine_code),
			"Print machine code."
		),
		param_flag!((None, "--license", license), "Print licensing information."),
		param_flag!(
			(Some('h'), "--help", help),
			"Print this help message. Hiii =^.^="
		),
		#[cfg(feature = "lsp")]
		param_flag!(
			(None, "--lsp", lsp),
			"Be a language server, communicate via LSP."
		),
	];

	/// The first pass on the command line arguments is summed up in this.
	#[derive(Default)]
	struct CmdArgsRaw {
		source_file_path: Option<String>,
		raw_source: Option<String>,
		output_file_path: Option<String>,
		no_output_file: bool,
		run: bool,
		pid: bool,
		pid_whenever: bool,
		verbose: bool,
		machine_code: bool,
		license: bool,
		help: bool,
		#[cfg(feature = "lsp")]
		lsp: bool,
	}
	let mut raw_args = CmdArgsRaw::default();

	// Set parameter values in `raw_args` to the values provided in the command line arguments.
	// Usually i use `clap` but i ate cement today and im insane.
	let mut string_args: Vec<_> = std::env::args().collect();
	'args: loop {
		if string_args.is_empty() {
			break 'args;
		}

		let mut arg = string_args.remove(0);
		let mut value = None;
		// Handle the `--arg=value` form.
		if let Some((arg_, value_)) = arg.clone().split_once('=') {
			arg = String::from(arg_);
			value = Some(String::from(value_));
		}
		let arg = arg;

		'params: for param in params.iter_mut() {
			let matches =
				param.long_name == arg || param.short_name.is_some_and(|chr| arg == format!("-{chr}"));
			if matches {
				if param.already_seen {
					println!("Argument \"{arg}\" is set multiple times >_<");
					return Err(ExitCode::FAILURE);
				}

				// Set the arg value in `raw_args`.
				match param.handling {
					CmdParamHandling::Flag(handling) => {
						// Handle the classic `--flag` form but also the `--flag=bool` form.
						match value.as_deref() {
							None | Some("true") | Some("1") => handling(&mut raw_args),
							Some("false") | Some("0") => { /* NOT set the flag */ },
							Some(value) => {
								println!(
									"Argument \"{arg}\" is a flag (boolean), it does not make sense to set it to \"{value}\""
								);
								return Err(ExitCode::FAILURE);
							},
						}
					},
					CmdParamHandling::Value(handling) => {
						let value = if let Some(value) = value {
							// The value was given in the form `--arg=value`.
							value
						} else {
							// The value is expected to follow, like in the `--arg value` form.
							if string_args.is_empty() {
								println!("Argument \"{arg}\" expects a value following it");
								return Err(ExitCode::FAILURE);
							}
							string_args.remove(0)
						};

						handling(&mut raw_args, value);
					},
				}
				param.already_seen = true;
				break 'params;
			}
		}
	}

	// We removed arguments when they matched with parameters.
	// Now that we checked all possible parameters, remaining arguments are unexpected ones
	// that do not correspond to any parameter.
	if !string_args.is_empty() {
		// Mom can we have `String::join`? No, we have `join` at home. `join` at home:
		let len = string_args.len();
		let last_index = len - 1;
		let mut formated_args = String::new();
		for (i, arg) in string_args.iter().enumerate() {
			formated_args.push_str(format!("\"{arg}\"").as_str());
			if i != last_index {
				formated_args.push_str(", ");
			}
		}
		let plural = if 2 <= len { "s" } else { "" };
		println!("Unknown argument{plural}: {formated_args}");
		return Err(ExitCode::FAILURE);
	}

	#[cfg(feature = "lsp")]
	if raw_args.lsp {
		return Ok(CmdArgsCases::Lsp);
	}

	if raw_args.help {
		println!("Spine compiler for the Spine programming language");
		println!();
		#[cfg(not(feature = "lsp"))]
		{
			println!("This build does not include the language server feature");
			println!("and thus does not support the --lsp option.");
			println!();
		}

		println!("Options:");
		let long_name_len_max = params
			.iter()
			.map(|param| param.long_name.chars().count())
			.max()
			.unwrap();
		for param in params {
			let short_name = if let Some(chr) = param.short_name {
				format!("-{chr}")
			} else {
				String::new()
			};
			let long_name = param.long_name;
			let flag = if matches!(param.handling, CmdParamHandling::Flag(_)) {
				"(flag) "
			} else {
				""
			};
			let description = param.description;
			println!("  {short_name:2} {long_name:long_name_len_max$}  {flag}{description}");
		}

		return Err(ExitCode::SUCCESS);
	}

	if raw_args.license {
		println!("Copyright (C) 2024-2026 Jeanne Demoussel");
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
		return Err(ExitCode::SUCCESS);
	}

	let source = match (raw_args.source_file_path, raw_args.raw_source) {
		(Some(path), None) => Some(Source::FilePath(path)),
		(None, Some(raw)) => Some(Source::Raw(raw)),
		(None, None) => None,
		(Some(_), Some(_)) => {
			println!(
				"Got both a source file (-f --source-file) and raw source (-r --raw-source), \
				need at most one of them, pick one"
			);
			return Err(ExitCode::FAILURE);
		},
	};

	let output_file = match (raw_args.output_file_path, raw_args.no_output_file) {
		(Some(path), false) => Some(OutputFile::SpecifiedPath(path)),
		(None, false) => Some(OutputFile::DefaultPath),
		(None, true) => None,
		(Some(_), true) => {
			println!(
				"Got given an output file path (-o --output-file) \
				but also got told to not output a file (--no-output-file), \
				this is contradictory, pick one"
			);
			return Err(ExitCode::FAILURE);
		},
	};
	if source.is_none()
		&& let Some(OutputFile::SpecifiedPath(_)) = output_file
	{
		println!(
			"The output file given with (-o --output-file) \
			cannot be emitted because no source code was provided, \
			there is no code to compile, provide source code (--source-file or --raw-source)"
		);
		return Err(ExitCode::FAILURE);
	}

	if raw_args.run && raw_args.no_output_file {
		println!(
			"Got told to run the produced binary file (--run) \
			but also got told to not produce a binary file (--no-output-file), \
			this is contradictory, pick one"
		);
		return Err(ExitCode::FAILURE);
	}
	if raw_args.pid && raw_args.pid_whenever {
		println!(
			"Got told to print the pid at the end (--pid) \
			but also got told to print the pid at the start (--pid-whenever), \
			there can only be at most one of them, pick one"
		);
		return Err(ExitCode::FAILURE);
	}
	if (raw_args.pid || raw_args.pid_whenever) && (!raw_args.run) {
		println!(
			"Got told to print the pid of the process running the produced binary (--pid or --pid-whenever) \
			but also got told to not run the produced binary (missing --run), \
			this is contradictory, pick one"
		);
		return Err(ExitCode::FAILURE);
	}
	let run = if raw_args.pid_whenever {
		Some(Run::YesAndPrintPid(PrintPid::Whenever))
	} else if raw_args.pid {
		Some(Run::YesAndPrintPid(PrintPid::AtTheEnd))
	} else if raw_args.run {
		Some(Run::Yes)
	} else {
		None
	};

	Ok(CmdArgsCases::CompilingAndRunning(CmdArgs {
		source,
		output_file,
		run,
		verbose: raw_args.verbose,
		print_machine_code: raw_args.machine_code,
	}))
}

pub(crate) enum CmdArgsCases {
	#[cfg(feature = "lsp")]
	Lsp,
	/// Real stuff
	CompilingAndRunning(CmdArgs),
}
pub(crate) struct CmdArgs {
	pub(crate) source: Option<Source>,
	pub(crate) output_file: Option<OutputFile>,
	pub(crate) run: Option<Run>,
	pub(crate) verbose: bool,
	pub(crate) print_machine_code: bool,
}
pub(crate) enum Source {
	FilePath(String),
	Raw(String),
}
pub(crate) enum OutputFile {
	SpecifiedPath(String),
	DefaultPath,
}
pub(crate) enum PrintPid {
	AtTheEnd,
	Whenever,
}
pub(crate) enum Run {
	Yes,
	YesAndPrintPid(PrintPid),
}
