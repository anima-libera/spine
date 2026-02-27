use std::borrow::Cow;

#[derive(Debug, Clone, Copy)]
pub enum KeywordWhich {
	/// Pops an i64 and prints the ASCII character it represents.
	PrintChar,
	/// Pops an i64 (string length) then pops a pointer (to the string content),
	/// then prints the UTF-8 encoded string.
	/// It works well with string literals (`printstr "uwu\n"` does what we expect).
	PrintStr,
	/// Pops two i64 values, add them together, and push the result.
	Add,
	/// Terminates the process execution by calling the exit syscall, with 0 as the exit code.
	Exit,
	DiscardI64,
	/// Casts a pointer to i64. Compiles into a nop.
	CastPointerToI64,
	/// Performs a syscall with the syscall number and the maximum number of arguments, all raw i64 types.
	/// Pops 6 i64 arguments from last to first, then pops the syscall number.
	/// Pushes the second return value (only used by the pipe syscall on some architectures)
	/// then pushes the (first) return value.
	Syscall,
	/// Executes the illegal x86_64 instruction `UD2`.
	Illegal,
	/// WIP compile-time definition!
	WipDef,
}

pub struct KeywordInLang {
	pub word: Cow<'static, str>,
	pub which: KeywordWhich,
	pub instr_doc: Option<KeywordInstrDoc>,
}

pub struct KeywordInstrDoc {
	pub signature: Cow<'static, str>,
	pub short_doc: Cow<'static, str>,
	pub long_doc: Cow<'static, str>,
}

macro_rules! keyword {
	($word:literal, $which:ident) => {
		KeywordInLang {
			word: Cow::Borrowed($word),
			which: KeywordWhich::$which,
			instr_doc: None,
		}
	};
}

macro_rules! keyword_instr {
	($word:literal, $which:ident, $signature:literal, $short_doc:literal, $long_doc:literal) => {
		KeywordInLang {
			word: Cow::Borrowed($word),
			which: KeywordWhich::$which,
			instr_doc: Some(KeywordInstrDoc {
				signature: Cow::Borrowed($signature),
				short_doc: Cow::Borrowed($short_doc),
				long_doc: Cow::Borrowed($long_doc),
			}),
		}
	};
}

pub const DEFAULT_KEYWORDS: [KeywordInLang; 9] = [
	keyword_instr!(
		"pc",
		PrintChar,
		"(char --> )",
		"print character",
		"\
			```spine\n\
			pc\n\
			```\n\
			*{Keyword}*\n\n\
			Calls the `write` syscall with a string made of the one provided character."
	),
	keyword_instr!(
		"ps",
		PrintStr,
		"(ptr len --> )",
		"print string",
		"\
			```spine\n\
			ps\n\
			```\n\
			*{Keyword}*\n\n\
			Calls the `write` syscall with the given pointer and length."
	),
	keyword_instr!(
		"add",
		Add,
		"(a b --> sum)",
		"add two numbers",
		"\
			```spine\n\
			add\n\
			```\n\
			*{Keyword}*\n\n\
			Pops two numbers then pushes the result of their addition."
	),
	keyword_instr!(
		"exit",
		Exit,
		"( --> )",
		"terminate execution",
		"\
			```spine\n\
			exit\n\
			```\n\
			*{Keyword}*\n\n\
			Calls the `exit` syscall, which terminates the process execution."
	),
	keyword_instr!(
		"di",
		DiscardI64,
		"(number --> )",
		"discard a number",
		"\
			```spine\n\
			di\n\
			```\n\
			*{Keyword}*\n\n\
			Pops a number and discards it."
	),
	keyword_instr!(
		"cpi",
		CastPointerToI64,
		"(pointer --> number)",
		"cast pointer to number",
		"\
			```spine\n\
			cpi\n\
			```\n\
			*{Keyword}*\n\n\
			Just casts the type of the top value from address to number. \
			Compile-time only, codegens down to nothing."
	),
	keyword_instr!(
		"sys",
		Syscall,
		"(s a1 a2 a3 a4 a5 a6 --> ret1 ret2)",
		"syscall",
		"\
			```spine\n\
			sys\n\
			```\n\
			*{Keyword}*\n\n\
			Pops 6 syscall arguments (last argument is popped first, etc), \
			then pops a syscall number, then runs the syscall, \
			then pushes the result 2, then the result.\n\n\
			Result 2 is meaningless and should always be discarded, \
			expect in the very specific case of the pipe syscall (syscall number 22) \
			on some specific architectures where it happens to return two numbers."
	),
	keyword_instr!(
		"ill",
		Illegal,
		"( --> )",
		"illegal",
		"\
			```spine\n\
			ill\n\
			```\n\
			*{Keyword}*\n\n\
			Executes the `UD2` illegal instruction, an explosion follows."
	),
	keyword!("def", WipDef),
];
