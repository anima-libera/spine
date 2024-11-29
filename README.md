# Spine

Compiled programming language in the making.
It compiles directly to **ELF x86_64**
(linux binary executable that only works on 64-bit Intel and AMD CPUs).

The generated machine code is of questionable quality, but it works!

## Installing

This is a Rust project, so you need Rust and `cargo`, which can be installed from [here](https://www.rust-lang.org/tools/install).

Install:
```sh
cargo install --git https://github.com/anima-libera/spine.git
```

or (after `git clone`-ing or downloading the repo)
```sh
cargo install --path .
```

Installing is necessary for the VSCode extension to use the language server.

## Usage

Usage:
```sh
spine -f test.spine -o binary & ./binary
```
(replace `spine` with `cargo run --` if you just `git clone`-ed or downloaded the repo)

Can also provide raw source code in command line:
```sh
spine -r "\`printstr \"haiii :3\\n\"; \`exit" && ./b
```
(woa what an amazing feature!!!¡¡)

(default output binary path is "b" when not provided via `-o`)

## VSCode extension

The extension is developped in `vscode-extension/spine-lang`.

It is packaged in `vscode-extension/spine-lang/spine-lang-0.0.1.vsix`.

The extension's VSIX file can be installed in VSCode
- either in the VSCode GUI, by going to `Extensions > ··· > Install from VSIX...`
- or in the VSCode CLI, by running
```sh
code --install-extension vscode-extension/spine-lang/spine-lang-0.0.1.vsix
```

The VSCode extension uses a language server (fancy!) which is in the Spine compiler. The VSCode extension runs the language server by running a shell command with the name `spine`, which only works if Spine is installed "globally", see [how to install](#installing).

## Not building the language server

The language server part of the Spine compiler binary is optional (and enabled by default), opting out of it produces a Spine compiler that has all the features *except* being able to be a language server for the VSCode extension.

The language server part of the code is gated behind the cargo feature `lsp` which is enabled by default. To build the thing without that feature, simply use the `--no-default-features` cargo option (see [here](https://doc.rust-lang.org/cargo/reference/features.html#the-default-feature) for more about this cargo option and cargo features).

Building without the language server part makes the compiler binary significantly smaller, and improves compile time by quite a lot (both the first build and the incremental builds), it can be a good idea to build with `--no-default-features` when iterating over the code and building with high frequency or when a small build is desirable.

## Spine programming language tour

```
`printstr "haiii world!!!\n"; -- uwu
`exit;                        -- dont forget, or else segfault
```

### Features and syntax

#### Comments

- `-- uwu` line comment
- `--- uwu` documentation line comment
- `--{ uwu }` block comment
- `---{ uwu }` documentation block comment

#### Statements

Statements are separated by `;` (semicolon).

Here is an example of statement: `` `printstr "uwu\n"; ``

A Spine program is a sequence of statements, executed from left to right.
However, inside a statement, the instructions can be understood as being executed from right to left.

In the piece of code `` `printchar 'a'; `printchar 'b'; `` the satement that prints `a` is executed before the statement that prints `b` (as we would expect), but inside a statement it is the instruction `'a'` that is executed before `` `printchar ``.
`'a'` pushes the character `a` on the stack, and `` `printchar `` pops it and prints it.

#### Typechecking

Spine is typechecked (!), literally 1984.

Inside a statement, instructions that consume operands of certain types do expect these values to be pushed on the stack by instructions on the right (that will be executed before). No value pushed during a statement shall remain on the stack at the end of that statement, and all operands shall be provided.

#### Instructions

Instruction operands and result values are documented with the syntax `(a b --> c d)` meaning that the instruction consumes (pops) `b` (on the top when the instruction executes) then `a` and it produces (pushes) `c` then `d` (so that `d` is on the top when the instruction finishes).

Some of the instructions syntax are keywords that begin with the character `` ` `` (grave accent), this is not a markdown typo, it is just the syntax used by internal keywords (keywords that are intended to be used only by the future stdlib implementation, or only for testing, but that are documented anyway because a definitive proper syntax is not yet implemented).

- `` `exit `` ( --> ) calls the `exit` syscall which terminates the process. It is expected at the end of Spine programs, or else execution will get past the end and into non-machine-code memory (which would cause undefined behavior, probably a segfault due to virtual memory pages after that not being allocated or marked as executable).
- `` `printchar `` (character --> ) prints the character to stdout.
- `` `printstr `` (pointer n --> ) prints n characters of the string pointed to by the pointer. If the string is shorter than n then undefined behavior occurs (the stuff after gets printed too, hopefully it is valid utf-8 >w< and hopefully it is in allocated virtual memory pages marked as readable).
- `` `add `` (n m --> r) pops and adds n and m then pushes the result.
- `41` ( --> 41) pushes 41. It works for other unsigned numbers too. Can be in hexadecimal (when prefixed by `0x`), in binary (when prefixed by `0b`), or in some arbitrary radix (when prefixed by `0r{8}` for octal for example); the `x`, `b` and `r` can be uppercase.
- `'a'` ( --> a) pushes the character `a`. It works for other characters too. See the [character escape syntax](#character-escape).
- `"awawa"` ( --> pointer len) pushes a pointer to the begining of static data that is the utf-8 encoding of `awawa`, and then pushes the length (of the utf-8 encoding, in bytes) of that string. It works for other strings too. See the [character escape syntax](#character-escape). Note how it works nicely with `` `printstr ``.

#### Character escape

- `\\` backslash
- `\'` single quote
- `\"` double quote
- `\e` escape (`0x1b` ASCII code)
- `\a` bell (`0x07` ASCII code)
- `\b` backspace (`0x08` ASCII code)
- `\n` newline
- `\t` tab (horizontal)
- `\r` carriage return
- `\v` vertical tab
- `\f` page break (`0x0c` ASCII code)
- `\?` replacement character `�`
- `\0` null (`0` ASCII code)
- `\x1B` character of provided ASCII code written as *exactly 2 hexadecimal digits* (here `1b`), the `x` can be uppercase
- `\u{fffd}` character of provided Unicode code point written in *hexadecimal* (of arbitrary length) (here `fffd`), the `u` can be uppercase
- `\d{65533}` character of provided Unicode code point written in *decimal* (of arbitrary length) (here `65533`), the `d` can be uppercase

The hexadecimal digits can be uppercase.

### List of features

- Compiled to machine language (not to llvm-ir, not to textual assembly, not to some other compiled language, but to actual binary like our ancestors used to write (no they didn't xd this is mostly for fun, and to get the achievement)). The machine code generation does not use dependencies (that explains why it is bad and unoptimized).
- The parser is also hand written, no dependencies there, like the Egyptians used to do 3000 BC.
- VSCode extension (with language server!).
- Numbers and strings. Strings can be printed (don't ask about the numbers please).

## License

Copyright © 2024 Jeanne DEMOUSSEL.

This project is licensed under either of

- [Apache License, Version 2.0](https://www.apache.org/licenses/LICENSE-2.0) ([`LICENSE-APACHE`](LICENSE-APACHE))
- [MIT license](https://opensource.org/licenses/MIT) ([`LICENSE-MIT`](LICENSE-MIT))

at your option.
