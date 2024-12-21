## Errors
- character/string literals related:
  - invalid escape: `\x`/`\u`/`\d` with a number that is not a unicode scalar value
- block comment missing closing curly
- block statement missing closing curly
- closing curly without a matching opening curly

## Feature improvements
- nested blocks in block comments
- integer literals with a negative sign
- more information on hovering integer/character/string literals, such as:
  - the list of character escapes and their meaning
  - is valid ASCII or not
  - length in bytes of the utf-8 representation
  - length in characters
  - address in runtime memory
  - binary representation
  - decimal representation
  - hexadecimal representation
  - radix prefix meaning and the range of valid digits authorized by it

## Language server new features
- run the code from IDE
- semantic tokens
- display tokens (like rust-analyzer allows to do)
- display AST (like rust-analyzer allows to do)

## CLI new features
- run the binary after compilation, if compilation succeeded; pass arguments to the binary
- print the errors and warnings, but do not compile
- print tokens
- print AST
- print quasi machine code
- print machine code annotated with asm-like form
- print machine code

## Language new features
- tree of scopes, local stuff can refer to anything (type, function, variable, etc.) in the outer scopes
- named blocks, can break out of a block designated by its name, CFG
- define constants
- separate data stack and call stack, function definition, typed signature (in -- out), call, return
- actual types, type names, layouts, explicit casts, proper type mismatch errors, type definitions
- local variables, typed, declared, set and get, stackframes
- conditionals, loops, CFG in action
- generics
- standard library of syscalls
- documentation comments attached to symbols get displayed on symbol hover by language server
