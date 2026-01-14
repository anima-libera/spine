## Errors and warnings
- warning for block comment missing closing curly (to be actually displayed when comments are not ignored)
- type checking errors

## Feature improvements
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
- quickfix suggestion for string literal containing unescaped newlines warning
- in case of mismatched curly errors, try to find a fix (try all positions and look at errors)

## Language server new features
- build and run the code from the IDE
- semantic tokens
- display tokens (like rust-analyzer allows to do)
- display AST (like rust-analyzer allows to do)
- fix errors being displayed twice on hover
- use `TextDocumentSyncKind::INCREMENTAL` instead of `TextDocumentSyncKind::FULL`
- display same documentation when hovering a keyword than when looking at it as a completion item
- command and button to restart the language server

## CLI new features
- pass arguments to the binary when using `--run`
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
- local variables, typed, declared, set and get, stackframes (on the call stack)
- move semantics for variables (move by default)
- conditionals, loops, CFG in action
- generics
- standard library of syscalls
- documentation comments attached to symbols get displayed on symbol hover by language server

## Formatter features
- make the high level ast contain all the info about the source code to be able to generate the same
- make the identity formatter
- trivial formatters that only modify whitespace

## Internal refactorings
- encapsulate lsp crate pos and range types to force the use of proper conversions to our types
- move completion stuff out of the lsp method, and factorize stuff
- move x86_64 specific stuff to its own module
- have an actual type that represents exactly one x86_64 instr (no label, no xor+mov)
