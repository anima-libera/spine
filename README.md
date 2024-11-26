# Spine

Compiled programming language in the making.
It compiles directlty to **ELF x86_64**.

Usage:
```sh
cargo run -- -f test.spine -o binary & ./binary
```

Can also provide raw source code in command line:
```sh
cargo run -- -r "\`printstr \"haiii :3\\n\"; \`exit" && ./b
```
(woa what an amazing feature!!!¡¡)

(default output binary path is "b" when not provided via `-o`)

## VSCode extension

The extension is developped in `vscode-extension/spine-lang`.

It is packaged in `vscode-extension/spine-lang/spine-lang-0.0.1.vsix`.

It can be installed by going to `Extensions > ··· > Install from VSIX...`
or by running
```sh
code --install-extension vscode-extension/spine-lang/spine-lang-0.0.1.vsix
```
