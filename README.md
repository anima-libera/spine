# Spine

Compiled programming language in the making.
It compiles directlty to **ELF x86_64**.

Usage:
```sh
cargo run -- -f test.spine -o binary & ./binary
```

Can also provide raw source code in command line:
```sh
cargo run -- -r "\`printchar 97; \`printchar 10; \`exit" -o binary && ./binary
```
(woa what an amazing feature!!!¡¡)
