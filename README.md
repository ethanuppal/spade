<img src="misc/spadefish.svg" />

# Spade

A work in progress HDL that doesn't make you want to pull your hair out. Taking
inspiration from rust and clash, the goal is to make a safer more expressive
language than Verilog and VHDL but without sacrificing the ability for low
level control of the hardware.

## Code examples

```
entity counter(clk: clk, rst: bool, max: int<8>) -> int<8> {
    reg(clk) value reset (rst: 0) =
        if value == max {
            0
        }
        else {
            value + 1
        };
    value
}
```

Spade is in its early stages, so everything is subject to change. For a taste of
what the language looks like, here are some projects using most of the features

- Work in progress Risc-V CPU: https://gitlab.com/TheZoq2/spade-v
- An executor for dynamic programming: https://gitlab.com/TheZoq2/dp-executor

## Getting started

The recommended way to use spade is with its build tool
[swim](https://gitlab.com/spade-lang/swim/), but for just playing around with
the language you can use the compiler directly.

1. Install rust via your package manager or https://rustup.rs/
2. Clone the repo `git clone --recursive https://gitlab.com/spade-lang/spade.git`
3. Build your spade code using `cargo run --bin spade -- <input.spade> -o output.v`

You can also install the compiler using `cargo install spade --git
https://gitlab.com/spade-lang/spade`.
That will install a `spade` binary to your [cargo
home](https://doc.rust-lang.org/book/ch14-04-installing-binaries.html).

If you are interested in contributing to spade, the
[ARCHITECTURE.md](ARCHITECTURE.md) document is a good place to start. It gives
an overview of the inner workings of the compiler.

## Editor integration

There are editor plugins for syntax highlighting available for some editors

 - vim: https://gitlab.com/spade-lang/spade-vim
 - vscode: https://git.ablecorp.us/elfein/spade_highlighting/
 - emacs: https://github.com/Emiluren/.emacs.d/blob/master/lisp/spade-mode/spade-mode.el

Note that most of these are maintained by third parties and may be out of date. If you make a plugin
for your favourite editor, feel free to add it to the list!

## Features

- Type inference
- Strongly typed
    - Sum types and pattern matching
    - Structs and tuples
- Combinatorial logic by default, registers as an explicit structure
- Compile time checked pipelines
    - Basic pipeline definitions
    - Pipeline instantiation

## Development and Community

If you are interested in using or contributing to Spade, feel free to join our
[discord group](https://discord.gg/YtXbeamxEX).

Spade is currently being developed as an Open Source project at the Department
of Electrical Engineering at Linköping university.

## License

The spade compiler is licensed under the [EUPL-1.2 license](LICENSE-EUPL-1.2.txt).

The spade standard library (all files located in the stdlib directory) is licensed under
the terms of both the [MIT license](MIT License) and the [Apache
License](LICENSE-APACHE2.0.txt).
