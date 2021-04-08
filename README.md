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

Spade is in its early stages, so everything is subject to change. For now,
there are a few larger examples of what the language looks like in the `1dpong`
and `gaming` directories.


## Getting started
1. Clone the repo `git clone git@gitlab.com:TheZoq2/spade.git`
2. Initalize the submodules `git submodules init && git submodules update`
3. Build the project `cargo build`
4. Build your spade code using `cargo run -- <input.spade> -o output.v`

If you are interested in contributing to spade, the
[ARCHITECTURE.md](ARCHITECTURE.md) document is a good place to start. It gives
an overview of the inner workings of the compiler.

## Editor integration

There is a vim plugin for syntax highlighting and auto indentation at
https://gitlab.com/TheZoq2/spade-vim

## Planned features

- [x] Type inference
- [x] Strongly typed
- [x] Compile time checked pipelines
    - [x] Basic pipeline definitions
    - [ ] Pipeline instantiation
    - [ ] Type Dependent lengths
- [ ] Traits and generics
- [ ] Structs
- [ ] Sum types and pattern matching
- [ ] ...

## License

Spade is licensed under the [EUPL-1.2 license](LICENSE.txt).
