# Changelog

All notable changes to this project will be documented in this file.

Spade is currently unstable and all 0.x releases are expected to contain
breaking changes. Releases are mainly symbolic and are done on a six-week
release cycle. Every six weeks, the current master branch is tagged and
released as a new version.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).
## Unreleased

### Added

[!251][!251] Allow instantiating single variant enums without `()`

### Fixed

### Changed

### Removed

[!251]: https://gitlab.com/spade-lang/spade/-/merge_requests/251

## [0.5.0]

### Added

- [!232][!232] Support for implementing traits
- Started adding a language reference documentation section where all language
  features will be described.
  <https://docs.spade-lang.org/language_reference/index.html>

### Fixed

- [!224][!224] `stage.valid` now does what it is supposed to
- [!235][!235] Workaround for vivado not supporting escaped identifiers called `new`
- [!239][!239] Codegen: Don't generate a source reference attribute for non-existent void values
- [!241][!241] Fix panic on zero-sized-type in pipeline

### Changed

- [!224][!224] Name de-aliasing now only de-aliases anonymous names
- [!232][!232] **Breaking change** Bump minimum rust version to 1.70


[!232]: https://gitlab.com/spade-lang/spade/-/merge_requests/232
[!224]: https://gitlab.com/spade-lang/spade/-/merge_requests/224
[!235]: https://gitlab.com/spade-lang/spade/-/merge_requests/235
[!239]: https://gitlab.com/spade-lang/spade/-/merge_requests/239
[!241]: https://gitlab.com/spade-lang/spade/-/merge_requests/241

## [0.4.0]

### Added

- [!216][!216] Support initial values for registers
- [!217][!217] Allow writing units that don't return a value.

### Fixed

- [!202][!202] Re-add missing requirement for the first argument of a pipeline to be a clock
- [!205][!205] Fix panic on method calls in let bindings
- [!206][!206] Re-add working VCD translation. It now also translates more values
- [!215][!215] Make generated code compile out of the box with verilator
- [!221][!221] Fix code generation bug when matching two variant enums

### Changed

- [!207][!207] Rename `wal_suffix` attribute to `wal_traceable`. It now defaults to the struct name as a suffix, but can override that using the `suffix` parameter to the attribute.
- [!208][!208] Add a new `#[wal_suffix]` attribute which emits a copy of the marked signal with a specific suffix. Can also be applied to units to add `#[wal_suffix]` to all inputs.
- [!214][!214] Improve the error messages for positional arguments

### Removed

- [!206][!206] Remove type dump file. This information was redundant and can be recovered from `CompilerState` instead


[Associated Swim release](https://gitlab.com/spade-lang/swim/-/tree/v0.4.0)

[!202]: https://gitlab.com/spade-lang/spade/-/merge_requests/202
[!205]: https://gitlab.com/spade-lang/spade/-/merge_requests/205
[!206]: https://gitlab.com/spade-lang/spade/-/merge_requests/206
[!207]: https://gitlab.com/spade-lang/spade/-/merge_requests/207
[!209]: https://gitlab.com/spade-lang/spade/-/merge_requests/209
[!214]: https://gitlab.com/spade-lang/spade/-/merge_requests/214
[!215]: https://gitlab.com/spade-lang/spade/-/merge_requests/215
[!216]: https://gitlab.com/spade-lang/spade/-/merge_requests/216
[!217]: https://gitlab.com/spade-lang/spade/-/merge_requests/217
[!211]: https://gitlab.com/spade-lang/spade/-/merge_requests/211
[!235]: https://gitlab.com/spade-lang/spade/-/merge_requests/235

## [0.3.0]

### Added

- [!168][!168] Add an inverted port type `~T`. [Documentation][doc_inverted_ports]
- [!168][!168] Add `port` expression for creating a `(T, ~T)`. [Documentation][doc_inverted_ports]
- [!189][!189] Add `#[no_mangle]` attribute to unit parameters to avoid appending `_i` or `_o`
- [!191][!191] Add `translate_value` method to spade-python
- [!200][!200] Add more sophisticated and experimental wordlength inference logic that can be activated with the flag `--infer-method` or the environment variable `SPADE_INFER_METHOD`.
- [!167][!167] Add support for ready and valid signaling in the pipelines. [Documentation](https://docs.spade-lang.org/language_reference/dynamic_pipelines.html)

### Fixed

- [!178][!178] `sext` and `zext` now error when trying to reduce the width
- [!188][!188] Fix codegen bug when indexing structs or tuples which are 1 bit wide.
- [!201][!201] Stop producing `spade.sv` when monomorphisation fails

### Internal

- [!187][!187] Change naming scheme of Verilog variables to make names more predictable. [Documentation](https://docs.spade-lang.org/internal/naming.html)
- [!184][!184] The CI system now builds both Linux and macOS-AArch64.
- [!195][!195] Logos and Clap have had their respective versions bumped.

[!167]: https://gitlab.com/spade-lang/spade/-/merge_requests/167
[!168]: https://gitlab.com/spade-lang/spade/-/merge_requests/168
[!178]: https://gitlab.com/spade-lang/spade/-/merge_requests/178
[!184]: https://gitlab.com/spade-lang/spade/-/merge_requests/184
[!187]: https://gitlab.com/spade-lang/spade/-/merge_requests/187
[!188]: https://gitlab.com/spade-lang/spade/-/merge_requests/188
[!189]: https://gitlab.com/spade-lang/spade/-/merge_requests/189
[!191]: https://gitlab.com/spade-lang/spade/-/merge_requests/191
[!195]: https://gitlab.com/spade-lang/spade/-/merge_requests/195
[!200]: https://gitlab.com/spade-lang/spade/-/merge_requests/200
[!201]: https://gitlab.com/spade-lang/spade/-/merge_requests/201

[doc_inverted_ports]: https://docs.spade-lang.org/language_reference/type_system/inverted_ports.html

## [0.2.0] - 2023-04-20

### Added

- [!155][!155] Support for specifying initial content of memories.
- [!154][!154] Add unsigned literals, for example `let x: int<8> 255u` as a
  stop gap solution until proper unsigned types are implemented
- [!169][!169] Add `!=` operator
- [!185][!185] `max`, `min`, and `order` operation added to `std::ops`

### Fixed

- [!156][!156] Report an internal error when inferring negative widths instead of panicking

### Changed

- [!165][!165] Standard library is now included by the compiler instead of Swim.

### Internal

- [!154](!154) Rewrote compiler to use arbitrary width integers internally.

[!154]: https://gitlab.com/spade-lang/spade/-/merge_requests/154
[!155]: https://gitlab.com/spade-lang/spade/-/merge_requests/155
[!156]: https://gitlab.com/spade-lang/spade/-/merge_requests/156
[!165]: https://gitlab.com/spade-lang/spade/-/merge_requests/165
[!169]: https://gitlab.com/spade-lang/spade/-/merge_requests/169
[!185]: https://gitlab.com/spade-lang/spade/-/merge_requests/185


## [0.1.0] - 2023-03-07

Initial numbered version

[Associated Swim release](https://gitlab.com/spade-lang/swim/-/tree/v0.1.0)

[Unreleased]: https://gitlab.com/spade-lang/spade/-/compare/v0.5.0...master
[0.5.0]: https://gitlab.com/spade-lang/spade/-/compare/v0.4.0...v0.5.0
[0.4.0]: https://gitlab.com/spade-lang/spade/-/compare/v0.3.0...v0.4.0
[0.3.0]: https://gitlab.com/spade-lang/spade/-/compare/v0.2.0...v0.3.0
[0.2.0]: https://gitlab.com/spade-lang/spade/-/compare/v0.1.0...v0.2.0
[0.1.0]: https://gitlab.com/spade-lang/spade/-/tree/v0.1.0
