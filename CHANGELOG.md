# Changelog

All notable changes to this project will be documented in this file.

Spade is currently unstable and all 0.x releases are expected to contain
breaking changes. Releases are mainly symbolic and are done on a six-week
release cycle. Every six weeks, the current master branch is tagged and
released as a new version.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added

- [!168][!168] Add an inverted port type `~T`. [Documentation][doc_inverted_ports]
- [!168][!168] Add `port` expression for creating a `(T, ~T)`. [Documentation][doc_inverted_ports]
- [!189][!189] Add `#[no_mangle]` attribute to unit parameters to avoid appending `_i` or `_o`
- [!191][!191] Add `translate_value` method to spade-python
- [!200][!200] Add more sophisticated and experimental wordlength inference logic that can be activated with the flag `--infer-method` or the environment variable `SPADE_INFER_METHOD`.

### Fixed

- [!178][!178] `sext` and `zext` now error when trying to reduce the width
- [!188][!188] Fix codegen bug when indexing structs or tuples which are 1 bit wide.

### Changed

### Removed

### Internal

- [!187][!187] Change naming scheme of Verilog variables to make names more predictable. [Documentation](https://docs.spade-lang.org/internal/naming.html)
- [!184][!184] The CI system now builds both Linux and macOS-AArch64.
- [!195][!195] Logos and Clap have had their respective versions bumped.

[!168]: https://gitlab.com/spade-lang/spade/-/merge_requests/168
[!178]: https://gitlab.com/spade-lang/spade/-/merge_requests/178
[!184]: https://gitlab.com/spade-lang/spade/-/merge_requests/184
[!187]: https://gitlab.com/spade-lang/spade/-/merge_requests/187
[!188]: https://gitlab.com/spade-lang/spade/-/merge_requests/188
[!189]: https://gitlab.com/spade-lang/spade/-/merge_requests/189
[!191]: https://gitlab.com/spade-lang/spade/-/merge_requests/191
[!195]: https://gitlab.com/spade-lang/spade/-/merge_requests/195

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

[Unreleased]: https://gitlab.com/spade-lang/spade/-/compare/v0.2.0...master
[0.2.0]: https://gitlab.com/spade-lang/spade/-/compare/v0.1.0...v0.2.0
[0.1.0]: https://gitlab.com/spade-lang/spade/-/tree/v0.1.0
