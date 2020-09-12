FILES_WITH_ERRORS=$(wildcard testcode/invalid/*)

all_invalid: $(patsubst %, %_built, $(FILES_WITH_ERRORS)) .PHONY

testcode/invalid/%.sp_built: testcode/invalid/%.sp cargo_build
	target/debug/spade $< || true

cargo_build:
	cargo build

.PHONY:


