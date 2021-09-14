SHELL=/bin/sh -o pipefail
$(shell cd .. && cargo build)
BUILD_DIR=build

IVERILOG_FLAGS=-g2012

SPADEC=../target/debug/spade

TEST_DIRS=$(wildcard test/*)

# Main rule
all: ${TEST_DIRS} .PHONY

test/saturating_adder: test/saturating_adder/build/code.v.vcd .PHONY
test/counter: test/counter/build/code.v.vcd .PHONY
test/multi_entity: test/multi_entity/build/code.v.vcd .PHONY
test/basic_pipeline: test/basic_pipeline/build/code.v.vcd .PHONY
test/tuple_pipeline: test/tuple_pipeline/build/code.v.vcd .PHONY
test/enum_instantiation: test/enum_instantiation/build/code.v.vcd .PHONY
test/match: test/match/build/code.v.vcd .PHONY

# Build verilog from the spade code
test/%/build/code.v: test/%/code.spade $(SPADEC)
	@mkdir -p ${@D}
	@echo -e "[\033[0;34m${SPADEC}\033[0m] building $@"
	@${SPADEC} $< -o $@

# Build a test binary
test/%/build/code.v.out: test/%/build/code.v
	@echo -e "[\033[0;34miverilog\033[0m] building $@"
	@iverilog \
		-o ${@} \
		${IVERILOG_FLAGS} \
		-DVCD_OUTPUT=\"test/$*/build/${<F}.vcd\" \
		$< ${@D}/../testbench.v

# Simulate the test binary
test/%/build/code.v.vcd: test/%/build/code.v.out .PHONY
	@mkdir -p output
	@echo -e "[\033[0;34mvvp\033[0m] simulating $@"
	@vvp $< | grep -v dumpfile


build_compiler:
	cd .. && cargo build



clean:
	rm -rf $(patsubst %, %/build, ${TEST_DIRS})


.SECONDARY: $(patsubst %, %/build/code.v, ${TEST_DIRS})
.PHONY:

# Builds an iverlog command file with all build options that can be passed to linters
iverilog_commandfile: build_hs
	@echo -e $(patsubst %, '-l %\n', ${non_test_verilogs}) > .verilog_config
