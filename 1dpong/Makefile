BUILD_DIR=build

IVERILOG_FLAGS=-g2012

SPADEC=../target/debug/spade

VCDS=$(wildcard test/*)

# Main rule
all: build/main.v.vcd .PHONY

# Build verilog from the spade code
build/main.v: src/main.spade $(SPADEC) | build_compiler
	@mkdir -p ${@D}
	@echo -e "[\033[0;34m${SPADEC}\033[0m] building $@"
	@${SPADEC} $< -o $@

# Build a test binary
build/main.v.out: build/main.v
	@echo -e "[\033[0;34miverilog\033[0m] building $@"
	@iverilog \
		-o ${@} \
		${IVERILOG_FLAGS} \
		-DVCD_OUTPUT=\"build/${<F}.vcd\" \
		$< src/testbench.v

# Simulate the test binary
build/main.v.vcd: build/main.v.out .PHONY
	@mkdir -p output
	@echo -e "[\033[0;34mvvp\033[0m] simulating $@"
	@vvp $< | grep -v dumpfile


build_compiler:
	cd .. && cargo build



clean:
	rm -rf build/


.SECONDARY: $(patsubst %, build/main.v, ${TEST_DIRS})
.PHONY:

# Builds an iverlog command file with all build options that can be passed to linters
iverilog_commandfile: build_hs
	@echo -e $(patsubst %, '-l %\n', ${non_test_verilogs}) > .verilog_config
