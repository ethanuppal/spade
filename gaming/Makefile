$(shell cd .. && cargo build)
BUILD_DIR=build

IVERILOG_FLAGS=-g2012

SPADEC=../target/debug/spade

VCDS=$(wildcard test/*)

# Main rule
all: ecp5.svf

# Build verilog from the spade code
build/main.v: src/main.spade $(SPADEC)
	@mkdir -p ${@D}
	@echo -e "[\033[0;34m${SPADEC}\033[0m] building $@"
	@${SPADEC} $< -o $@

upload: ecp5.svf .PHONY
	openocd -f openocd-ecpix5.cfg -c "init" -c "svf -quiet ecp5.svf" -c "exit"

# ECPIX5 stuff
IDCODE ?= 0x81112043 # 12f

ecp5.json: top_ecp5.v build/main.v ecpix5.lpf
	yosys \
		-p "synth_ecp5 -json $@" \
		-E .$(basename $@).d \
		top_ecp5.v build/main.v

ecp5.config: ecp5.json ecpix5.lpf
	nextpnr-ecp5 \
		--json $< \
		--textcfg $@ \
		--lpf ecpix5.lpf \
		--um5g-45k \
		--package CABGA554

ecp5.bit: ecp5.config
	ecppack --idcode $(IDCODE) $< $@

ecp5.svf: ecp5.config
	ecppack --idcode $(IDCODE) --input $< --svf $@

clean:
	rm -rf build/


.SECONDARY: $(patsubst %, build/main.v, ${TEST_DIRS})
.PHONY: build/main.v.vcd build_compiler all

# Builds an iverlog command file with all build options that can be passed to linters
iverilog_commandfile: build_hs
	@echo -e $(patsubst %, '-l %\n', ${non_test_verilogs}) > .verilog_config
