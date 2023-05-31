#top = pipeline_ready_valid::ready_valid_pipeline

from cocotb.triggers import FallingEdge, NextTimeStep
from spade import SpadeExt
from cocotb import cocotb
from cocotb.clock import Clock

@cocotb.test()
async def enabled_stages_behave_normally(dut):
    clk = dut.clk_i

    s = SpadeExt(dut)

    await cocotb.start(Clock(clk, 1, units="ns").start())

    s.i.enables = "&[true, true, true, true]"

    async def driver():
        # We need to wait one cycle before starting, because of the enables
        for i in range(0, 6):
            await FallingEdge(clk)
            s.i.val = f"{i}"

    async def checker():
        [await FallingEdge(clk) for _ in range(0, 4)]
        for i in range(0, 6):
            await FallingEdge(clk)
            s.o.val.assert_eq(f"{i}")

    task1 = cocotb.start_soon(driver())
    task2 = cocotb.start_soon(checker())

    await task1
    await task2

@cocotb.test()
async def disabled_stages_result_in_deasserted_valid(dut):
    clk = dut.clk_i

    s = SpadeExt(dut)

    await cocotb.start(Clock(clk, 1, units="ns").start())

    s.i.enables = "&[true, true, true, true]"
    # Let the enables propagate through the pipeline until the enabled
    # values have propagated
    [await FallingEdge(clk) for _ in range(0, 4)]

    s.i.enables = "&[false, true, true, true]"
    await NextTimeStep()
    # Valid is not combinatorial
    s.o.s0_valid.assert_eq("true");
    s.o.s1_valid.assert_eq("true");
    s.o.s2_valid.assert_eq("true");
    s.o.s3_valid.assert_eq("true");
    s.o.s4_valid.assert_eq("true");

    await FallingEdge(clk)
    s.o.s0_valid.assert_eq("true");
    s.o.s1_valid.assert_eq("false");
    s.o.s2_valid.assert_eq("true");
    s.o.s3_valid.assert_eq("true");
    s.o.s4_valid.assert_eq("true");

    # re-enable the stages so we have a single invalid value being propagated
    s.i.enables = "&[true, true, true, true]"

    s.o.s0_valid.assert_eq("true");
    s.o.s1_valid.assert_eq("false");
    s.o.s2_valid.assert_eq("true");
    s.o.s3_valid.assert_eq("true");
    s.o.s4_valid.assert_eq("true");
    await FallingEdge(clk)

    s.o.s0_valid.assert_eq("true");
    s.o.s1_valid.assert_eq("true");
    s.o.s2_valid.assert_eq("false");
    s.o.s3_valid.assert_eq("true");
    s.o.s4_valid.assert_eq("true");
    await FallingEdge(clk)

    s.o.s0_valid.assert_eq("true");
    s.o.s1_valid.assert_eq("true");
    s.o.s2_valid.assert_eq("true");
    s.o.s3_valid.assert_eq("false");
    s.o.s4_valid.assert_eq("true");
    await FallingEdge(clk)


@cocotb.test()
async def downstream_disables_disable_upstream(dut):
    clk = dut.clk_i

    s = SpadeExt(dut)

    await cocotb.start(Clock(clk, 1, units="ns").start())

    s.i.enables = "&[true, true, true, true]"
    # Let the enables propagate through the pipeline until the enabled
    # values have propagated
    [await FallingEdge(clk) for _ in range(0, 4)]

    s.i.enables = "&[true, true, true, true]"
    await FallingEdge(clk)
    s.o.s0_ready.assert_eq("true");
    s.o.s1_ready.assert_eq("true");
    s.o.s2_ready.assert_eq("true");
    s.o.s3_ready.assert_eq("true");
    s.o.s4_ready.assert_eq("true");


    s.i.enables = "&[true, true, true, false]"
    await FallingEdge(clk)
    s.o.s0_ready.assert_eq("false");
    s.o.s1_ready.assert_eq("false");
    s.o.s2_ready.assert_eq("false");
    s.o.s3_ready.assert_eq("false");
    s.o.s4_ready.assert_eq("true");


    s.i.enables = "&[true, true, false, true]"
    await FallingEdge(clk)
    s.o.s0_ready.assert_eq("false");
    s.o.s1_ready.assert_eq("false");
    s.o.s2_ready.assert_eq("false");
    s.o.s3_ready.assert_eq("true");
    s.o.s4_ready.assert_eq("true");


    s.i.enables = "&[true, false, true, true]"
    await FallingEdge(clk)
    s.o.s0_ready.assert_eq("false");
    s.o.s1_ready.assert_eq("false");
    s.o.s2_ready.assert_eq("true");
    s.o.s3_ready.assert_eq("true");
    s.o.s4_ready.assert_eq("true");


    s.i.enables = "&[false, true, true, true]"
    await FallingEdge(clk)
    s.o.s0_ready.assert_eq("false");
    s.o.s1_ready.assert_eq("true");
    s.o.s2_ready.assert_eq("true");
    s.o.s3_ready.assert_eq("true");
    s.o.s4_ready.assert_eq("true");


    s.i.enables = "&[false, true, true, false]"
    await FallingEdge(clk)
    s.o.s0_ready.assert_eq("false");
    s.o.s1_ready.assert_eq("false");
    s.o.s2_ready.assert_eq("false");
    s.o.s3_ready.assert_eq("false");
    s.o.s4_ready.assert_eq("true");

