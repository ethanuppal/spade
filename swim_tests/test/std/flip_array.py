#top = flip_array::bitreverse

from spade import SpadeExt
from cocotb import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)
    s.i.a = "[true, true, false, false, true, false, true, false]"
    await Timer(1, units='ns')
    s.o.assert_eq(f"[false, true, false, true, false, false, true, true]")

