# top=array_eval::array_in_array_in_array_with_shorthand

from spade import SpadeExt

import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)
    await Timer(1, units='ns')
    s.o.assert_eq("[[[1, 1], [1, 1]], [[1, 1], [1, 1]]]")
