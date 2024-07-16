# top=array_eval::constant_array

from spade import SpadeExt

import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test(dut):
    s = SpadeExt(dut)
    await Timer(1, units='ns')
    s.o.assert_eq("ArrayInStruct([1,2,3,4,5,6,7,8], 9)")

