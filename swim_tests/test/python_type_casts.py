#top = python_api::type_casts

from spade import SpadeExt
import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def input_casts(dut):
    s = SpadeExt(dut)

    s.i.b = True
    s.i.i = 10
    s.i.array = [1,2,3,4,5,6,7,8]
    await Timer(10, units = "ns")
    s.o.b.assert_eq('true')
    s.o.i.assert_eq("10")
    s.o.array.assert_eq("[1, 2, 3, 4, 5, 6, 7, 8]")

@cocotb.test()
async def output_casts(dut):
    s = SpadeExt(dut)

    s.i.b = "true"
    s.i.i = "10"
    s.i.array = "[1,2,3,4,5,6,7,8]"
    await Timer(10, units = "ns")
    s.o.b.assert_eq(True)
    s.o.i.assert_eq(10)
    s.o.array.assert_eq([1, 2, 3, 4, 5, 6, 7, 8])


