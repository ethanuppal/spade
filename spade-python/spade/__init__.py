from .spade import *

import cocotb
import colors
from cocotb.types import LogicArray
from cocotb.handle import Force
import cocotb.triggers as triggers
from spade import Spade

# TODO: Consider adding a prelude so we don't import this
import os


class SpadeExt(Spade):
    def __new__(cls, dut):
        compiler_state = os.environ["SWIM_SPADE_STATE"]
        uut_name = os.environ["SWIM_UUT"]

        try:
            result = super().__new__(cls, uut_name, compiler_state)
        except FileNotFoundError as e:
            print(f"{compiler_state}")
            print("Failed to find", e.filename, " ", e.filename2)
            raise e


        result.dut = dut
        result.i = InputPorts(dut, result)
        return result

    def o(self):
        return OutputValue(self, self.output_value(self.dut.output__.value.binstr))

    # def assert_port(self, port, expected):
    #     # Evaluate the expected value
    #     expected_bits = self.value_as_output_type(expected)
    #     if port.value.binstr.lower() != expected_bits.lower():
    #         spade_value = self.translate_output_value(port.value.binstr)

    #         message = "\n"
    #         message += colors.red("Assertion failed") + "\n"
    #         message += f"\t expected: {colors.green(expected)}\n";
    #         message += f"\t      got: {colors.red(spade_value)}\n"
    #         message += "\n"
    #         message += f"\tverilog ({colors.green(expected_bits)} != {colors.red(port.value)})"
    #         assert False, message


class InputPorts(object):
    def __init__(self, dut, spade: SpadeExt):
        self.spade__ = spade
        self.dut__ = dut

    def __setattr__(self, name: str, value: str):
        if not name.endswith("__"):
            # Ask the spade compiler if the DUT has this field
            (port, val) = self.spade__.port_value(name, value)

            self.dut__._id(port, extended=False).value = LogicArray(val.inner())
        else:
            super(InputPorts, self).__setattr__(name, value)


class OutputValue(object):
    def __init__(self, spade: SpadeExt, value: TypedValue):
        self.spade__ = spade
        self.val__ = value

    def assert_eq(self, expected: str):
        c = self.spade__.compare_values(self.val__, expected)

        if c.expected_bits.inner().lower() != c.got_bits.inner().lower():
            message = "\n"
            message += colors.red("Assertion failed") + "\n"
            message += f"\t expected: {colors.green(c.expected_spade)}\n";
            message += f"\t      got: {colors.red(c.got_spade)}\n"
            message += "\n"
            message += f"\tverilog ({colors.green(c.expected_bits.inner())} != {colors.red(c.got_bits.inner())})"
            assert False, message

    def __getattribute__(self, __name: str):
        if not __name.endswith("__") and __name != "assert_eq":
            pass
        else:
            return super(OutputValue, self).__getattribute__(__name)
