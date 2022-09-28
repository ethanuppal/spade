from .spade import *

import cocotb
import colors
from cocotb.types import LogicArray
from cocotb.handle import Force
from cocotb.triggers import *
from spade import Spade

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
        result.o = result.o__()
        return result

    def o__(self):
        """ Get a reference to the output of the DUT"""
        return OutputField(self, [], self.output_as_field_ref(), self.dut)


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


class OutputField(object):
    def __init__(self, spade: SpadeExt, path: list[str], field_ref, dut):
        self.spade__ = spade
        self.path__ = path
        self.field_ref__ = field_ref
        self.dut__ = dut

    def assert_eq(self, expected: str):
        # This shares a bit of code with is_eq, but since we need access to intermediate
        # values, we'll duplicate things for now
        r = self.spade__.compare_field(
            self.field_ref__,
            expected,
            BitString(self.dut__.output__.value.binstr)
        )

        expected_bits = r.expected_bits.inner();
        got_bits = r.got_bits.inner();

        if expected_bits.lower() != got_bits.lower():
            message = "\n"
            message += colors.red("Assertion failed") + "\n"
            message += f"\t expected: {colors.green(r.expected_spade)}\n";
            message += f"\t      got: {colors.red(r.got_spade)}\n"
            message += "\n"
            message += f"\tverilog ('{colors.green(expected_bits)}' != '{colors.red(got_bits)}')"
            assert False, message

    def value(self):
        """
            Returns the value of the field as a string representation of the spade value.
        """
        # This shares a bit of code with is_eq, but since we need access to intermediate
        # values, we'll duplicate things for now
        return self.spade__.field_value(
            self.field_ref__,
            BitString(self.dut__.output__.value.binstr)
        )

    def is_eq(self, other: str) -> bool:
        r = self.spade__.compare_field(
            self.field_ref__,
            other,
            BitString(self.dut__.output__.value.binstr)
        )
        expected_bits = r.expected_bits.inner();
        got_bits = r.got_bits.inner();
        return expected_bits.lower() == got_bits.lower()


    def __getattribute__(self, __name: str):
        if __name.endswith("__") or __name == "assert_eq" or __name == "is_eq" or __name == "value":
            return super(OutputField, self).__getattribute__(__name)
        else:
            new_path = self.path__ + [__name]
            return OutputField(
                self.spade__,
                new_path,
                self.spade__.output_field(new_path),
                self.dut__
            )

