// top = cxx::top::comparison_test

#include <cassert>
#define TOP comparison_test

#include <verilator_util.hpp>

#include <iostream>


TEST_CASE(it_works, {
    s.i->in = "Some(1)";
    dut->eval();
    ASSERT_EQ(s.o, "Some(1)")

    s.i->in = "Some(2)";
    dut->eval();
    ASSERT_EQ(s.o, "Some(2)")

    s.i->in = "None()";
    dut->eval();
    ASSERT_EQ(s.o, "None()")

    assert(!(*s.o == "Some(0)"));

    return 0;
})

MAIN
