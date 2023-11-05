// top=cxx::top::large_input

#include <cassert>
#define TOP large_input

#include <verilator_util.hpp>

TEST_CASE(it_works, {
    dut->eval();
    ctx->timeInc(1);
    dut->eval();

    s.i->a = "0x1_0000_0002_0000_0003u";

    ctx->timeInc(1);
    dut->eval();

    ctx->timeInc(1);
    dut->eval();

    ASSERT_EQ(s.o, "0x1_0000_0002_0000_0003u");
    return 0;
})

MAIN
