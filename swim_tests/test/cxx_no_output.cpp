// top=cxx::top::no_output

#include <cassert>
#define TOP no_output

#include <verilator_util.hpp>

TEST_CASE(it_works, {
    dut->eval();
    ctx->timeInc(1);
    dut->eval();

    s.i->a = "5";
    s.i->b = "10";

    ctx->timeInc(1);
    dut->eval();

    ctx->timeInc(1);
    dut->eval();

    return 0;
})

MAIN
