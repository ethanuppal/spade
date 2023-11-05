// top=cxx::top::large_output

#include <cassert>
#define TOP large_output

#include <verilator_util.hpp>

TEST_CASE(it_works, {
    s.i->a = "1";
    s.i->b = "2";
    s.i->c = "3";
    s.i->d = "2";

    ctx->timeInc(1);
    dut->eval();

    ctx->timeInc(1);
    dut->eval();

    assert(*s.o == "0x0000_0001_0000_0002_0000_0003_02");
    return 0;
})

MAIN
