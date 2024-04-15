// top=cxx::top::add

#include <cassert>
#define TOP add

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

    assert(dut->output___05F == 15);

    assert(s.o->spade_repr() == "15");
    return 0;
})

MAIN
