`include "vatch/main.v"

module saturating_adder_tb();
    `SETUP_TEST

    initial begin
        $dumpfile(`VCD_OUTPUT);
        $dumpvars(0, saturating_adder_tb);
    end

    reg[7:0] a;
    reg[7:0] b;
    reg[7:0] max;
    wire[7:0] result;

    initial begin
        a <= 1;
        b <= 2;
        max <= 5;
        #1
        `ASSERT_EQ(result, 3);
        #10
        max <= 2;
        #1
        `ASSERT_EQ(result, 2);

        #10

        `END_TEST
    end

    \saturating_adder uut
        ( .a_i(a)
        , .b_i(b)
        , .max_i(max)
        , .output__(result)
        );
endmodule
