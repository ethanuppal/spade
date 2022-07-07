`include "vatch/main.v"

module counter_tb();
    `SETUP_TEST

    reg clk;

    initial begin
        $dumpfile(`VCD_OUTPUT);
        $dumpvars(0, counter_tb);
        clk = 1;
        forever begin
            clk = ~clk;
            #1;
        end
    end


    reg[7:0] variant;
    wire[7:0] result;

    initial begin
        variant <= 0;
        #1
        `ASSERT_EQ(result, 0)
        variant <= 1;
        #1
        `ASSERT_EQ(result, 2)
        variant <= 2;
        #1
        `ASSERT_EQ(result, 3)

        #20

        `END_TEST
    end

    e_counter counter
        ( .test_case_i(variant)
        , .output__(result)
        );
endmodule
