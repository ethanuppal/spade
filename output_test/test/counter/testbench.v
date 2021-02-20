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


    reg rst;
    reg[7:0] max;
    wire[7:0] result;

    initial begin
        max <= 2;

        rst <= 1;
        @(negedge clk)
        @(negedge clk)
        rst <= 0;

        `ASSERT_EQ(result, 0)
        @(negedge clk)
        `ASSERT_EQ(result, 1)
        @(negedge clk)
        `ASSERT_EQ(result, 2)
        @(negedge clk)
        `ASSERT_EQ(result, 0)

        #20

        `END_TEST
    end

    counter counter
        ( ._i_clk(clk)
        , ._i_rst(rst)
        , ._i_max(max)
        , .__output(result)
        );
endmodule
