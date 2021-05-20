`include "vatch/main.v"

module pipeline_tb();
    `SETUP_TEST

    reg clk;

    initial begin
        $dumpfile(`VCD_OUTPUT);
        $dumpvars(0, pipeline_tb);
        clk = 1;
        forever begin
            clk = ~clk;
            #1;
        end
    end


    reg rst;
    reg[7:0] in_val;
    wire[7:0] result;

    initial begin
        rst <= 1;
        @(negedge clk)
        @(negedge clk)
        rst <= 0;
        in_val <= 1;

        @(negedge clk)
        in_val <= 0;
        @(negedge clk)
        `ASSERT_EQ(result, 1);
        @(negedge clk)
        `ASSERT_EQ(result, 0);

        #20

        `END_TEST
    end

    delay_3 delay_3
        ( ._i_clk(clk)
        , ._i_input1(in_val[7:4])
        , ._i_input2(in_val[3:0])
        , .__output(result)
        );
endmodule
