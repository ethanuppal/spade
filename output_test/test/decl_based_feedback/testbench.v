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
    wire[7:0] x;
    wire[7:0] y;

    initial begin
        rst <= 1;
        @(negedge clk)
        rst <= 0;

        `ASSERT_EQ(x, 0);
        `ASSERT_EQ(y, 0);

        repeat(8) @(negedge clk);
        `ASSERT_EQ(x, 8);
        `ASSERT_EQ(y, 0);

        repeat(6) @(negedge clk);
        `ASSERT_EQ(x, 8);
        `ASSERT_EQ(y, 6);

        @(negedge clk);

        `ASSERT_EQ(x, 0);
        `ASSERT_EQ(y, 0);

        #20

        `END_TEST
    end

    e_counter counter
        ( .clk_i(clk)
        , .rst_i(rst)
        , .output__({x, y})
        );
endmodule
