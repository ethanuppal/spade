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
    reg[15:0] in_val;
    wire[3:0] result;

    initial begin
        rst <= 1;
        @(negedge clk)
        @(negedge clk)
        rst <= 0;
        in_val <= {4'd1, 4'b0, 4'b0, 4'b0};

        @(negedge clk)
        in_val <= {4'd2, 4'b0, 4'b0, 4'b0};
        @(negedge clk)
        @(negedge clk)
        `ASSERT_EQ(result, 1);
        @(negedge clk)
        `ASSERT_EQ(result, 2);

        #20

        `END_TEST
    end

    e_delay_3 delay_3
        ( .clk_i(clk)
        , .input_i(in_val)
        , .output__(result)
        );
endmodule
