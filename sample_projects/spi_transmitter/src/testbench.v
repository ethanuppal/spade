`include "../../output_test/vatch/main.v"

module counter_tb();
    reg clk;

    `SETUP_TEST

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
    reg sclk;
    reg mosi;
    reg[7:0] result;

    initial begin
        mosi <= 1;
        sclk <= 1;
        rst <= 1;
        #10
        rst <= 0;

        @(negedge clk)

        // bit 1
        sclk <= 0;
        @(negedge clk)
        @(negedge clk)
        mosi <= 0;
        sclk <= 1;
        @(negedge clk)
        @(negedge clk)

        // bit 2
        sclk <= 0;
        @(negedge clk)
        @(negedge clk)
        mosi <= 0;
        sclk <= 1;
        @(negedge clk)
        @(negedge clk)

        // bit 3
        sclk <= 0;
        @(negedge clk)
        @(negedge clk)
        mosi <= 1;
        sclk <= 1;
        @(negedge clk)
        @(negedge clk)

        // bit 4
        sclk <= 0;
        @(negedge clk)
        @(negedge clk)
        mosi <= 1;
        sclk <= 1;
        @(negedge clk)
        @(negedge clk)

        // bit 5
        sclk <= 0;
        @(negedge clk)
        @(negedge clk)
        mosi <= 1;
        sclk <= 1;
        @(negedge clk)
        @(negedge clk)

        // bit 6
        sclk <= 0;
        @(negedge clk)
        @(negedge clk)
        mosi <= 1;
        sclk <= 1;
        @(negedge clk)
        @(negedge clk)

        // bit 7
        sclk <= 0;
        @(negedge clk)
        @(negedge clk)
        mosi <= 1;
        sclk <= 1;
        @(negedge clk)
        @(negedge clk)

        // bit 8
        sclk <= 0;
        @(negedge clk)
        @(negedge clk)
        mosi <= 1;
        sclk <= 1;
        @(negedge clk)
        @(negedge clk)

        `ASSERT_EQ(result, 8'b10011111);

        @(negedge clk)
        // bit 1
        sclk <= 0;
        @(negedge clk)
        @(negedge clk)
        mosi <= 0;
        sclk <= 1;
        @(negedge clk)
        @(negedge clk)

        // bit 2
        sclk <= 0;
        @(negedge clk)
        @(negedge clk)
        mosi <= 0;
        sclk <= 1;
        @(negedge clk)
        @(negedge clk)

        // bit 3
        sclk <= 0;
        @(negedge clk)
        @(negedge clk)
        mosi <= 1;
        sclk <= 1;
        @(negedge clk)
        @(negedge clk)

        // bit 4
        sclk <= 0;
        @(negedge clk)
        @(negedge clk)
        mosi <= 1;
        sclk <= 1;
        @(negedge clk)
        @(negedge clk)

        // bit 5
        sclk <= 0;
        @(negedge clk)
        @(negedge clk)
        mosi <= 1;
        sclk <= 1;
        @(negedge clk)
        @(negedge clk)

        // bit 6
        sclk <= 0;
        @(negedge clk)
        @(negedge clk)
        mosi <= 1;
        sclk <= 1;
        @(negedge clk)
        @(negedge clk)

        // bit 7
        sclk <= 0;
        @(negedge clk)
        @(negedge clk)
        mosi <= 0;
        sclk <= 1;
        @(negedge clk)
        @(negedge clk)

        // bit 8
        sclk <= 0;
        @(negedge clk)
        @(negedge clk)
        sclk <= 1;
        @(negedge clk)
        @(negedge clk)

        `ASSERT_EQ(result, 8'b10011110);

        #10



        `END_TEST
    end

    main main
        ( ._i_clk(clk)
        , ._i_rst(rst)
        , ._i_sclk_unsync(sclk)
        , ._i_mosi_unsync(mosi)
        , .__output(result)
        );
endmodule
