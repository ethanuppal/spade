`include "../../output_test/vatch/main.v"

module spi_tb();
    reg clk;

    `SETUP_TEST

    initial begin
        $dumpfile(`VCD_OUTPUT);
        $dumpvars(0, spi_tb);
        clk = 1;
        forever begin
            clk = ~clk;
            #1;
        end
    end


    reg rst;
    wire sclk;
    wire mosi;
    wire busy;
    reg miso;
    reg[16:0] to_transmit;
    wire[16:0] received;

    // We don't care about precise timing for the received data, just that
    // it has all arrived in one piece by the end of the transmission. So this
    // will store the last received byte
    reg[15:0] received_latched;
    initial begin
        @(negedge received[16]);
        received_latched = received[15:0];
    end

    integer i;

    reg[15:0] miso_data;

    initial begin
        rst = 1;
        to_transmit <= 17'b1_0000_0000_0000_0000;
        miso_data <= 16'h9D0F;
        #4
        rst = 0;

        miso <= miso_data[0];

        repeat (2000) @(negedge clk);
        `ASSERT_EQ(busy, 0);
        `ASSERT_EQ(sclk, 1);

        to_transmit <= 17'b0_1011_0010_1010_0101;
        @(negedge clk)
        @(negedge clk)

        for (i = 0; i < 16; i = i + 1) begin
            // Clock should still be high and data set
            `ASSERT_EQ(sclk, 1);
            `ASSERT_EQ(mosi, to_transmit[i]);
            miso <= miso_data[15-i];
            repeat(50) @(negedge clk);
            // Clock should have fallen
            `ASSERT_EQ(sclk, 0);
            repeat(50) @(negedge clk);
        end

        `ASSERT_EQ(sclk, 1);

        `ASSERT_EQ(received_latched, miso_data);

        `ASSERT_EQ(busy, 0);

        #100

        `END_TEST
    end

    spi uut
        ( ._i_clk(clk)
        , ._i_rst(rst)
        , ._i_to_transmit(to_transmit)
        , ._i_miso(miso)
        , .__output({sclk, mosi, busy, received})
        );
endmodule

module main_tb();
    reg clk;

    `SETUP_TEST

    initial begin
        $dumpfile(`VCD_OUTPUT);
        $dumpvars(0, main_tb);
        clk = 1;
        forever begin
            clk = ~clk;
            #1;
        end
    end


    reg rst;
    wire sclk;
    wire mosi;
    wire cs;
    reg miso;
    reg[15:0] value;

    initial begin
        rst = 1;
        #4
        rst = 0;
        #10000

        `END_TEST
    end

    main uut
        ( ._i_clk(clk)
        , ._i_rst(rst)
        , ._i_miso_unsync(miso)
        , .__output({sclk, mosi, cs, value})
        );
endmodule
