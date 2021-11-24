`include "../../output_test/vatch/main.v"

module vga_tb();
    reg clk;

    `SETUP_TEST

    initial begin
        $dumpfile(`VCD_OUTPUT);
        $dumpvars(0, vga_tb);
        clk = 1;
        forever begin
            clk = ~clk;
            #1;
        end
    end


    reg rst;
    wire cs;
    wire hsync, vsync, r, g, b;

    integer i;

    initial begin
        rst = 1;
        #4
        rst = 0;

        #4000000

        `END_TEST
    end

    main uut
        ( ._i_clk(clk)
        , ._i_rst(rst)
        , .__output({hsync, vsync, r, g, b})
        );
endmodule
