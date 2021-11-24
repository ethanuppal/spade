// look in pins.pcf for all the pin names on the TinyFPGA BX board
module top (
    input clk,

    output[7:0] pmod7,
    output[3:0] pmod0,
    output[3:0] pmod0Lower
);
    // assign rst = pmod0[2];

    reg rst = 1;
    always @(posedge clk) begin
        rst <= 0;
    end

    wire vsync, hsync, r, g, b;

    assign pmod7[0] = vsync;
    assign pmod7[1] = hsync;

    assign pmod7[4] = r;
    assign pmod7[5] = g;
    assign pmod7[6] = b;

    main main
        ( ._i_clk(clk)
        , ._i_rst(rst)
        , .__output({hsync, vsync, r, g, b})
        );
endmodule

