// look in pins.pcf for all the pin names on the TinyFPGA BX board
module top (
    input clk,

    output[7:0] pmod7,
    input[3:0] pmod0,
    output[3:0] pmod0Lower
);
    wire rst;
    assign rst = pmod0[2];

    wire[15:0] result;
    wire sclk;
    wire mosi;
    wire cs;

    assign pmod0Lower[0] = sclk;
    assign pmod0Lower[2] = mosi;
    assign pmod0Lower[3] = cs;

    assign pmod7 = result[10:3];

    main main
        ( ._i_clk(clk)
        , ._i_rst(rst)
        , ._i_miso_unsync(pmod0[1])
        , .__output({sclk, mosi, cs, result})
        );
endmodule

