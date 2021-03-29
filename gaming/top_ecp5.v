// look in pins.pcf for all the pin names on the TinyFPGA BX board
module top (
    input clk,    // 16MHz clock

    output[2:0] ld5,
    output[2:0] ld6,
    output[2:0] ld7,
    output[2:0] ld8
);
    wire valid;
    wire enable = 1'b1;
    reg rst = 1;

    always @(posedge clk) begin
        rst <= 0;
    end

    wire[11:0] out;

    pong pong
        ( ._i_clk(clk)
        , ._i_rst(rst)
        // , ._i_tick_len(25_000_000)
        , .__output(out)
        );


    assign ld5 = ~out[5:3];
    assign ld6 = ~out[2:0];
    assign ld7 = ~out[11:9];
    assign ld8 = ~out[8:6];

    // assign LD5_R = disp[7];
    // assign LD5_G = disp[6];
    // assign LD5_B = disp[5];
    // assign PIN_4 = disp[4];
    // assign PIN_5 = disp[3];
    // assign PIN_6 = disp[2];
    // assign PIN_7 = disp[1];
    // assign PIN_8 = disp[0];
endmodule

