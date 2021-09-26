

// look in pins.pcf for all the pin names on the TinyFPGA BX board
module top (
    input CLK,    // 16MHz clock
    output LED,   // User/boot LED next to power LED
    output USBPU,  // USB pull-up resistor

    // Debug pin
    output PIN_13,

    output PIN_1,
    output PIN_2,
    output PIN_3,
    output PIN_4,
    output PIN_5,
    output PIN_6,
    output PIN_7,
    output PIN_8
);
    wire valid;
    wire enable = 1'b1;
    reg[7:0] disp;

    reg[23:0] dispCounter;
    reg[2:0] byteCounter;

    reg rst = 1;

    always @(posedge CLK) begin
        rst <= 0;
    end

    reg[15:0] t = 'hffff;

    always @(posedge CLK) begin
        t <= t + 1;
    end

    always @(posedge CLK) begin
        if (dispCounter == 8_000_000) begin
            dispCounter = 0;
            if (byteCounter == 2) begin
                byteCounter <= 0;
            end
            else begin
                byteCounter = byteCounter + 1;
            end
        end
        else begin
            dispCounter = dispCounter + 1;
        end
    end

     pong pong
        ( ._i_clk(CLK)
        , ._i_rst(rst)
        , ._i_tick_length(4_000_000)
        , .__output(disp)
        );



    assign PIN_13 = valid;
    assign PIN_1 = disp[7];
    assign PIN_2 = disp[6];
    assign PIN_3 = disp[5];
    assign PIN_4 = disp[4];
    assign PIN_5 = disp[3];
    assign PIN_6 = disp[2];
    assign PIN_7 = disp[1];
    assign PIN_8 = disp[0];
endmodule

