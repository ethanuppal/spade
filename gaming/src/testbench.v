module counter_tb();
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
    reg[31:0] tick_length;
    reg[7:0] result;

    initial begin
        rst <= 1;
        tick_length <= 3;

        #10
        rst <= 0;

        #200

        // $finish();
        $finish();
    end

    pong pong
        ( ._i_clk(clk)
        , ._i_rst(rst)
        , ._i_tick_len(tick_length)
        , .__output(result)
        );
endmodule
