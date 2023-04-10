`include "vatch/main.v"

module counter_tb();
    `SETUP_TEST

    initial begin
        $dumpfile(`VCD_OUTPUT);
        $dumpvars(0, counter_tb);
    end


    reg[9:0] val;
    wire[11:0] result;

    initial begin
        val <= 10;
        #1
        `ASSERT_EQ(result, 20);

        val <= 5;
        #1
        `ASSERT_EQ(result, 10);


        #20

        `END_TEST
    end

    \arbiter counter
        ( .val_i(val)
        , .output__(result)
        );
endmodule
