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


    reg valid;
    reg[15:0] index;
    wire[16:0] result;

    initial begin
        index <= 0;
        #1

        // The valid bit here might seem inverted, but because the enum is
        // declared as `Some(T), None`, the 0th option is the `Some` case
        `ASSERT_EQ(result, 11);

        index <= 1;

        #1

        `ASSERT_EQ(result, 12)

        index <= 2;

        #1

        `ASSERT_EQ(result, 13)

        `END_TEST
    end

    e_uut uut
        ( ._i_index(index)
        , .__output(result)
        );
endmodule
