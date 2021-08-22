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
    reg[15:0] in_x;
    wire[16:0] result;

    initial begin
        in_x <= 123;
        valid <= 1;
        #1

        // The valid bit here might seem inverted, but because the enum is
        // declared as `Some(T), None`, the 0th option is the `Some` case
        `ASSERT_EQ(result, {1'b0, in_x});

        valid <= 0;

        #1
        `ASSERT_EQ(result[16], 1'b1);

        `END_TEST
    end

    uut uut
        ( ._i_x(in_x)
        , ._i_valid(valid)
        , .__output(result)
        );
endmodule
