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
    reg[7:0] inval;
    wire[15:0] extended;
    wire[3:0] truncated;

    initial begin
        inval <= 1;
        #1

        `ASSERT_EQ(extended, 1);
        `ASSERT_EQ(truncated, 1);

        #1

        inval <= -1;

        #1
        `ASSERT_EQ(extended, -(4'd1));
        `ASSERT_EQ(truncated, -(4'd1));

        inval <= 8'b1000_1010;
        #1
        `ASSERT_EQ(truncated, 4'b1010);
        `ASSERT_EQ(extended, 16'b1111_1111_1000_1010);


        `END_TEST
    end

    uut uut
        ( ._i_inval(inval)
        , .__output({extended, truncated})
        );
endmodule
