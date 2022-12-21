`include "vatch/main.v"

module counter_tb();
    `SETUP_TEST


    reg[7:0] x;
    reg[7:0] y;

    wire[7:0] result;

    integer x_;
    integer y_;
    integer div_result;
    real div_result_real;

    initial begin
        for (x_ = -128; x_ < 127; x_ = x_ + 1) begin
            for (y_ = 0; y_ < 8; y_ = y_ + 1) begin
                div_result_real = $itor(x_) / 2.0**$itor(y_);
                // We want to always round towards 0 here
                if (div_result_real < 0 && $abs(div_result_real - $floor(div_result_real)) == 0.5) begin

                    div_result = real'(div_result_real + 0.5);
                end
                else begin
                    div_result = real'(div_result_real);
                end

                x = x_;
                y = y_;

                #1
                // $display("%0d `div_pow2` %0d = %f (%0d). Got %0d", x_, 2.0 ** y_, div_result_real, div_result, $signed(result));


                `ASSERT_EQ(result, $signed(8'(div_result)))
            end
        end

        #20

        `END_TEST
    end

    \counter counter
        ( .x_i(x)
        , .y_i(y)
        , .output__(result)
        );
endmodule
