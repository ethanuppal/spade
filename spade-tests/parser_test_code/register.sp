entity counter(clk: Clock, reset: bool, count_enable: bool) -> Integer<16> {
    reg(clk) counter reset(rst, 0) = {
        if count_enable {
            counter + 1
        }
        else {
            counter
        }
    }

    counter
}
