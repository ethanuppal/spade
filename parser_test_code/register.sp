entity counter(clk: Clock, reset: bool, count_enable: bool) -> Integer<16> {
    reg(clk) reset(rst, 0) counter = {
        if count_enable {
            counter + 1
        }
        else {
            counter
        }
    }

    counter
}
