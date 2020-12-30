entity counter(clk: clk, rst: bit, max_value: uint[16]) -> uint[16] {
    reg (clk) value reset (rst: max_value) = {
        if value == max_value {
            0
        }
        else {
            value + 1
        }
    }

    value
}
