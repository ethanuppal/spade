module Wire #(
  parameter WIDTH = 32,
) (
  input wire logic [WIDTH-1:0] in,
  output wire logic [WIDTH-1:0] out
);
  assign out = in;
endmodule
