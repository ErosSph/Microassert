// Explicit structural intent, independent of signal-name matching.
module unit_counter(input clk, rst, en, output reg [7:0] q);
always @(posedge clk) if(rst) q <= 0; else if(en) q <= q + 1;
endmodule
module unit_accumulator(input clk, rst, input [7:0] d, output reg [7:0] q);
always @(posedge clk) if(rst) q <= 0; else q <= q + d;
endmodule
module unit_mixed_feedback(input clk, input [7:0] d, input mode, output reg [7:0] q);
always @(posedge clk) if(mode) q <= q + 1; else q <= d;
endmodule
module unit_shift(input [7:0] a, input [2:0] b, output [7:0] y);
assign y = a << b;
endmodule
module unit_compare(input [7:0] a,b, output y);
assign y = a < b;
endmodule
module unit_multiply(input [7:0] a,b, output [15:0] y);
assign y = a * b;
endmodule
module unit_divide(input [7:0] a,b, output [7:0] y);
assign y = a / b;
endmodule
module unit_mux(input s, input [7:0] a,b, output [7:0] y);
assign y = s ? a : b;
endmodule
module unit_add_only(input [7:0] a,b, output [7:0] y);
assign y = a + b;
endmodule
module unit_inline_alu(input s, input [7:0] a,b, output [7:0] y);
assign y = s ? a+b : a^b;
endmodule
module unit_composed_alu(input s,t, input [7:0] a,b, output [7:0] y);
wire [7:0] add_value = a + b;
wire [7:0] logic_value = a ^ b;
assign y = ({8{s}} & add_value) | ({8{t}} & logic_value);
endmodule
module unit_selector_arithmetic_not_alu(input [7:0] a,b,c,d, output [7:0] y);
assign y = (a+b == c) ? c^d : c&d;
endmodule
module unit_unconnected_operations(input s, input [7:0] a,b, output [7:0] y,z);
assign y = a+b;
assign z = s ? a^b : a&b;
endmodule
module unit_net_vs_variable_initializer(input [7:0] a,b, output [7:0] y);
wire [7:0] real_driver = a+b;
reg [7:0] initial_only = a+b;
assign y = real_driver;
endmodule
module unit_selected_multiply_not_alu(input s, input [7:0] a,b, output [15:0] y);
wire [7:0] normalized = (0-a) ^ b;
assign y = s ? normalized*b : a*b;
endmodule
