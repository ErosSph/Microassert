// Diagnostic corpus, not a held-out research benchmark. Labels live in tests.
module decode_case(input clk, input [3:0] op, output reg flag);
 always @(posedge clk) begin
  flag <= 0;
  case (op)
   4'h9: flag <= 1;
  endcase
 end
endmodule

module wide_mux(input clk, input en, input [7:0] a, b, output reg [7:0] q);
 always @(posedge clk) begin
  q <= a;
  if (en) q <= b;
 end
endmodule

module boolean_enable(input clk, input en, output reg q);
 always @(posedge clk) begin
  q <= 0;
  if (en) q <= 1;
 end
endmodule

module inequality_flag(input clk, input [3:0] x, output reg q);
 always @(posedge clk) begin
  q <= 0;
  if (x > 4'd3) q <= 1;
 end
endmodule

module negated_comparison(input clk, input [3:0] x, output reg q);
 always @(posedge clk) begin
  q <= 0;
  if (!(x == 4'd3)) q <= 1;
 end
endmodule

module mixed_decode(input clk, input [3:0] x, input en, output reg q);
 always @(posedge clk) begin
  q <= 0;
  if (x == 4'd3 || en) q <= 1;
 end
endmodule

module counter_feedback(input clk, input rst, output reg [2:0] q);
 always @(posedge clk) begin
  if (rst) q <= 0;
  else if (q == 3'd5) q <= 0;
  else q <= q + 1;
 end
endmodule

module fsm_constant(input clk, input rst, input en, output reg [1:0] state);
 always @(posedge clk) begin
  if (rst) state <= 0;
  else case (state)
   0: if (en) state <= 1;
   1: state <= 2;
   default: state <= 0;
  endcase
 end
endmodule

module copy_pipeline(input clk, input [7:0] d, output reg [7:0] q);
 reg [7:0] middle;
 always @(posedge clk) begin
  middle <= d;
  q <= middle;
 end
endmodule

module arithmetic_chain(input clk, input [7:0] d, output reg [7:0] q);
 reg [7:0] middle;
 always @(posedge clk) begin
  middle <= d + 1;
  q <= middle ^ 8'h5a;
 end
endmodule

module different_clock(input c1, c2, input [7:0] d, output reg [7:0] q);
 reg [7:0] middle;
 always @(posedge c1) middle <= d;
 always @(posedge c2) q <= middle;
endmodule

module opposite_edge(input clk, input [7:0] d, output reg [7:0] q);
 reg [7:0] middle;
 always @(posedge clk) middle <= d;
 always @(negedge clk) q <= middle;
endmodule

module bit_lifecycle(input clk, input request, output reg response);
 reg active;
 always @(posedge clk) begin
  if (request) active <= 1;
  if (active) begin
   active <= 0;
   response <= 1;
  end else response <= 0;
 end
endmodule

module unrelated_set_clear(input clk, input a, b, output reg q);
 always @(posedge clk) begin
  if (a) q <= 1;
  if (b) q <= 0;
 end
endmodule

// Supported intent, alternative encoding: measure misses rather than relabel.
module continuous_decode(input [3:0] op, output q);
 assign q = op == 4'h9;
endmodule

module split_fsm(input clk, input rst, input en, output reg [1:0] state);
 reg [1:0] next_state;
 always @* begin
  next_state = state;
  case (state)
   0: if (en) next_state = 1;
   1: next_state = 2;
   default: next_state = 0;
  endcase
 end
 always @(posedge clk) begin
  if (rst) state <= 0;
  else state <= next_state;
 end
endmodule
