module progress_mask(input clk,reset,start, output reg done, output reg [7:0] mask);
always @(posedge clk) begin
 if(reset) begin mask<=0; done<=0; end
 else if(start) begin mask<=1<<7; done<=0; end
 else begin mask<=mask>>1; if(!mask) done<=1; end
end
endmodule
module non_onehot_mask(input clk,reset,start, output reg done, output reg [7:0] mask);
always @(posedge clk) begin
 if(reset) begin mask<=0; done<=0; end
 else if(start) mask<=3;
 else begin mask<=mask>>1; if(!mask) done<=1; end
end
endmodule
module enabled_stages(input clk,reset,en, input [7:0] data, output reg [7:0] q);
reg [7:0] mid;
always @(posedge clk) begin
 if(reset) begin mid<=0; q<=0; end
 else begin mid<=en?data:mid; q<=en?mid:q; end
end
endmodule
module non_copy_stages(input clk,reset,en, input [7:0] data, output reg [7:0] q);
reg [7:0] mid;
always @(posedge clk) begin
 if(reset) begin mid<=0; q<=0; end
 else begin mid<=en?(data+1):mid; q<=en?mid:q; end
end
endmodule
module decode_history_boundary(input clk, input [3:0] opcode, input gate,
                               output reg history, output reg merged);
wire first = opcode==4'd1;
wire second = opcode==4'd2;
wire selected = first || second;
always @(posedge clk) begin
 history <= selected && gate;
 merged <= first || second;
end
endmodule
module sparse_fsm(input clk,reset,step, output reg [2:0] state);
always @(posedge clk) begin
 if(reset) state<=0;
 else case(state)
  0: if(step) state<=2;
  2: if(step) state<=5;
  default: state<=0;
 endcase
end
endmodule
module indexed_bank(input clk,reset,en,en2, input [3:0] wa,wb,ra,rb,
                    input [7:0] wd,wd2, output [7:0] qa,qb);
reg [7:0] storage [15:0];
always @(posedge clk) begin
 if(en) storage[wa]<=wd;
 if(en2) storage[wb]<=wd2;
end
assign qa=storage[ra];
assign qb=storage[rb];
endmodule
module gated_bank(input clk,reset,en, input [3:0] wa,ra,rb,
                  input [7:0] wd, output [7:0] qa,qb);
reg [7:0] storage [0:15];
always @(posedge clk) if(en) storage[wa]<=wd;
assign qa=ra ? storage[ra] : 0;
assign qb=rb ? storage[rb] : 0;
endmodule
module uninitialized_mask(input clk,reset,start, output reg done, output reg [7:0] mask);
always @(posedge clk) begin
 if(reset) done<=0;
 else if(start) mask<=1<<7;
 else begin mask<=mask>>1; if(!mask) done<=1; end
end
endmodule
