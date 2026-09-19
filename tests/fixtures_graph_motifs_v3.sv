module bank_2r1w(input clk,we, input [3:0] wa,ra,rb, input [7:0] wd,
                 output [7:0] qa,qb);
reg [7:0] storage [0:15];
always @(posedge clk) if(we) storage[wa] <= wd;
assign qa = storage[ra];
assign qb = storage[rb];
endmodule
module bank_same_address(input clk,we, input [3:0] wa,ra, input [7:0] wd,
                         output [7:0] qa,qb);
reg [7:0] storage [0:15];
always @(posedge clk) if(we) storage[wa] <= wd;
assign qa = storage[ra];
assign qb = storage[ra];
endmodule
module load_store_rmw(input [1:0] op, input [31:0] base,offset,raw_data,write_data,
                       output reg [31:0] address,read_result,store_result);
wire [31:0] sum = base + offset;
always @* begin
 address=0; read_result=0; store_result=0;
 case(op)
  2'b01: begin address=sum; read_result={24'b0,raw_data[7:0]}; end
  2'b10: begin address=sum; store_result={raw_data[31:8],write_data[7:0]}; end
 endcase
end
endmodule
module unrelated_subword_paths(input [1:0] op, input [31:0] base,offset,raw_data,write_data,
                               output [31:0] address, output reg [31:0] read_result,store_result);
assign address = base+offset;
always @* begin
 read_result=0; store_result=0;
 case(op)
  2'b01: read_result={24'b0,raw_data[7:0]};
  2'b10: store_result={raw_data[31:8],write_data[7:0]};
 endcase
end
endmodule
module iter_multiply(input clk,rst,start, input [7:0] a,b,
                     output reg done, output reg [15:0] acc);
reg [15:0] shifted;
reg [7:0] bits;
reg [3:0] count;
reg busy;
always @(posedge clk) begin
 done<=0;
 if(rst) begin busy<=0; acc<=0; shifted<=0; bits<=0; count<=0; end
 else if(start) begin busy<=1; shifted<=a; bits<=b; count<=8; acc<=0; end
 else if(busy) begin
  if(count==0) begin done<=1; busy<=0; end
  else begin
   if(bits[0]) acc<=acc+shifted;
   shifted<=shifted<<1; bits<=bits>>1; count<=count-1;
  end
 end
end
endmodule
module iter_divide(input clk,rst,start, input [7:0] a,b,
                   output reg done, output reg [15:0] remainder);
reg [15:0] shifted;
reg [3:0] count;
reg busy;
always @(posedge clk) begin
 done<=0;
 if(rst) begin busy<=0; remainder<=0; shifted<=0; count<=0; end
 else if(start) begin busy<=1; shifted<=b<<7; remainder<=a; count<=8; end
 else if(busy) begin
  if(count==0) begin done<=1; busy<=0; end
  else begin
   if(remainder>=shifted) remainder<=remainder-shifted;
   shifted<=shifted>>1; count<=count-1;
  end
 end
end
endmodule
module staged_decode(input [7:0] opcode, input gate, output result, output bad, output merged, output bad_merge);
wire p = opcode[3:0]==4'h3;
wire q = opcode[7:4]==4'h7;
assign result = p && q && gate;
assign bad = p || gate;
assign merged = |{p,q};
assign bad_merge = |{p,gate};
endmodule
module case_alu(input [1:0] op, input [7:0] a,b, output reg [7:0] y);
always @* begin
 y=0;
 case(op)
  2'b00: y=a+b;
  2'b01: y=a^b;
 endcase
end
endmodule
