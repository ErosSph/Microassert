module req84_patterns (
    input wire clk,
    input wire rst_n,
    input wire [3:0] selector_i,
    input wire request_i,
    input wire [7:0] payload_i,
    output reg response_o,
    output reg decode_o,
    output reg [7:0] pipeline_o
);
    reg [1:0] control_q;
    reg active_q;
    reg [7:0] stage1_q;
    reg [7:0] stage2_q;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            decode_o <= 1'b0;
        end else begin
            decode_o <= 1'b0;
            if (selector_i == 4'h9)
                decode_o <= 1'b1;
        end
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            control_q <= 2'b00;
        end else begin
            case (control_q)
                2'b00: if (request_i) control_q <= 2'b01;
                2'b01: control_q <= 2'b10;
                2'b10: control_q <= 2'b00;
                default: control_q <= 2'b00;
            endcase
        end
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            active_q <= 1'b0;
            response_o <= 1'b0;
        end else begin
            if (request_i)
                active_q <= 1'b1;
            if (active_q) begin
                response_o <= 1'b1;
                active_q <= 1'b0;
            end else begin
                response_o <= 1'b0;
            end
        end
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            stage1_q <= 8'h00;
            stage2_q <= 8'h00;
            pipeline_o <= 8'h00;
        end else begin
            stage1_q <= payload_i;
            stage2_q <= stage1_q;
            pipeline_o <= stage2_q;
        end
    end
endmodule
