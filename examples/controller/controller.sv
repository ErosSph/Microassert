// Small original fixture for offline installation and formal smoke tests.
module controller (
    input wire clk, input wire rst_n,
    input wire start, input wire [1:0] opcode,
    input wire [7:0] data_i,
    output reg busy, output reg done, output reg [7:0] data_o
);
    reg [1:0] state;
    reg decoded;
    localparam IDLE = 2'b00, ACTIVE = 2'b01, COMPLETE = 2'b10;
    always @(posedge clk) begin
        if (!rst_n) begin
            state <= IDLE;
            decoded <= 0;
            busy <= 0;
            done <= 0;
            data_o <= 0;
        end else begin
            decoded <= 0;
            case (opcode)
                2'b10: decoded <= 1;
            endcase
            case (state)
                IDLE: begin
                    done <= 0;
                    if (start) begin
                        state <= ACTIVE;
                        busy <= 1;
                        data_o <= data_i;
                    end
                end
                ACTIVE: state <= COMPLETE;
                COMPLETE: begin
                    state <= IDLE;
                    busy <= 0;
                    done <= 1;
                end
                default: state <= IDLE;
            endcase
        end
    end
endmodule
