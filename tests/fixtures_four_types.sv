module fixtures_four_types (
    input logic clk,
    input logic resetn,
    input logic req_valid,
    input logic req_ready,
    input logic [7:0] req_data,
    input logic en,
    input logic [7:0] a,
    input logic [7:0] b,
    output logic [7:0] result
);
    localparam IDLE = 2'b01, BUSY = 2'b10;
    logic [1:0] state;
    logic [7:0] held;

    always_ff @(posedge clk) begin
        if (!resetn) begin
            state <= IDLE;
            held <= 8'h00;
        end else begin
            case (state)
                IDLE: if (req_valid) state <= BUSY;
                BUSY: if (req_ready) state <= IDLE;
                default: state <= IDLE;
            endcase
            if (en)
                held <= req_data;
        end
    end

    always_comb result = a + b;
endmodule
