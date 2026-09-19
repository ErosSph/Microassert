module grounding_flow_fixture (
    input  logic        clk,
    input  logic        resetn,
    input  logic        en,
    input  logic [6:0]  opcode,
    input  logic [2:0]  funct3,
    input  logic [6:0]  funct7,
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic [31:0] comb_result,
    output logic [31:0] seq_result,
    output logic [31:0] mem_addr,
    output logic [31:0] write_data,
    output logic [31:0] cycle_counter,
    output logic [7:0]  narrow_result,
    output logic [1:0]  state,
    output logic        event_o,
    output wire  [31:0] passthrough
);
    localparam IDLE = 2'd0, BUSY = 2'd1;

    assign passthrough = a;

    always_comb begin
        comb_result = 32'h0;
        mem_addr = a;
        write_data = b;
        narrow_result = 8'h0;
        event_o = 1'b0;
        if (opcode == 7'h33 && funct3 == 3'h0 && funct7 == 7'h00) begin
            comb_result = a + b;
            event_o = 1'b1;
        end else if (opcode == 7'h33 && funct3 == 3'h0 && funct7 == 7'h20) begin
            comb_result = a - b;
        end
        case (state)
            IDLE, 2'd2: if (en) narrow_result = a[7:0];
            BUSY: narrow_result = b[7:0];
            default: narrow_result = 8'h0;
        endcase
    end

    always_ff @(posedge clk) begin
        if (!resetn) begin
            seq_result <= 32'h0;
            cycle_counter <= 32'h0;
            state <= IDLE;
        end else if (en) begin
            seq_result <= comb_result;
            cycle_counter <= cycle_counter + 1'b1;
            state <= BUSY;
        end else begin
            cycle_counter <= cycle_counter + 1'b1;
            state <= IDLE;
        end
    end
endmodule
