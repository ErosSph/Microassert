module req8_producer (
    input wire clk,
    input wire rst_n,
    input wire ready,
    output reg valid,
    output reg [7:0] data
);
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            valid <= 1'b0;
            data <= 8'h00;
        end else if (ready) begin
            valid <= 1'b1;
            data <= data + 8'h01;
        end
    end
endmodule

module req8_consumer (
    input wire valid,
    input wire [7:0] data,
    output wire ready,
    output wire [7:0] observed
);
    assign ready = valid;
    assign observed = data;
endmodule

module req8_top (
    input wire clk,
    input wire rst_n,
    output wire [7:0] observed
);
    wire producer_valid;
    wire producer_ready;
    wire [7:0] producer_data;
    wire [7:0] consumer_data;

    req8_producer u_producer (
        .clk(clk), .rst_n(rst_n), .ready(producer_ready),
        .valid(producer_valid), .data(producer_data)
    );

    assign consumer_data = producer_data;

    req8_consumer u_consumer (
        .valid(producer_valid), .data(consumer_data),
        .ready(producer_ready), .observed(observed)
    );
endmodule
