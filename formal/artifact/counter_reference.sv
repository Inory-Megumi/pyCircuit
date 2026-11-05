// Independent known-two-state reference: increment is considered before decrement.
module counter_reference (
    input wire clk,
    input wire rst,
    input wire inc_request,
    input wire dec_request,
    output reg [2:0] count
);
    wire [2:0] inc_candidate =
        inc_request && count < 3'd5 ? count + 3'd1 : count;
    wire [2:0] next_count =
        dec_request && inc_candidate > 3'd0 ? inc_candidate - 3'd1 : inc_candidate;

    always @(posedge clk) begin
        if (rst)
            count <= 3'd0;
        else
            count <= next_count;
    end
endmodule
