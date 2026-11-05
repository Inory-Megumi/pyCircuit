`timescale 1ns/1ps

module checked_tb;
    reg clk = 1'b0;
    reg rst = 1'b0;
    reg inc_request = 1'b0;
    reg dec_request = 1'b0;
    wire [2:0] count;

    observed_counter dut (
        .clk(clk),
        .rst(rst),
        .inc_request(inc_request),
        .dec_request(dec_request),
        .count(count)
    );

    task automatic step(
        input bit reset_request,
        input bit increment_request,
        input bit decrement_request,
        input logic [2:0] expected
    );
        clk = 1'b0;
        rst = reset_request;
        inc_request = increment_request;
        dec_request = decrement_request;
        #1;
        clk = 1'b1;
        #1;
        if (count !== expected)
            $fatal(1, "count=%b expected=%b rst=%b inc=%b dec=%b",
                count, expected, rst, inc_request, dec_request);
        clk = 1'b0;
        #1;
    endtask

    initial begin
        step(1, 0, 0, 3'd0);
        step(0, 0, 0, 3'd0);
        step(0, 1, 0, 3'd1);
        step(0, 1, 1, 3'd1);
        step(0, 0, 1, 3'd0);
        step(0, 1, 1, 3'd0);
        step(0, 1, 0, 3'd1);
        step(0, 1, 0, 3'd2);
        step(0, 1, 0, 3'd3);
        step(0, 1, 0, 3'd4);
        step(0, 1, 0, 3'd5);
        step(0, 1, 0, 3'd5);
        step(0, 1, 1, 3'd4);
        step(1, 0, 0, 3'd0);
        $display("PYC_FORMAL_CHECKED_RTL_PASS");
        $finish;
    end
endmodule
