module ALU(
    input logic[31:0] a,
    input logic[31:0] b,
    input logic[2:0] ALUControl,
    output logic[31:0] result,
    output logic zero
);


always_comb begin

    case(ALUControl) 

        3'b000: begin
            result = a + b;
        end
        3'b001: begin
            result = a - b;
        end
        3'b010: begin
            result = a&b;
        end
        3'b011: begin
            result = a|b;
        end
        3'b100: begin
            result = (a<b) ? 32'd1 : 32'd0; 
        end
        default: begin
            result = 32'hxxxxx;
        end
    endcase

end

assign zero = ((a-b) == 32'd0);


endmodule 

`timescale 1ns / 1ps

module ALU_tb;

    // Declare testbench signals
    logic [31:0] a, b;
    logic [2:0] ALUControl;
    logic [31:0] result;
    logic zero;

    // Instantiate the ALU
    ALU dut (
        .a(a),
        .b(b),
        .ALUControl(ALUControl),
        .result(result),
        .zero(zero)
    );

    // Test procedure
    initial begin
        $display("Starting ALU Test...");

        // Test ADD (a + b)
        a = 32'd10; b = 32'd5; ALUControl = 3'b000;
        #10;
        $display("ADD: 10 + 5 = %d (Expected: 15)", result);

        // Test SUB (a - b)
        a = 32'd10; b = 32'd5; ALUControl = 3'b001;
        #10;
        $display("SUB: 10 - 5 = %d (Expected: 5)", result);

        // Test AND (a & b)
        a = 32'hF0F0F0F0; b = 32'h0F0F0F0F; ALUControl = 3'b010;
        #10;
        $display("AND: F0F0F0F0 & 0F0F0F0F = %h (Expected: 00000000)", result);

        // Test OR (a | b)
        a = 32'hF0F0F0F0; b = 32'h0F0F0F0F; ALUControl = 3'b011;
        #10;
        $display("OR: F0F0F0F0 | 0F0F0F0F = %h (Expected: FFFFFFFF)", result);

        // Test SLT (Set Less Than, Unsigned)
        a = 32'd5; b = 32'd10; ALUControl = 3'b100;
        #10;
        $display("SLT: 5 < 10 = %d (Expected: 1)", result);

        a = 32'd15; b = 32'd10; ALUControl = 3'b100;
        #10;
        $display("SLT: 15 < 10 = %d (Expected: 0)", result);

        // Test ZERO flag
        a = 32'd10; b = 32'd10; ALUControl = 3'b001; // 10 - 10 = 0
        #10;
        $display("ZERO Flag (SUB 10-10): %d (Expected: 1)", zero);

        a = 32'd10; b = 32'd5; ALUControl = 3'b001; // 10 - 5 = 5
        #10;
        $display("ZERO Flag (SUB 10-5): %d (Expected: 0)", zero);

        $display("ALU Test Completed.");
        $finish;
    end

endmodule
