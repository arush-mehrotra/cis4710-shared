/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned_pipelined (
    input wire clk, rst,
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    // TODO: your code here

    // Stage 1 Result Wires 
    wire[31:0] temp_remainder[17];
    wire[31:0] temp_quotient[17];
    wire[31:0] temp_dividend[17];

    assign temp_remainder[0] = 32'b0;
    assign temp_quotient[0] = 32'b0;
    assign temp_dividend[0] = i_dividend[31:0];


    // Registers
    reg[31:0] intermediate_remainder;
    reg[31:0] intermediate_quotient;
    reg[31:0] intermediate_dividend;

    // Stage 1
    genvar i;
        generate for (i = 0; i < 16; i++) begin: g_loop
            divu_1iter d1(.i_dividend(temp_dividend[i]), .i_divisor(i_divisor[31:0]),
            .i_remainder(temp_remainder[i]), .i_quotient(temp_quotient[i]),
            .o_dividend(temp_dividend[i+1]), .o_remainder(temp_remainder[i+1]),
            .o_quotient(temp_quotient[i+1]));
        end endgenerate


    // Assign Values to Registers
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            intermediate_remainder <= 32'b0;
            intermediate_quotient <= 32'b0;
            intermediate_dividend <= 32'b0;
        end else begin
            intermediate_remainder <= temp_remainder[16];
            intermediate_quotient <= temp_quotient[16];
            intermediate_dividend <= temp_dividend[16];
        end
    end

    // Stage 2 Result Wires 
    wire[31:0] temp_remainder_2[17];
    wire[31:0] temp_quotient_2[17];
    wire[31:0] temp_dividend_2[17];

    assign temp_remainder_2[0] = intermediate_remainder;
    assign temp_quotient_2[0] = intermediate_quotient;
    assign temp_dividend_2[0] = intermediate_dividend;

    // Stage 2
    genvar j;
        generate for (j = 0; j < 16; j++) begin: g_loop_2
            divu_1iter d1(.i_dividend(temp_dividend_2[j]), .i_divisor(i_divisor[31:0]),
            .i_remainder(temp_remainder_2[j]), .i_quotient(temp_quotient_2[j]),
            .o_dividend(temp_dividend_2[j+1]), .o_remainder(temp_remainder_2[j+1]),
            .o_quotient(temp_quotient_2[j+1]));
        end endgenerate
    
    // Assign Final Values
    assign o_remainder[31:0] = temp_remainder_2[16][31:0];
    assign o_quotient[31:0] = temp_quotient_2[16][31:0];

endmodule


module divu_1iter (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    input  wire [31:0] i_remainder,
    input  wire [31:0] i_quotient,
    output wire [31:0] o_dividend,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

  // TODO: copy your code from HW2A here
    wire [31:0] temp_remainder;
    assign temp_remainder[31:0] = (i_remainder << 1) | ((i_dividend >> 31) & 32'b1);
    assign o_quotient[31:0] = (temp_remainder < i_divisor) ? (i_quotient << 1) : ((i_quotient << 1) | 32'b1);
    assign o_remainder[31:0] = (temp_remainder < i_divisor) ? temp_remainder : (temp_remainder - i_divisor);
    assign o_dividend[31:0] = i_dividend << 1;

endmodule
