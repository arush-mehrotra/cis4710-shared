/* INSERT NAME AND PENNKEY HERE */

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);

    // TODO: your code here
    wire[31:0] temp_remainder[33];
    wire[31:0] temp_quotient[33];
    wire[31:0] temp_dividend[33];

    assign temp_remainder[0] = 32'b0;
    assign temp_quotient[0] = 32'b0;
    assign temp_dividend[0] = i_dividend[31:0];

    genvar i;
        generate for (i = 0; i < 32; i++) begin: g_loop
            divu_1iter d1(.i_dividend(temp_dividend[i]), .i_divisor(i_divisor[31:0]),
            .i_remainder(temp_remainder[i]), .i_quotient(temp_quotient[i]),
            .o_dividend(temp_dividend[i+1]), .o_remainder(temp_remainder[i+1]),
            .o_quotient(temp_quotient[i+1]));
        end endgenerate

    assign o_remainder[31:0] = temp_remainder[32][31:0];
    assign o_quotient[31:0] = temp_quotient[32][31:0];

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
  /*
    for (int i = 0; i < 32; i++) {
        remainder = (remainder << 1) | ((dividend >> 31) & 0x1);
        if (remainder < divisor) {
            quotient = (quotient << 1);
        } else {
            quotient = (quotient << 1) | 0x1;
            remainder = remainder - divisor;
        }
        dividend = dividend << 1;
    }
    */

    // TODO: your code here
    wire [31:0] temp_remainder;
    assign temp_remainder[31:0] = (i_remainder << 1) | ((i_dividend >> 31) & 32'b1);
    assign o_quotient[31:0] = (temp_remainder < i_divisor) ? (i_quotient << 1) : ((i_quotient << 1) | 32'b1);
    assign o_remainder[31:0] = (temp_remainder < i_divisor) ? temp_remainder : (temp_remainder - i_divisor);
    assign o_dividend[31:0] = i_dividend << 1;


endmodule
