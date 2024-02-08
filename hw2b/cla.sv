`timescale 1ns / 1ps

/**
 * @param a first 1-bit input
 * @param b second 1-bit input
 * @param g whether a and b generate a carry
 * @param p whether a and b would propagate an incoming carry
 */
module gp1(input wire a, b,
           output wire g, p);
   assign g = a & b;
   assign p = a | b;
endmodule

/**
 * Computes aggregate generate/propagate signals over a 4-bit window.
 * @param gin incoming generate signals
 * @param pin incoming propagate signals
 * @param cin the incoming carry
 * @param gout whether these 4 bits internally would generate a carry-out (independent of cin)
 * @param pout whether these 4 bits internally would propagate an incoming carry from cin
 * @param cout the carry outs for the low-order 3 bits
 */
module gp4(input wire [3:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [2:0] cout);

   // TODO: your code here
   wire gout0, pout0, gout1, pout1, gout2, pout2, gout3, pout3;

   gp1 gp1_0(.a(gin[0]), .b(pin[0]), .g(gout0), .p(pout0));
   gp1 gp1_1(.a(gin[1]), .b(pin[1]), .g(gout1), .p(pout1));
   gp1 gp1_2(.a(gin[2]), .b(pin[2]), .g(gout2), .p(pout2));
   gp1 gp1_3(.a(gin[3]), .b(pin[3]), .g(gout3), .p(pout3));

   assign pout = pout3 & pout2 & pout1 & pout0;

   wire temp_g2, temp_g1, temp_g0;
   assign temp_g2 = pout3 & gout2;
   assign temp_g1 = pout3 & pout2 & gout1;
   assign temp_g0 = pout3 & pout2 & pout1 & gout0;
   assign gout = temp_g2 | temp_g1 | temp_g0 | gout3;

   // cout 0
   assign cout[0] = gout0 | (pout0 & cin);

   // cout 1
   assign cout[1] = gout1 | (pout1 & gout0) | (pout1 & pout0 & cin);

   // cout 2
   assign cout[2] = gout2 | (pout2 & gout1) | (pout2 & pout1 & gout0) | (pout2 & pout1 & pout0 & cin);

endmodule

/** Same as gp4 but for an 8-bit window instead */
module gp8(input wire [7:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [6:0] cout);

   // TODO: your code here
   wire gout0, pout0, gout1, pout1;

   gp4 gp4_0(.gin(gin[3:0]), .pin(pin[3:0]), .cin(cin), .gout(gout0), .pout(pout0), .cout(cout[2:0]));
   gp4 gp4_1(.gin(gin[7:4]), .pin(pin[7:4]), .cin(cin), .gout(gout1), .pout(pout1), .cout(cout[6:4]));

   assign gout = gout1 | (pout1 & gout0);
   assign pout = pout1 & pout0;
   assign cout[3] = gout0 | (pout0 & cin);

endmodule

module cla
  (input wire [31:0]  a, b,
   input wire         cin,
   output wire [31:0] sum);

   // TODO: your code here
   wire gout0, pout0, gout1, pout1, gout2, pout2, gout3, pout3;
   wire[31:0] cout;

   gp8 gp8_0(.gin(a[7:0]), .pin(b[7:0]), .cin(cin), .gout(gout0), .pout(pout0), .cout(cout[6:0]));
   gp8 gp8_1(.gin(a[15:8]), .pin(a[15:8]), .cin(cout[7]), .gout(gout1), .pout(pout1), .cout(cout[14:8]));
   gp8 gp8_2(.gin(a[23:16]), .pin(a[23:16]), .cin(cout[15]), .gout(gout2), .pout(pout2), .cout(cout[22:16]));
   gp8 gp8_3(.gin(a[31:24]), .pin(a[31:24]), .cin(cout[23]), .gout(gout3), .pout(pout3), .cout(cout[30:24]));

   assign cout[7] = gout0 | (pout0 & cin);
   assign cout[15] = gout1 | (pout1 & gout0) | (pout1 & pout0 & cin);
   assign cout[23] = gout2 | (pout2 & gout1) | (pout2 & pout1 & gout0) | (pout2 & pout1 & pout0 & cin);
   assign cout[31] = gout3 | (pout3 & gout2) | (pout3 & pout2 & gout1) | (pout3 & pout2 & pout1 & gout0) | (pout3 & pout2 & pout1 & pout0 & cin);

   assign sum[31:0] = a[31:0] ^ b[31:0] ^ cout[31:0];

endmodule
