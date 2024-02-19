`timescale 1ns / 1ps

/**
 * @param a first 1-bit input
 * @param b second 1-bit input
 * @param g whether a and b generate a carry
 * @param p whether a and b would propagate an incoming carry
 */
module gp1 (
    input  wire a,
    b,
    output wire g,
    p
);
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
module gp4 (
    input wire [3:0] gin,
    pin,
    input wire cin,
    output wire gout,
    pout,
    output wire [2:0] cout
);
  wire inter1, inter2, inter3;

  //assign carry out bits 
  assign inter1 = (cin & pin[0]) | gin[0];
  assign inter2 = (pin[1] & inter1) | gin[1];
  assign inter3 = (pin[2] & inter2) | gin[2];

  assign cout[0] = inter1;
  assign cout[1] = inter2;
  assign cout[2] = inter3;

  //propogate 
  assign pout = pin[0] & pin[1] & pin[2] & pin[3];

  //generate 
  assign gout = (gin[0] & gin[1] & pin[2] & pin[3]) | (gin[2] | gin[3]);

endmodule

/** Same as gp4 but for an 8-bit window instead */
module gp8 (
    input wire [7:0] gin,
    pin,
    input wire cin,
    output wire gout,
    pout,
    output wire [6:0] cout
);

  // TODO: your code here
  wire inter1, inter2, inter3, inter4, inter5, inter6, inter7;

  //assign carry out bits 
  assign inter1 = (cin & pin[0]) | gin[0];
  assign inter2 = (pin[1] & inter1) | gin[1];
  assign inter3 = (pin[2] & inter2) | gin[2];
  assign inter4 = (pin[3] & inter3) | gin[3];
  assign inter5 = (pin[4] & inter4) | gin[4];
  assign inter6 = (pin[5] & inter5) | gin[5];
  assign inter7 = (pin[6] & inter6) | gin[6];
  assign cout[0] = inter1;
  assign cout[1] = inter2;
  assign cout[2] = inter3;
  assign cout[3] = inter4;
  assign cout[4] = inter5;
  assign cout[5] = inter6;
  assign cout[6] = inter7;


  //propogate 
  assign pout = pin[0] & pin[1] & pin[2] & pin[3] & pin[4] & pin[5] & pin[6] & pin[7];

  //generate 
  assign gout = gin[7] | 
              (gin[6] & pin[7]) | 
              (gin[5] & pin[6] & pin[7]) | 
              (gin[4] & (|pin[7:5])) | 
              (gin[3] & (|pin[7:4])) |
              (gin[2] & (|pin[7:3])) |
              (gin[1] & (|pin[7:2])) |
              (gin[0] & (|pin[7:1]));
endmodule

module cla (
    input  wire [31:0] a,
    b,
    input  wire        cin,
    output wire [31:0] sum
);

  // TODO: your code here

  // First lets generate our 32 gp1 modules

  genvar gp1;
  generate
    for (gp1 = 0; gp1 < 32; gp1++) begin
      gp1 new_gp1 (
          .a(a[i]),
          .b(b[i]),
          .g(g[i]),
          .p(p[i])
      );
    end
  endgenerate



endmodule
