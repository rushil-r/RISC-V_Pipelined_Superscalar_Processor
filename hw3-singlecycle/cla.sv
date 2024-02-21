`timescale 1ns / 1ps
// Authors: Ahmed Abdellah, Rushil Roy 
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
  assign gout = (gin[0] & pin[1] & pin[2] & pin[3])  | (gin[1] & pin[2] & pin[3]) | (gin[2] & pin[3]) | gin[3];

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

  // carry out temp vars
  wire inter1, inter2, inter3, inter4, inter5, inter6, inter7;

  // Assign intermeidate values before cout 
  assign inter1 = gin[0] | (pin[0] & cin);
  assign inter2 = gin[1] | (pin[1] & inter1);
  assign inter3 = gin[2] | (pin[2] & inter2);
  assign inter4 = gin[3] | (pin[3] & inter3);
  assign inter5 = gin[4] | (pin[4] & inter4);
  assign inter6 = gin[5] | (pin[5] & inter5);
  assign inter7 = gin[6] | (pin[6] & inter6);

  // Assign cout according to intermediate 
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
  assign gout = (gin[0] & pin[1] & pin[2] & pin[3] & pin[4] & pin[5] & pin[6] & pin[7])  | (gin[1] & pin[2] & pin[3] & pin[4] & pin[5] & pin[6] & pin[7]) |
    (gin[2]  & pin[3] & pin[4] & pin[5] & pin[6] & pin[7]) | 
    (gin[3] & pin[4] & pin[5] & pin[6] & pin[7]) | 
    (gin[4] & pin[5] & pin[6] & pin[7]) | 
    (gin[5] &  pin[6] & pin[7]) | 
    (gin[6] & pin[7]) | gin[7];
endmodule

module cla (
    input  wire [31:0] a,
    b,
    input  wire        cin,
    output wire [31:0] sum
);

  wire [31:0] c_fin, p_temp, g_temp;  // make final buses 
  //make firtt ctemp bit the current cin value  (c0)
  assign c_fin[0] = cin;

  //use genvar to make 32 gp1 for first carryout output 
  genvar gp1_create;
  generate
    for (gp1_create = 0; gp1_create < 32; gp1_create = gp1_create + 1)
    gp1 gp1_instantiate (
        a[gp1_create],
        b[gp1_create],
        g_temp[gp1_create],
        p_temp[gp1_create]
    );
  endgenerate

  //array for routing the proper cout_outputs into the right gp4 (curr + 4 NOT INCLUSIVE)
  parameter int c_routing[8] = '{1, 5, 9, 13, 17, 21, 25, 29};
  //wires for storing prop and gen signals 
  wire [7:0] g4, p4;
  genvar gp4_iter;

  generate
    for (gp4_iter = 0; gp4_iter < 8; gp4_iter = gp4_iter + 1)
    gp4 gp4_instantiate (
        g_temp[4*gp4_iter+:4],  //starting index + next 4 bits 
        p_temp[4*gp4_iter+:4],
        c_fin[4*gp4_iter],
        g4[gp4_iter],
        p4[gp4_iter],
        c_fin[c_routing[gp4_iter]+:3]  // starting index + next 3 bits to make next index not inclusive of next cout 
    );
  endgenerate


  // now make our single g8 
  wire g8, p8;
  wire [6:0] c_inter;  //hold our interemdaite values 
  gp8 gp8_inst (
      g4,
      p4,
      c_fin[0],
      g8,
      p8,
      c_inter
  );

  // assign final c values from our intermediates 
  assign c_fin[4]  = c_inter[0];
  assign c_fin[8]  = c_inter[1];
  assign c_fin[12] = c_inter[2];
  assign c_fin[16] = c_inter[3];
  assign c_fin[20] = c_inter[4];
  assign c_fin[24] = c_inter[5];
  assign c_fin[28] = c_inter[6];

  // final sum XOR  
  genvar summation;
  generate
    for (summation = 0; summation < 32; summation++)
      assign sum[summation] = a[summation] ^ b[summation] ^ c_fin[summation];
  endgenerate

endmodule
