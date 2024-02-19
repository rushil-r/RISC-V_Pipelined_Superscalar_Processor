/* INSERT NAME AND PENNKEY HERE 
Rushil Roy (rushilr)
Ahmed Abdellah (abdellah)
*/

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned (
    input  wire [31:0] i_dividend,
    input  wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);
  // TODO: your code here
  wire [31:0] store_dividend [33];
  wire [31:0] store_quotient [33];
  wire [31:0] store_remainder[33];
  assign store_dividend[0]  = i_dividend;
  assign store_quotient[0]  = 32'h0000_0000;
  assign store_remainder[0] = 32'h0000_0000;
  genvar i;
  generate
    for (i = 0; i < 32; i = i + 1) begin : div_iteration
      divu_1iter div_mod (
          .i_dividend (store_dividend[i]),
          .i_divisor  (i_divisor),
          .i_remainder(store_remainder[i]),
          .i_quotient (store_quotient[i]),
          .o_dividend (store_dividend[i+1]),
          .o_remainder(store_remainder[i+1]),
          .o_quotient (store_quotient[i+1])
      );
    end
  endgenerate
  assign o_remainder = store_remainder[32];
  assign o_quotient  = store_quotient[32];
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
  wire [31:0] intermediate;
  wire [ 0:0] less_than;

  assign intermediate = (i_remainder << 1) | ((i_dividend >> 31) & 32'h0000_0001);
  assign less_than = intermediate < i_divisor;
  assign o_remainder = less_than ? intermediate : (intermediate - i_divisor);
  assign o_quotient = less_than ? (i_quotient << 1) : ((i_quotient << 1) | 32'h0000_0001);
  assign o_dividend = i_dividend << 1;

endmodule
