/* INSERT NAME AND PENNKEY HERE
Rushil Roy (rushilr)
Ahmed Abdellah (abdellah)
*/

`timescale 1ns / 1ns

// quotient = dividend / divisor

module divider_unsigned_pipelined (
    input wire clk,
    rst,
    input wire [31:0] i_dividend,
    input wire [31:0] i_divisor,
    output wire [31:0] o_remainder,
    output wire [31:0] o_quotient
);
  wire [31:0] store_divisor[33];
  wire [31:0] store_dividend[33];
  wire [31:0] store_quotient[33];
  wire [31:0] store_remainder[33];
  logic [31:0] dividend_new;
  logic [31:0] remainder_new;
  logic [31:0] quotient_new;
  logic [31:0] i_divisor_post_pipe;
  assign store_divisor[0]   = i_divisor;
  assign store_dividend[0]  = i_dividend;
  assign store_quotient[0]  = 32'h0000_0000;
  assign store_remainder[0] = 32'h0000_0000;
  genvar i;
  generate
    for (i = 0; i < 32; i = i + 1) begin : g_div_iteration
      if (i < 16) begin : g_reg_iter
        divu_1iter div_mod_a (
            .i_dividend (store_dividend[i]),
            .i_divisor  (i_divisor),
            .i_remainder(store_remainder[i]),
            .i_quotient (store_quotient[i]),
            .o_dividend (store_dividend[i+1]),
            .o_remainder(store_remainder[i+1]),
            .o_quotient (store_quotient[i+1])
        );
        if (i == 15) begin : g_prep_pipe
          always_ff @(posedge clk) begin : clock_check
            if (rst) begin : reset_case
              i_divisor_post_pipe <= 32'h0000_0000;
              dividend_new <= 32'h0000_0000;
              remainder_new <= 32'h0000_0000;
              quotient_new <= 32'h0000_0000;
            end else begin : pipe_case
              i_divisor_post_pipe <= i_divisor;
              dividend_new <= store_dividend[16];
              remainder_new <= store_remainder[16];
              quotient_new <= store_quotient[16];
            end
          end
        end
      end else if (i > 16) begin : g_post_pipe_iter
        divu_1iter div_mod_b (
            .i_dividend (store_dividend[i]),
            .i_divisor  (i_divisor_post_pipe),
            .i_remainder(store_remainder[i]),
            .i_quotient (store_quotient[i]),
            .o_dividend (store_dividend[i+1]),
            .o_remainder(store_remainder[i+1]),
            .o_quotient (store_quotient[i+1])
        );
      end else begin : g_pipe_iter
        //i == 16
        divu_1iter div_mod_16 (
            .i_dividend (dividend_new),
            .i_divisor  (i_divisor_post_pipe),
            .i_remainder(remainder_new),
            .i_quotient (quotient_new),
            .o_dividend (store_dividend[i+1]),
            .o_remainder(store_remainder[i+1]),
            .o_quotient (store_quotient[i+1])
        );
      end
    end
  endgenerate
  assign o_remainder = store_remainder[32];
  assign o_quotient  = store_quotient[32];
  // TODO: your code here

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

  wire [31:0] intermediate;
  wire [ 0:0] less_than;

  assign intermediate = (i_remainder << 1) | ((i_dividend >> 31) & 32'h0000_0001);
  assign less_than = intermediate < i_divisor;
  assign o_remainder = less_than ? intermediate : (intermediate - i_divisor);
  assign o_quotient = less_than ? (i_quotient << 1) : ((i_quotient << 1) | 32'h0000_0001);
  assign o_dividend = i_dividend << 1;


endmodule
