/* INSERT NAME AND PENNKEY HERE
Rushil Roy (rushilr)
Ahmed Abdellah (abdellah)
*/
`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`include "../hw2a/divider_unsigned.sv"
`include "../hw2b/cla.sv"

module RegFile (
    input logic [4:0] rd,
    input logic [`REG_SIZE] rd_data,
    input logic [4:0] rs1,
    output logic [`REG_SIZE] rs1_data,
    input logic [4:0] rs2,
    output logic [`REG_SIZE] rs2_data,

    input logic clk,
    input logic we,
    input logic rst
);
  localparam int NumRegs = 32;
  logic [`REG_SIZE] regs[NumRegs];
  // TODO: your code here
  assign regs[0]  = 32'd0;
  assign rs1_data = regs[rs1];
  assign rs2_data = regs[rs2];
  always_ff @(posedge clk) begin
    if (rst) begin
      regs[1] <= 32'd0;
    end else begin
      if (we && rd == 1) begin
        regs[1] <= rd_data;
      end
    end
  end
  genvar i;
  for (i = 2; i < 32; i = i + 1) begin : gen_other_regs
    always_ff @(posedge clk) begin
      if (rst) begin
        regs[i] <= 32'd0;
      end else begin
        if (we && rd == i) begin
          regs[i] <= rd_data;
        end
      end
    end
  end
endmodule


module DatapathSingleCycle (
    input wire clk,
    input wire rst,
    output logic halt,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`REG_SIZE] insn_from_imem,
    // addr_to_dmem is a read-write port
    output wire [`REG_SIZE] addr_to_dmem,
    input logic [`REG_SIZE] load_data_from_dmem,
    output wire [`REG_SIZE] store_data_to_dmem,
    output wire [3:0] store_we_to_dmem
);

  logic [0:0] regfile_we;
  logic [`REG_SIZE] data_rd;
  logic [`REG_SIZE] data_rs1;
  logic [`REG_SIZE] data_rs2;
  logic [4:0] regfile_rd;
  logic [4:0] regfile_rs1;
  logic [4:0] regfile_rs2;

  // components of the instruction
  wire [6:0] insn_funct7;
  wire [4:0] insn_rs2;
  wire [4:0] insn_rs1;
  wire [2:0] insn_funct3;
  wire [4:0] insn_rd;
  wire [`OPCODE_SIZE] insn_opcode;
  // split R-type instruction - see section 2.2 of RiscV spec
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = insn_from_imem;

  // setup for I, S, B & J type instructions
  // I - short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = insn_from_imem[31:20];
  wire [ 4:0] imm_shamt = insn_from_imem[24:20];

  // S - stores
  wire [11:0] imm_s;
  assign imm_s[11:5] = insn_funct7, imm_s[4:0] = insn_rd;

  // B - conditionals
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:5]} = insn_funct7, {imm_b[4:1], imm_b[11]} = insn_rd, imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {
    insn_from_imem[31:12], 1'b0
  };

  // U - 20-bit immediate
  wire [19:0] imm_u;
  assign imm_u = insn_from_imem[31:12];


  wire [`REG_SIZE] imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  wire [`REG_SIZE] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  wire [`REG_SIZE] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  wire [`REG_SIZE] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};
  wire [`REG_SIZE] imm_u_sext = {{12{imm_u[19]}}, imm_u[19:0]};
  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpLui = 7'b01_101_11;

  wire insn_lui = insn_opcode == OpLui;
  wire insn_auipc = insn_opcode == OpAuipc;
  wire insn_jal = insn_opcode == OpJal;
  wire insn_jalr = insn_opcode == OpJalr;

  wire insn_beq = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b000;
  wire insn_bne = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b001;
  wire insn_blt = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b100;
  wire insn_bge = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b101;
  wire insn_bltu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b110;
  wire insn_bgeu = insn_opcode == OpBranch && insn_from_imem[14:12] == 3'b111;

  wire insn_lb = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b000;
  wire insn_lh = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b001;
  wire insn_lw = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b010;
  wire insn_lbu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b100;
  wire insn_lhu = insn_opcode == OpLoad && insn_from_imem[14:12] == 3'b101;

  wire insn_sb = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b000;
  wire insn_sh = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b001;
  wire insn_sw = insn_opcode == OpStore && insn_from_imem[14:12] == 3'b010;

  wire insn_addi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b000;
  wire insn_slti = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b010;
  wire insn_sltiu = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b011;
  wire insn_xori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b100;
  wire insn_ori = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b110;
  wire insn_andi = insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b111;

  wire insn_slli = (insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b001
     && insn_from_imem[31:25] == 7'd0);
  wire insn_srli = (insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101
     && insn_from_imem[31:25] == 7'd0);
  wire insn_srai = (insn_opcode == OpRegImm && insn_from_imem[14:12] == 3'b101
     && insn_from_imem[31:25] == 7'b0100000);

  wire insn_add = (insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000
     && insn_from_imem[31:25] == 7'd0);
  wire insn_sub = (insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b000
     && insn_from_imem[31:25] == 7'b0100000);
  wire insn_sll = (insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b001
     && insn_from_imem[31:25] == 7'd0);
  wire insn_slt = (insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b010
     && insn_from_imem[31:25] == 7'd0);
  wire insn_sltu = (insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b011
     && insn_from_imem[31:25] == 7'd0);
  wire insn_xor = (insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b100
     && insn_from_imem[31:25] == 7'd0);
  wire insn_srl = (insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101
     && insn_from_imem[31:25] == 7'd0);
  wire insn_sra  = (insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b101
     && insn_from_imem[31:25] == 7'b0100000);
  wire insn_or = (insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b110
     && insn_from_imem[31:25] == 7'd0);
  wire insn_and = (insn_opcode == OpRegReg && insn_from_imem[14:12] == 3'b111
     && insn_from_imem[31:25] == 7'd0);

  wire insn_mul    = (insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1
     && insn_from_imem[14:12] == 3'b000);
  wire insn_mulh   = (insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1
     && insn_from_imem[14:12] == 3'b001);
  wire insn_mulhsu = (insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1
     && insn_from_imem[14:12] == 3'b010);
  wire insn_mulhu  = (insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1
     && insn_from_imem[14:12] == 3'b011);
  wire insn_div    = (insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1
     && insn_from_imem[14:12] == 3'b100);
  wire insn_divu   = (insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1
     && insn_from_imem[14:12] == 3'b101);
  wire insn_rem    = (insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1
     && insn_from_imem[14:12] == 3'b110);
  wire insn_remu   = (insn_opcode == OpRegReg && insn_from_imem[31:25] == 7'd1
     && insn_from_imem[14:12] == 3'b111);

  wire insn_ecall = insn_opcode == OpEnviron && insn_from_imem[31:7] == 25'd0;
  wire insn_fence = insn_opcode == OpMiscMem;

  // synthesis translate_off
  // this code is only for simulation, not synthesis
  `include "RvDisassembler.sv"
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn_from_imem);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic...
  wire [(8*32)-1:0] disasm_wire;
  genvar i;
  for (i = 0; i < 32; i = i + 1) begin : gen_disasm
    assign disasm_wire[(((i+1))*8)-1:((i)*8)] = disasm_string[31-i];
  end
  // synthesis translate_on

  // program counter
  logic [`REG_SIZE] pcNext, pcCurrent;
  always @(posedge clk) begin
    if (rst) begin
      pcCurrent <= 32'd0;
    end else begin
      pcCurrent <= pcNext;
    end
  end
  assign pc_to_imem = pcCurrent;

  // cycle/insn_from_imem counters
  logic [`REG_SIZE] cycles_current, num_insns_current;
  always @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
      num_insns_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
      if (!rst) begin
        num_insns_current <= num_insns_current + 1;
      end
    end
  end
  logic [31:0] temp_add; 
  logic illegal_insn;
  wire [31:0] cla_sum;
  wire [31:0] cla_sum_reg;
  wire [31:0] cla_diff_reg;
  wire [31:0] div_u_rem_reg;
  wire [31:0] div_u_qot_reg;
  wire [31:0] div_rem_reg;
  wire [31:0] div_qot_reg;
  wire [31:0] div_rem_reg_bn;
  wire [31:0] div_qot_reg_bn;
  logic [3:0] store_we_to_dmem_temp;
  logic [31:0] store_data_to_dmem_temp;
  //assign branch_tgt = pcCurrent + {{19{imm_b[11]}}, (imm_b)};
  assign store_we_to_dmem = store_we_to_dmem_temp;
  assign store_data_to_dmem = store_data_to_dmem_temp;
  assign addr_to_dmem = {temp_add[31:2], 2'd0};
  RegFile rf (
      .rd(insn_rd),
      .rd_data(data_rd),
      .rs1(insn_rs1),
      .rs1_data(data_rs1),
      .rs2(insn_rs2),
      .rs2_data(data_rs2),
      .clk(clk),
      .we(regfile_we),
      .rst(rst)
  );

  cla cla_ops (
      .a  (data_rs1),
      .b  (imm_i_sext),
      .cin(1'b0),
      .sum(cla_sum)
  );
  cla cla_reg_add (
      .a  (data_rs1),
      .b  (data_rs2),
      .cin(1'b0),
      .sum(cla_sum_reg)
  );
  cla cla_reg_sub (
      .a  (data_rs1),
      .b  ((~data_rs2) + 1'b1),
      .cin(1'b0),
      .sum(cla_diff_reg)
  );
  divider_unsigned div_u_alu (
      .i_dividend (data_rs1),
      .i_divisor  (data_rs2),
      .o_remainder(div_u_rem_reg),
      .o_quotient (div_u_qot_reg)
  );

  divider_unsigned div_sr_alu_n (
      .i_dividend ((({32{data_rs1[31]}} ^ data_rs1) + {31'b0, data_rs1[31]})),
      .i_divisor  ((({32{data_rs2[31]}} ^ data_rs2) + {31'b0, data_rs2[31]})),
      .o_remainder(div_rem_reg),
      .o_quotient (div_qot_reg)
  );

  always_comb begin
    halt = 1'b0;
    // set as default, but make sure to change if illegal/default-case/failure
    illegal_insn = 1'b0;
    regfile_we = 1'b0;
    pcNext = pcCurrent + 4;
    temp_add = 32'd0;
    store_data_to_dmem_temp = 32'd0;
    store_we_to_dmem_temp = 4'd0;

    case (insn_opcode)
      OpLui: begin
        regfile_we = 1'b1;
        data_rd = {{imm_u[19:0]}, 12'b0};  // 20-bit bitshifted left by 12
      end
      OpAuipc: begin
        regfile_we = 1'b1;
        data_rd = pcCurrent + {{imm_u[19:0]}, 12'b0};  // 20-bit bitshifted left by 12
      end
      OpRegImm: begin
        regfile_we = 1'b1;  //re-enable regfile when changing data_rd
        case (insn_from_imem[14:12])
          3'b000: begin
            //addi
            data_rd = cla_ops.sum;
          end
          3'b001: begin
            //slli
            data_rd = data_rs1 << imm_shamt;  //imm_shamt for shift_amount
          end
          3'b010: begin
            //slti
            data_rd = ($signed(data_rs1) < $signed(imm_i_sext)) ? 1 : 0;
          end
          3'b011: begin
            //stliu
            data_rd = data_rs1 < imm_i_sext ? 1 : 0;
          end
          3'b100: begin
            //xori
            data_rd = data_rs1 ^ imm_i_sext;
          end
          3'b101: begin
            if (insn_from_imem[31:25] == 7'd0) begin
              //srli
              data_rd = data_rs1 >> imm_shamt;
            end else begin
              //srai
              data_rd = $signed(data_rs1) >>> imm_shamt;
            end
          end
          3'b110: begin
            //ori
            data_rd = data_rs1 | imm_i_sext;
          end
          3'b111: begin
            //andi
            data_rd = data_rs1 & imm_i_sext;
          end
          default: begin
            regfile_we   = 1'b0;
            illegal_insn = 1'b1;
          end
        endcase
      end
      OpBranch: begin
        regfile_we = 1'b0;
        // formula for SEXT(targ12<<1) = {{19{imm_b[11]}}, (imm_b<<1)}
        case (insn_from_imem[14:12])
          3'b000: begin
            //beq
            if (data_rs1 == data_rs2) begin
              pcNext = pcCurrent + imm_b_sext;
            end
          end
          3'b001: begin
            //bne
            if (data_rs1 != data_rs2) begin
              pcNext = pcCurrent + imm_b_sext;
            end
          end
          3'b100: begin
            if ($signed(data_rs1) < $signed(data_rs2)) begin
              pcNext = pcCurrent + imm_b_sext;
            end
          end
          3'b101: begin
            //bge
            if ($signed(data_rs1) >= $signed(data_rs2)) begin
              pcNext = pcCurrent + imm_b_sext;
            end
          end
          3'b110: begin
            //bltu
            if (data_rs1 < data_rs2) begin
              pcNext = pcCurrent + imm_b_sext;
            end
          end
          3'b111: begin
            //bgeu
            if (data_rs1 >= data_rs2) begin
              pcNext = pcCurrent + imm_b_sext;
            end
          end
          default: begin
            illegal_insn = 1'b1;
            regfile_we   = 1'b0;
          end
        endcase
      end
      OpRegReg: begin
        regfile_we = 1'b1;
        case (insn_from_imem[14:12])
          3'b000: begin
            if (insn_from_imem[31:25] == 7'd0) begin
              //add
              data_rd = cla_reg_add.sum;
            end else if (insn_from_imem[31:25] == 7'b0100000) begin
              //sub
              data_rd = cla_reg_sub.sum;
            end else if (insn_from_imem[31:25] == 7'b0000001) begin
              //mul
              data_rd = (data_rs1 * data_rs2) & 32'h00000000ffffffff;
            end
          end
          3'b001: begin
            if (insn_from_imem[31:25] == 7'd0) begin
              //sll
              data_rd = data_rs1 << (data_rs2[4:0]);
            end else if (insn_from_imem[31:25] == 7'b0000001) begin
              //mulh
              logic [63:0] inter_mulh;
              inter_mulh = ($signed(data_rs1) * $signed(data_rs2));
              data_rd = inter_mulh[63:32];
            end
          end
          3'b010: begin
            if (insn_from_imem[31:25] == 7'd0) begin
              //slt
              data_rd = $signed(data_rs1) < $signed(data_rs2) ? 1 : 0;
            end else if (insn_from_imem[31:25] == 7'b0000001) begin
              //mulhsu
              logic [63:0] inter_mulhsu;
              inter_mulhsu = ($signed(data_rs1) * $unsigned(data_rs2));
              data_rd = inter_mulhsu[63:32];
            end
          end
          3'b011: begin
            if (insn_from_imem[31:25] == 7'd0) begin
              //sltu
              data_rd = data_rs1 < data_rs2 ? 1 : 0;
            end else if (insn_from_imem[31:25] == 7'b0000001) begin
              //mulhu
              logic [63:0] inter_mulhu;
              inter_mulhu = ($unsigned(data_rs1) * $unsigned(data_rs2));
              data_rd = inter_mulhu[63:32];
            end
          end
          3'b100: begin
            if (insn_from_imem[31:25] == 7'd0) begin
              //xor
              data_rd = data_rs1 ^ data_rs2;
            end else if (insn_from_imem[31:25] == 7'b0000001) begin
              //div
              if (data_rs1[31] != data_rs2[31]) begin
                data_rd = ((~div_qot_reg)+(1'b1*(|(~div_qot_reg)))+(&div_qot_reg * ({32{1'b1}})));
                //(((~div_qot_reg) | ({{31{&div_qot_reg}}, 1'b0})) + 1'b1);
              end else begin
                data_rd = div_qot_reg;  // case falls here (should be 3)
              end
            end
          end
          3'b101: begin
            if (insn_from_imem[31:25] == 7'd0) begin
              //srl
              data_rd = data_rs1 >> (data_rs2[4:0]);
            end else if (insn_from_imem[31:25] == 7'b0100000) begin
              //sra
              data_rd = $signed(data_rs1) >>> $signed(data_rs2[4:0]);
            end else if (insn_from_imem[31:25] == 7'b0000001) begin
              //divu
              data_rd = div_u_qot_reg;
            end
          end
          3'b110: begin
            if (insn_from_imem[31:25] == 7'd0) begin
              //or
              data_rd = data_rs1 | data_rs2;
            end else if (insn_from_imem[31:25] == 7'b0000001) begin
              //rem
              if (data_rs1[31]) begin
                data_rd = ((~div_rem_reg) + 1'b1);
              end else begin
                data_rd = div_rem_reg;
              end
            end
          end
          3'b111: begin
            if (insn_from_imem[31:25] == 7'd0) begin
              //and
              data_rd = data_rs1 & data_rs2;
            end else if (insn_from_imem[31:25] == 7'b0000001) begin
              //remu
              data_rd = div_u_rem_reg;
            end
          end
          default: begin
            illegal_insn = 1'b1;
            regfile_we   = 1'b0;
          end
        endcase
      end
      OpEnviron: begin
        regfile_we = 1'b0;
        case (insn_from_imem[31:7])
          25'd0: begin
            halt = 1'b1;
          end
          default: begin
            illegal_insn = 1'b1;
            regfile_we   = 1'b0;
          end
        endcase
      end
      OpJal: begin
        regfile_we = 1'b1;
        data_rd = pcCurrent + 4;
        pcNext = pcCurrent + imm_j_sext;
      end
      OpJalr: begin
        regfile_we = 1'b1;
        data_rd = pcCurrent + 4;
        pcNext = ((data_rs1 + imm_i_sext) & (32'b11111111111111111111111111111110));
      end
      OpLoad: begin
        regfile_we = 1'b1;
        case (insn_from_imem[14:12])
          3'b000: begin
            // lb loads an 8-bit value from mem, SEXT to 32 bits, then stores in rd
            temp_add = data_rs1 + imm_i_sext;
            // Ensure addres is aligned 
            case (temp_add[1:0])
              2'b00:
              // aligned so we grab the first byte 
              data_rd = {
                {24{load_data_from_dmem[7]}}, load_data_from_dmem[7:0]
              };
              2'b01:
              // mod 1 -> grab the second byte 
              data_rd = {
                {24{load_data_from_dmem[15]}}, load_data_from_dmem[15:8]
              };
              2'b10:
              // mod 2 -> grab the third byte 
              data_rd = {
                {24{load_data_from_dmem[23]}}, load_data_from_dmem[23:16]
              };
              2'b11:
              // mod 3 -> grab the 4th byte 
              data_rd = {
                {24{load_data_from_dmem[31]}}, load_data_from_dmem[31:24]
              };
              default: begin
                illegal_insn = 1'b1;
                regfile_we   = 1'b0;
              end
            endcase
          end
          3'b001: begin
            // lh loads a 16-bit value from mem, SEXT to 32-bits, then stores in rd
            temp_add = data_rs1 + imm_i_sext;
             // Align to the nearest lower half-word boundary

            // Assuming memory access returns a 32-bit word
            case (temp_add[1:0])
              2'b00: begin
                // Aligned access so we grab the first 16 bits
                data_rd = {{16{load_data_from_dmem[15]}}, load_data_from_dmem[15:0]};
              end
              2'b10: begin
                // Unaligned access, half-word crosses 32-bit word boundary
                // Grab the second 16 bits 
                data_rd = {{16{load_data_from_dmem[31]}}, load_data_from_dmem[31:16]};
              end
              default: begin
                illegal_insn = 1'b1;
                regfile_we   = 1'b0;
              end

            endcase
          end
          3'b010: begin
            // lw loads a 32-bit value from memory into rd
            // Calculate memory address to load from
            temp_add = data_rs1 + imm_i_sext;
            data_rd = load_data_from_dmem;  // Data loaded from memory
          end
          3'b100: begin
            // lbu loads an 8-bit value from mem, zext to 32 bits, then stores in rd
            temp_add = data_rs1 + imm_i_sext;

            // Sign-extend based on the lowest 2 bits of the address
            case (temp_add[1:0])
              2'b00: data_rd = {24'd0, load_data_from_dmem[7:0]};  //mul of 4 (mod 0)
              2'b01: data_rd = {24'd0, load_data_from_dmem[15:8]};  //mod 1 
              2'b10: data_rd = {24'd0, load_data_from_dmem[23:16]};  // mod 2
              2'b11: data_rd = {24'd0, load_data_from_dmem[31:24]};  // mod 3 
              default: begin
                regfile_we   = 1'b0;
                illegal_insn = 1'b1;
              end
            endcase
          end
          3'b101: begin
            // lhu loads a 16-bit value from mem, 0-fills to 32-bits, then stores in rd
            temp_add = data_rs1 + imm_i_sext;
            // Assuming memory access returns a 32-bit word
            case (temp_add[1:0])
              2'b00: begin
                // Aligned access
                data_rd = {16'd0, load_data_from_dmem[15:0]};
              end
              2'b10: begin
                // Unaligned access, half-word crosses 32-bit word boundary
                // Grab the second 16 bits 
                data_rd = {16'd0, load_data_from_dmem[31:16]};
              end
              default: begin
                illegal_insn = 1'b1;
                regfile_we   = 1'b0;
              end
            endcase
          end
          default: begin
            illegal_insn = 1'b1;
            regfile_we   = 1'b0;
          end
        endcase
      end
      OpStore: begin
        regfile_we = 1'b1;
        case (insn_from_imem[14:12])
          3'b000: begin
            // store byte
            temp_add = data_rs1 + imm_i_sext;
            case (temp_add[1:0])
              2'b00: begin
                //aligned --> grab first byte
                store_we_to_dmem_temp  = 4'b0001;
                store_data_to_dmem_temp = data_rs2;
                // store_data_to_dmem[7:0] = data_rs2[7:0];
              end
              2'b01: begin
                // store second byte 
                store_we_to_dmem_temp   = 4'b0010;
                store_data_to_dmem_temp = {16'd0, data_rs2[7:0], 8'd0};
                // store_data_to_dmem[15:8] = data_rs2[7:0];
              end
              2'b10: begin
                // store third byte 
                store_we_to_dmem_temp   = 4'b0100;
                store_data_to_dmem_temp = {8'd0, data_rs2[7:0], 16'd0};
                // store_data_to_dmem[23:16] = data_rs2[7:0];
              end
              2'b11: begin
                // store fourth byte 
                store_we_to_dmem_temp   = 4'b1000;
                store_data_to_dmem_temp = {data_rs2[7:0], 24'd0};
                // store_data_to_dmem[31:24] = data_rs2[7:0];
              end
              default: begin
                regfile_we   = 1'b0;
                illegal_insn = 1'b1;
              end
            endcase

          end
          3'b001: begin
            // store half word
            temp_add = data_rs1 + imm_i_sext;
            case (temp_add[1:0])
              2'b00: begin
                //aligned --> grab first half-word
                store_we_to_dmem_temp   = 4'b0011;
                store_data_to_dmem_temp = data_rs2;
                // store_data_to_dmem[15:0] = data_rs2[15:0];
              end
              2'b10: begin
                // store second half-word
                store_we_to_dmem_temp   = 4'b1100;
                store_data_to_dmem_temp = {data_rs2[15:0],16'd0};
                // store_data_to_dmem[31:16] = data_rs2[15:0];
              end
              default: begin
                regfile_we   = 1'b0;
                illegal_insn = 1'b1;
              end
            endcase
          end
          3'b010: begin
            //store word
            temp_add = data_rs1 + imm_i_sext;
            store_we_to_dmem_temp = 4'b1111;
            store_data_to_dmem_temp = data_rs2;
          end
          default: begin
            illegal_insn = 1'b1;
            regfile_we   = 1'b0;
          end
        endcase
      end
      default: begin
        regfile_we   = 1'b0;
        illegal_insn = 1'b1;
      end
    endcase
    // pcNext = pcCurrent+4
    //^^^^^ relocated to inside case statements to allow for branching logic
  end
endmodule

/* A memory module that supports 1-cycle reads and writes, with one read-only port
* and one read+write port.
*/
module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. See RiscvProcessor for clock details.
    input wire clock_mem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] pc_to_imem,

    // the value at memory location pc_to_imem
    output logic [`REG_SIZE] insn_from_imem,

    // must always be aligned to a 4B boundary
    input wire [`REG_SIZE] addr_to_dmem,

    // the value at memory location addr_to_dmem
    output logic [`REG_SIZE] load_data_from_dmem,

    // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
    input wire [`REG_SIZE] store_data_to_dmem,

    // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
    // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
    input wire [3:0] store_we_to_dmem
);

  // memory is arranged as an array of 4B words
  logic [`REG_SIZE] mem[NUM_WORDS];

  initial begin
    $readmemh("mem_initial_contents.hex", mem, 0);
  end

  always_comb begin
    // memory addresses should always be 4B-aligned
    assert (pc_to_imem[1:0] == 2'b00);
    assert (addr_to_dmem[1:0] == 2'b00);
  end

  localparam int AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam int AddrLsb = 2;

  always @(posedge clock_mem) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clock_mem) begin
    if (rst) begin
    end else begin
      if (store_we_to_dmem[0]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
      end
      if (store_we_to_dmem[1]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
      end
      if (store_we_to_dmem[2]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
      end
      if (store_we_to_dmem[3]) begin
        mem[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
      end
      // dmem is "read-first": read returns value before the write
      load_data_from_dmem <= mem[{addr_to_dmem[AddrMsb:AddrLsb]}];
    end
  end
endmodule

/*
This shows the relationship between clock_proc and clock_mem. The clock_mem is
phase-shifted 90° from clock_proc. You could think of one proc cycle being
broken down into 3 parts. During part 1 (which starts @posedge clock_proc)
the current PC is sent to the imem. In part 2 (starting @posedge clock_mem) we
read from imem. In part 3 (starting @negedge clock_mem) we read/write memory and
prepare register/PC updates, which occur at @posedge clock_proc.

    ____
proc: |    |______
        ____
mem:  ___|    |___
*/
module RiscvProcessor (
    input  wire  clock_proc,
    input  wire  clock_mem,
    input  wire  rst,
    output logic halt
);

  wire [`REG_SIZE] pc_to_imem, insn_from_imem, mem_data_addr,
     mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) mem (
      .rst                (rst),
      .clock_mem          (clock_mem),
      // imem is read-only
      .pc_to_imem         (pc_to_imem),
      .insn_from_imem     (insn_from_imem),
      // dmem is read-write
      .addr_to_dmem       (mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem   (mem_data_we)
  );

  DatapathSingleCycle datapath (
      .clk(clock_proc),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt)
  );
endmodule
