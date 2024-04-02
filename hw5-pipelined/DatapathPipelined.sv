`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31:0

// insns are 32 bits in RV32IM
`define INSN_SIZE 31:0

// RV opcodes are 7 bits
`define OPCODE_SIZE 6:0

`ifndef RISCV_FORMAL
`include "../hw2b/cla.sv"
`include "../hw3-singlecycle/RvDisassembler.sv"
`include "../hw4-multicycle/divider_unsigned_pipelined.sv"
`endif

module Disasm #(
    byte PREFIX = "D"
) (
    input wire [31:0] insn,
    output wire [(8*32)-1:0] disasm
);
  // synthesis translate_off
  // this code is only for simulation, not synthesis
  string disasm_string;
  always_comb begin
    disasm_string = rv_disasm(insn);
  end
  // HACK: get disasm_string to appear in GtkWave, which can apparently show only wire/logic. Also,
  // string needs to be reversed to render correctly.
  genvar i;
  for (i = 3; i < 32; i = i + 1) begin : gen_disasm
    assign disasm[((i+1-3)*8)-1-:8] = disasm_string[31-i];
  end
  assign disasm[255-:8] = PREFIX;
  assign disasm[247-:8] = ":";
  assign disasm[239-:8] = " ";
  // synthesis translate_on
endmodule

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
  genvar i;
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
/**
 * This enum is used to classify each cycle as it comes through the Writeback stage, identifying
 * if a valid insn is present or, if it is a stall cycle instead, the reason for the stall. The
 * enum values are mutually exclusive: only one should be set for any given cycle. These values
 * are compared against the trace-*.json files to ensure that the datapath is running with the
 * correct timing.
 *
 * You will need to set these values at various places within your pipeline, and propagate them
 * through the stages until they reach Writeback where they can be checked.
 */
typedef enum {
  /** invalid value, this should never appear after the initial reset sequence completes */
  CYCLE_INVALID = 0,
  /** a stall cycle that arose from the initial reset signal */
  CYCLE_RESET = 1,
  /** not a stall cycle, a valid insn is in Writeback */
  CYCLE_NO_STALL = 2,
  /** a stall cycle that arose from a taken branch/jump */
  CYCLE_TAKEN_BRANCH = 4,

  // the values below are only needed in HW5B

  /** a stall cycle that arose from a load-to-use stall */
  CYCLE_LOAD2USE = 8,
  /** a stall cycle that arose from a div/rem-to-use stall */
  CYCLE_DIV2USE  = 16,
  /** a stall cycle that arose from a fence.i insn */
  CYCLE_FENCEI   = 32
} cycle_status_e;

/** state at the start of Decode stage */
typedef struct packed {
  logic [`REG_SIZE] pc_d;
  logic [`INSN_SIZE] insn_d;
  cycle_status_e cycle_status_d;
} stage_decode_t;

typedef struct packed {
  logic [`REG_SIZE] pc_e;
  cycle_status_e cycle_status_ee;
  logic [`INSN_SIZE] insn_e;
  logic [`OPCODE_SIZE] insn_opcode_e;
  logic [4:0] insn_rd_e;
  logic [4:0] insn_rs1_e;
  logic [4:0] insn_rs2_e;
  logic [`REG_SIZE] data_rs1_e;
  logic [`REG_SIZE] data_rs2_e;
  logic [`REG_SIZE] imm_i_sext_e;
  logic [`REG_SIZE] imm_s_sext_e;
  logic [`REG_SIZE] imm_b_sext_e;
  logic [`REG_SIZE] imm_j_sext_e;
  logic [`REG_SIZE] imm_u_sext_e;
  logic [4:0] imm_shamt_e;
} stage_execute_t;

/** state at the start of Memory stage */
// stores: result of ALU, REMOVED : data to write (store insn), register for detinations, and flags indicating for mem_read and read_write
typedef struct packed {
  logic [31:0] alu_result_m;
  logic [`INSN_SIZE] insn_m;
  logic mem_read_m;
  logic mem_write_m;
  logic regfile_we_m;  //this is the write enable signal for the RF
  logic [4:0] rd_m;
  cycle_status_e cycle_status_m;
} stage_memory_t;

/** state at the start of Writeback stage */
// stores: result of ALU and destination register
typedef struct packed {
  logic [`REG_SIZE] alu_result_w;
  logic [`INSN_SIZE] insn_w;
  logic [4:0] rd_w;
  logic regfile_we_w;  //this is the write enable signal for the RF
  logic mem_read_w;  //tells us if we read from datamemory
  logic mem_write_w;  //tells us if we wrote to datamemory
  cycle_status_e cycle_status_w;
} stage_writeback_t;

module DatapathPipelined (
    input wire clk,
    input wire rst,
    output logic [`REG_SIZE] pc_to_imem,
    input wire [`INSN_SIZE] insn_from_imem,
    // dmem is read/write
    output logic [`REG_SIZE] addr_to_dmem,
    input wire [`REG_SIZE] load_data_from_dmem,
    output logic [`REG_SIZE] store_data_to_dmem,
    output logic [3:0] store_we_to_dmem,

    output logic halt,

    // The PC of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`REG_SIZE] trace_writeback_pc,
    // The bits of the insn currently in Writeback. 0 if not a valid insn.
    output logic [`INSN_SIZE] trace_writeback_insn,
    // The status of the insn (or stall) currently in Writeback. See cycle_status_e enum for valid values.
    output cycle_status_e trace_writeback_cycle_status
);


  // opcodes - see section 19 of RiscV spec
  localparam bit [`OPCODE_SIZE] OpcodeLoad = 7'b00_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeStore = 7'b01_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeBranch = 7'b11_000_11;
  localparam bit [`OPCODE_SIZE] OpcodeJalr = 7'b11_001_11;
  localparam bit [`OPCODE_SIZE] OpcodeMiscMem = 7'b00_011_11;
  localparam bit [`OPCODE_SIZE] OpcodeJal = 7'b11_011_11;

  localparam bit [`OPCODE_SIZE] OpcodeRegImm = 7'b00_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeRegReg = 7'b01_100_11;
  localparam bit [`OPCODE_SIZE] OpcodeEnviron = 7'b11_100_11;

  localparam bit [`OPCODE_SIZE] OpcodeAuipc = 7'b00_101_11;
  localparam bit [`OPCODE_SIZE] OpcodeLui = 7'b01_101_11;

  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
  logic [`REG_SIZE] cycles_current;
  always_ff @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
    end
  end

  /***************/
  /* FETCH STAGE */
  /***************/

  logic [`REG_SIZE] f_pc_current, f_pc_next;
  wire [`REG_SIZE] f_insn;
  cycle_status_e f_cycle_status;

  // program counter
  logic flag_div;
  always_ff @(posedge clk) begin
    if (rst) begin
      f_pc_current   <= 32'd0;
      // NB: use CYCLE_NO_STALL since this is the value that will persist after the last reset cycle
      f_cycle_status <= CYCLE_NO_STALL;
    end else begin
      f_cycle_status <= CYCLE_NO_STALL;
      f_pc_current   <= f_pc_current + 4;
    end
  end
  // send PC to imem
  assign pc_to_imem = f_pc_current;
  assign f_insn = insn_from_imem;

  // Here's how to disassemble an insn into a string you can view in GtkWave.
  // Use PREFIX to provide a 1-character tag to identify which stage the insn comes from.
  wire [255:0] f_disasm;
  Disasm #(
      .PREFIX("F")
  ) disasm_0fetch (
      .insn  (f_insn),
      .disasm(f_disasm)
  );

  /****************/
  /* DECODE STAGE */
  /****************/

  // this shows how to package up state in a `struct packed`, and how to pass it between stages
  // Sequental capture of the instruction & state
  stage_decode_t decode_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      decode_state <= '{pc_d: 0, insn_d: 0, cycle_status_d: CYCLE_RESET};
    end else begin
      begin
        decode_state <= '{pc_d: f_pc_current, insn_d: f_insn, cycle_status_d: f_cycle_status};
      end
    end
  end
  wire [255:0] d_disasm;
  Disasm #(
      .PREFIX("D")
  ) disasm_1decode (
      .insn  (decode_state.insn_d),
      .disasm(d_disasm)
  );

  // combinational logic
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
  assign {insn_funct7, insn_rs2, insn_rs1, insn_funct3, insn_rd, insn_opcode} = decode_state.insn_d;

  // setup for I, S, B & J type instructions

  // I - short immediates and loads
  wire [11:0] imm_i;
  assign imm_i = decode_state.insn_d[31:20];
  wire [ 4:0] imm_shamt = decode_state.insn_d[24:20];

  // S - stores
  wire [11:0] imm_s;
  assign imm_s[11:5] = insn_funct7, imm_s[4:0] = insn_rd;

  // B - conditionals
  wire [12:0] imm_b;
  assign {imm_b[12], imm_b[10:5]} = insn_funct7, {imm_b[4:1], imm_b[11]} = insn_rd, imm_b[0] = 1'b0;

  // J - unconditional jumps
  wire [20:0] imm_j;
  assign {imm_j[20], imm_j[10:1], imm_j[11], imm_j[19:12], imm_j[0]} = {
    decode_state.insn_d[31:12], 1'b0
  };

  // U - 20-bit immediate
  wire [19:0] imm_u;
  assign imm_u = decode_state.insn_d[31:12];

  wire [`REG_SIZE] imm_i_sext = {{20{imm_i[11]}}, imm_i[11:0]};
  wire [`REG_SIZE] imm_s_sext = {{20{imm_s[11]}}, imm_s[11:0]};
  wire [`REG_SIZE] imm_b_sext = {{19{imm_b[12]}}, imm_b[12:0]};
  wire [`REG_SIZE] imm_j_sext = {{11{imm_j[20]}}, imm_j[20:0]};
  wire [`REG_SIZE] imm_u_sext = {{12{imm_u[19]}}, imm_u[19:0]};

  wire insn_lui = insn_opcode == OpcodeLui;
  wire insn_auipc = insn_opcode == OpcodeAuipc;
  wire insn_jal = insn_opcode == OpcodeJal;
  wire insn_jalr = insn_opcode == OpcodeJalr;

  wire insn_beq = insn_opcode == OpcodeBranch && decode_state.insn_d[14:12] == 3'b000;
  wire insn_bne = insn_opcode == OpcodeBranch && decode_state.insn_d[14:12] == 3'b001;
  wire insn_blt = insn_opcode == OpcodeBranch && decode_state.insn_d[14:12] == 3'b100;
  wire insn_bge = insn_opcode == OpcodeBranch && decode_state.insn_d[14:12] == 3'b101;
  wire insn_bltu = insn_opcode == OpcodeBranch && decode_state.insn_d[14:12] == 3'b110;
  wire insn_bgeu = insn_opcode == OpcodeBranch && decode_state.insn_d[14:12] == 3'b111;

  wire insn_lb = insn_opcode == OpcodeLoad && decode_state.insn_d[14:12] == 3'b000;
  wire insn_lh = insn_opcode == OpcodeLoad && decode_state.insn_d[14:12] == 3'b001;
  wire insn_lw = insn_opcode == OpcodeLoad && decode_state.insn_d[14:12] == 3'b010;
  wire insn_lbu = insn_opcode == OpcodeLoad && decode_state.insn_d[14:12] == 3'b100;
  wire insn_lhu = insn_opcode == OpcodeLoad && decode_state.insn_d[14:12] == 3'b101;

  wire insn_sb = insn_opcode == OpcodeStore && decode_state.insn_d[14:12] == 3'b000;
  wire insn_sh = insn_opcode == OpcodeStore && decode_state.insn_d[14:12] == 3'b001;
  wire insn_sw = insn_opcode == OpcodeStore && decode_state.insn_d[14:12] == 3'b010;

  wire insn_addi = insn_opcode == OpcodeRegImm && decode_state.insn_d[14:12] == 3'b000;
  wire insn_slti = insn_opcode == OpcodeRegImm && decode_state.insn_d[14:12] == 3'b010;
  wire insn_sltiu = insn_opcode == OpcodeRegImm && decode_state.insn_d[14:12] == 3'b011;
  wire insn_xori = insn_opcode == OpcodeRegImm && decode_state.insn_d[14:12] == 3'b100;
  wire insn_ori = insn_opcode == OpcodeRegImm && decode_state.insn_d[14:12] == 3'b110;
  wire insn_andi = insn_opcode == OpcodeRegImm && decode_state.insn_d[14:12] == 3'b111;

  wire insn_slli = (insn_opcode == OpcodeRegImm && decode_state.insn_d[14:12] == 3'b001
     && decode_state.insn_d[31:25] == 7'd0);
  wire insn_srli = (insn_opcode == OpcodeRegImm && decode_state.insn_d[14:12] == 3'b101
     && decode_state.insn_d[31:25] == 7'd0);
  wire insn_srai = (insn_opcode == OpcodeRegImm && decode_state.insn_d[14:12] == 3'b101
     && decode_state.insn_d[31:25] == 7'b0100000);

  wire insn_add = (insn_opcode == OpcodeRegReg && decode_state.insn_d[14:12] == 3'b000
     && decode_state.insn_d[31:25] == 7'd0);
  wire insn_sub = (insn_opcode == OpcodeRegReg && decode_state.insn_d[14:12] == 3'b000
     && decode_state.insn_d[31:25] == 7'b0100000);
  wire insn_sll = (insn_opcode == OpcodeRegReg && decode_state.insn_d[14:12] == 3'b001
     && decode_state.insn_d[31:25] == 7'd0);
  wire insn_slt = (insn_opcode == OpcodeRegReg && decode_state.insn_d[14:12] == 3'b010
     && decode_state.insn_d[31:25] == 7'd0);
  wire insn_sltu = (insn_opcode == OpcodeRegReg && decode_state.insn_d[14:12] == 3'b011
     && decode_state.insn_d[31:25] == 7'd0);
  wire insn_xor = (insn_opcode == OpcodeRegReg && decode_state.insn_d[14:12] == 3'b100
     && decode_state.insn_d[31:25] == 7'd0);
  wire insn_srl = (insn_opcode == OpcodeRegReg && decode_state.insn_d[14:12] == 3'b101
     && decode_state.insn_d[31:25] == 7'd0);
  wire insn_sra  = (insn_opcode == OpcodeRegReg && decode_state.insn_d[14:12] == 3'b101
     && decode_state.insn_d[31:25] == 7'b0100000);
  wire insn_or = (insn_opcode == OpcodeRegReg && decode_state.insn_d[14:12] == 3'b110
     && decode_state.insn_d[31:25] == 7'd0);
  wire insn_and = (insn_opcode == OpcodeRegReg && decode_state.insn_d[14:12] == 3'b111
     && decode_state.insn_d[31:25] == 7'd0);

  wire insn_mul    = (insn_opcode == OpcodeRegReg && decode_state.insn_d[31:25] == 7'd1
     && decode_state.insn_d[14:12] == 3'b000);
  wire insn_mulh   = (insn_opcode == OpcodeRegReg && decode_state.insn_d[31:25] == 7'd1
     && decode_state.insn_d[14:12] == 3'b001);
  wire insn_mulhsu = (insn_opcode == OpcodeRegReg && decode_state.insn_d[31:25] == 7'd1
     && decode_state.insn_d[14:12] == 3'b010);
  wire insn_mulhu  = (insn_opcode == OpcodeRegReg && decode_state.insn_d[31:25] == 7'd1
     && decode_state.insn_d[14:12] == 3'b011);
  wire insn_div    = (insn_opcode == OpcodeRegReg && decode_state.insn_d[31:25] == 7'd1
     && decode_state.insn_d[14:12] == 3'b100);
  wire insn_divu   = (insn_opcode == OpcodeRegReg && decode_state.insn_d[31:25] == 7'd1
     && decode_state.insn_d[14:12] == 3'b101);
  wire insn_rem    = (insn_opcode == OpcodeRegReg && decode_state.insn_d[31:25] == 7'd1
     && decode_state.insn_d[14:12] == 3'b110);
  wire insn_remu   = (insn_opcode == OpcodeRegReg && decode_state.insn_d[31:25] == 7'd1
     && decode_state.insn_d[14:12] == 3'b111);

  wire insn_ecall = insn_opcode == OpcodeEnviron && decode_state.insn_d[31:7] == 25'd0;
  wire insn_fence = insn_opcode == OpcodeMiscMem;

  // TODO: your code here, though you will also need to modify some of the code above

  // USE STRUCT VALS TO ESTABLISH CONSTs
  // logic [0:0] regfile_we;
  // logic [`REG_SIZE] data_rd;
  // logic [`REG_SIZE] data_rs1;
  // logic [`REG_SIZE] data_rs2;
  // logic [4:0] regfile_rd;
  // logic [4:0] regfile_rs1;
  // logic [4:0] regfile_rs2;

  // components of the instruction

  // MIGHT NEED LATER
  // wire [6:0] insn_funct7;
  // wire [4:0] insn_rs2;
  // wire [4:0] insn_rs1;
  // wire [2:0] insn_funct3;
  // wire [4:0] insn_rd;
  // wire [`OPCODE_SIZE] insn_opcode;

  // TODO: the testbench requires that your register file instance is named `rf`
  /*******************/
  /*    EXECUTION    */
  /*******************/
  logic is_read_insn;
  logic is_write_insn;
  stage_execute_t execute_state;

  logic [31:0] data_rs1_e;
  logic [31:0] data_rs2_e;
  logic [31:0] data_rd_e;
  logic [4:0] rs1_e;
  logic [4:0] rs2_e;
  logic [4:0] rd_e;

  always_ff @(posedge clk) begin
    if (rst) begin
      execute_state <= '{
          pc_e: 0,
          cycle_status_ee: CYCLE_RESET,
          insn_e: 0,
          insn_opcode_e: 0,
          insn_rd_e: 0,
          insn_rs1_e: 0,
          insn_rs2_e: 0,
          data_rs1_e: 0,
          data_rs2_e: 0,
          imm_i_sext_e: 0,
          imm_s_sext_e: 0,
          imm_b_sext_e: 0,
          imm_j_sext_e: 0,
          imm_u_sext_e: 0,
          imm_shamt_e: 0
      };
    end else begin
      execute_state <= '{
          pc_e: decode_state.pc_d,
          cycle_status_ee: decode_state.cycle_status_d,
          insn_e: decode_state.insn_d,
          insn_opcode_e: insn_opcode,
          insn_rd_e: insn_rd,
          insn_rs1_e: insn_rs1,
          insn_rs2_e: insn_rs2,
          data_rs1_e: data_rs1,
          data_rs2_e: data_rs2,
          imm_i_sext_e: imm_i_sext,
          imm_s_sext_e: imm_s_sext,
          imm_b_sext_e: imm_b_sext,
          imm_j_sext_e: imm_j_sext,
          imm_u_sext_e: imm_u_sext,
          imm_shamt_e: imm_shamt
      };
    end
  end
  assign data_rs1_e = execute_state.data_rs1_e;
  assign data_rs2_e = execute_state.data_rs2_e;

  logic [31:0] temp_addr;
  logic [31:0] temp_load_casing;
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

  RegFile rf (
      .rd(writeback_state.rd_w),  //note: derived from decode_state.insn_d
      .rd_data(writeback_state.alu_result_w),
      .rs1(insn_rs1),  //note: derived from decode_state.insn_d
      .rs1_data(data_rs1),
      .rs2(insn_rs2),  //note: derived from decode_state.insn_d
      .rs2_data(data_rs2),
      .clk(clk),
      .we(writeback_state.regfile_we_w),  //note: derived from decode_state.insn_d
      .rst(rst)
  );

  logic [`REG_SIZE] cla_input_2;
  logic [`REG_SIZE] cla_input_1;

  always_comb begin
    if (writeback_state.rd_w == execute_state.insn_rs1_e) begin
      // wx bypassing rs1 input
      cla_input_1 = writeback_state.alu_result_w;
    end else if (memory_state.rd_m == execute_state.insn_rs1_e) begin
      // mx bypassing rs1 input
      cla_input_1 = memory_state.alu_result_m;
    end else begin
      cla_input_1 = data_rs1_e;
    end

    if (writeback_state.rd_w == execute_state.insn_rs2_e) begin
      // wx bypassing rs2 input
      cla_input_2 = writeback_state.alu_result_w;
    end else if (memory_state.rd_m == execute_state.insn_rs2_e) begin
      // mx bypassing rs2 input
      cla_input_2 = memory_state.alu_result_m;
    end else begin
      cla_input_2 = data_rs2_e;
    end
  end

  // TODO: Remove these extra CLA's and dividers
  cla cla_ops (
      .a  (data_rs1_e),
      .b  (execute_state.imm_i_sext_e),
      .cin(1'b0),
      .sum(cla_sum)
  );
  cla cla_reg_add (
      .a  (cla_input_1),
      .b  (cla_input_2),
      .cin(1'b0),
      .sum(cla_sum_reg)
  );
  cla cla_reg_sub (
      .a  (data_rs1_e),
      .b  ((~data_rs2_e) + 1'b1),
      .cin(1'b0),
      .sum(cla_diff_reg)
  );
  divider_unsigned_pipelined div_u_alu (
      .clk(clk),
      .rst(rst),
      .i_dividend(data_rs1_e),
      .i_divisor(data_rs2_e),
      .o_remainder(div_u_rem_reg),
      .o_quotient(div_u_qot_reg)
  );

  divider_unsigned_pipelined div_sr_alu_n (
      .clk(clk),
      .rst(rst),
      .i_dividend((({32{data_rs1_e[31]}} ^ data_rs1_e) + {31'b0, data_rs1_e[31]})),
      .i_divisor((({32{data_rs2_e[31]}} ^ data_rs2_e) + {31'b0, data_rs2_e[31]})),
      .o_remainder(div_rem_reg),
      .o_quotient(div_qot_reg)
  );


  wire [255:0] e_disasm;
  Disasm #(
      .PREFIX("E")
  ) disasm_2execute (
      .insn  (execute_state.insn_e),
      .disasm(e_disasm)
  );

  /*******************/
  /*    MEMORY     */
  /*******************/

  stage_memory_t memory_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      memory_state <= '{
          alu_result_m: 0,
          insn_m: 0,
          regfile_we_m: 0,
          mem_read_m: 0,
          mem_write_m: 0,
          cycle_status_m: CYCLE_RESET,
          rd_m: 0
      };
    end else begin
      memory_state <= '{
          alu_result_m: data_rd_e,
          insn_m: execute_state.insn_e,
          regfile_we_m: regfile_we,
          mem_read_m: is_read_insn,
          mem_write_m: is_write_insn,
          rd_m: execute_state.insn_rd_e,
          cycle_status_m: execute_state.cycle_status_ee
      };
    end
  end
  wire [255:0] m_disasm;
  Disasm #(
      .PREFIX("M")
  ) disasm_3memory (
      .insn  (memory_state.insn_m),
      .disasm(m_disasm)
  );

  /*******************/
  /*    WRITEBACK     */
  /*******************/
  stage_writeback_t writeback_state;
  always_ff @(posedge clk) begin
    if (rst) begin
      writeback_state <= '{
          alu_result_w: 0,
          insn_w: 0,
          mem_read_w: 0,
          mem_write_w: 0,
          cycle_status_w: CYCLE_RESET,
          rd_w: 0,
          regfile_we_w: 0
      };
    end else begin
      writeback_state <= '{
          alu_result_w: memory_state.alu_result_m,
          insn_w: memory_state.insn_m,
          mem_read_w: memory_state.mem_read_m,
          mem_write_w: memory_state.mem_write_m,
          cycle_status_w: memory_state.cycle_status_m,
          rd_w: memory_state.rd_m,
          regfile_we_w: memory_state.regfile_we_m
      };
    end
  end
  always_comb begin
    halt = 1'b0;
    // set as default, but make sure to change if illegal/default-case/failure
    illegal_insn = 1'b0;
    if (!((flag_div == 0) && (insn_div || insn_divu || insn_rem || insn_remu))) begin
      f_pc_next = f_pc_current + 4;
    end
    if (insn_lw || insn_lb || insn_lbu || insn_lh || insn_lhu) begin
      is_write_insn = 1;
    end else begin
      is_write_insn = 0;
    end
    if (insn_sw || insn_sb || insn_sh) begin
      is_read_insn = 1;
    end else begin
      is_read_insn = 0;
    end
    regfile_we = 1'b0;
    //f_pc_next = f_pc_current + 4;
    temp_addr = 'd0;
    addr_to_dmem = 'd0;
    store_we_to_dmem = 4'b0000;
    if (insn_ecall) begin
      // ecall
      halt = 1'b1;
    end
    if (execute_state.cycle_status_ee == CYCLE_RESET) begin
      data_rd_e = 0;
    end else begin
      case (execute_state.insn_opcode_e)
        OpcodeMiscMem: begin
          f_pc_next = ((f_pc_current + 4) & 32'b11111111111111111111111111111100);
          addr_to_dmem = (addr_to_dmem & 32'b11111111111111111111111111111100);
        end
        OpcodeLui: begin
          regfile_we = 1'b1;
          data_rd_e  = execute_state.imm_u_sext_e << 12;  // 20-bit bitshifted left by 12
        end
        OpcodeAuipc: begin
          regfile_we = 1'b1;
          data_rd_e  = execute_state.imm_u_sext_e;  // 20-bit bitshifted left by 12
        end
        OpcodeRegImm: begin
          case (execute_state.insn_e[14:12])
            3'b000: begin
              //addi
              data_rd_e = cla_sum;
            end
            3'b001: begin
              //slli
              data_rd_e = data_rs1_e << execute_state.imm_shamt_e;
            end
            3'b010: begin
              //slti
              data_rd_e = ($signed(data_rs1_e) < $signed(execute_state.imm_i_sext_e)) ? 1 : 0;
            end
            3'b011: begin
              //stliu
              data_rd_e = data_rs1_e < execute_state.imm_i_sext_e ? 1 : 0;
            end
            3'b100: begin
              //xori
              data_rd_e = data_rs1_e ^ execute_state.imm_i_sext_e;
            end
            3'b101: begin
              if (insn_from_imem[31:25] == 7'd0) begin
                //srli
                data_rd_e = data_rs1_e >> execute_state.imm_shamt_e;
              end else begin
                //srai
                data_rd_e = $signed(data_rs1_e) >>> execute_state.imm_shamt_e;
              end
            end
            3'b110: begin
              //ori
              data_rd_e = data_rs1_e | execute_state.imm_i_sext_e;
            end
            3'b111: begin
              //andi
              data_rd_e = data_rs1_e & execute_state.imm_i_sext_e;
            end
            default: begin
              regfile_we   = 1'b0;
              illegal_insn = 1'b1;
            end
          endcase
        end
        OpcodeBranch: begin
          regfile_we = 1'b0;
          // formula for SEXT(targ12<<1) = {{19{imm_b[11]}}, (imm_b<<1)}
          case (execute_state.insn_e[14:12])
            3'b000: begin
              //beq
              if (data_rs1_e == data_rs2_e) begin
                f_pc_next = f_pc_current + execute_state.imm_b_sext_e;
              end
            end
            3'b001: begin
              //bne
              if (data_rs1_e != data_rs2_e) begin
                f_pc_next = f_pc_current + execute_state.imm_b_sext_e;
              end
            end
            3'b100: begin
              if ($signed(data_rs1_e) < $signed(data_rs2_e)) begin
                f_pc_next = f_pc_current + execute_state.imm_b_sext_e;
              end
            end
            3'b101: begin
              //bge
              if ($signed(data_rs1_e) >= $signed(data_rs2_e)) begin
                f_pc_next = f_pc_current + execute_state.imm_b_sext_e;
              end
            end
            3'b110: begin
              //bltu
              if (data_rs1_e < data_rs2_e) begin
                f_pc_next = f_pc_current + execute_state.imm_b_sext_e;
              end
            end
            3'b111: begin
              //bgeu
              if (data_rs1_e >= data_rs2_e) begin
                f_pc_next = f_pc_current + execute_state.imm_b_sext_e;
              end
            end
            default: begin
              illegal_insn = 1'b1;
              regfile_we   = 1'b0;
            end
          endcase
        end
        OpcodeRegReg: begin
          case (execute_state.insn_e[14:12])
            3'b000: begin
              regfile_we = 1'b1;
              if (execute_state.insn_e[31:25] == 7'd0) begin
                //add
                data_rd_e = cla_reg_add.sum;
              end else if (insn_from_imem[31:25] == 7'b0100000) begin
                //sub
                data_rd_e = cla_reg_sub.sum;
              end else if (insn_from_imem[31:25] == 7'b0000001) begin
                //mul
                data_rd_e = (data_rs1_e * data_rs2_e) & 32'h00000000ffffffff;
              end
            end
            3'b001: begin
              regfile_we = 1'b1;
              if (insn_from_imem[31:25] == 7'd0) begin
                //sll
                data_rd_e = data_rs1_e << (data_rs2_e[4:0]);
              end else if (insn_from_imem[31:25] == 7'b0000001) begin
                //mulh
                logic [63:0] inter_mulh;
                inter_mulh = ($signed(data_rs1_e) * $signed(data_rs2_e));
                data_rd_e  = inter_mulh[63:32];
              end
            end
            3'b010: begin
              regfile_we = 1'b1;

              if (insn_from_imem[31:25] == 7'd0) begin
                //slt
                data_rd_e = $signed(data_rs1_e) < $signed(data_rs2_e) ? 1 : 0;
              end else if (insn_from_imem[31:25] == 7'b0000001) begin
                //mulhsu
                logic [63:0] inter_mulhsu;
                inter_mulhsu = $signed(data_rs1_e) * $signed({1'b0, data_rs2_e});
                data_rd_e = (inter_mulhsu[63:32]);
              end
            end
            3'b011: begin
              regfile_we = 1'b1;
              if (insn_from_imem[31:25] == 7'd0) begin
                //sltu
                data_rd_e = data_rs1_e < data_rs2_e ? 1 : 0;
              end else if (insn_from_imem[31:25] == 7'b0000001) begin
                //mulhu
                logic [63:0] inter_mulhu;
                inter_mulhu = ($unsigned(data_rs1_e) * $unsigned(data_rs2_e));
                data_rd_e   = inter_mulhu[63:32];
              end
            end
            3'b100: begin
              regfile_we = 1'b1;
              if (insn_from_imem[31:25] == 7'd0) begin
                //xor
                data_rd_e = data_rs1_e ^ data_rs2_e;
              end else if (insn_from_imem[31:25] == 7'b0000001) begin
                if (data_rs2_e == 0) begin
                  data_rd_e = 32'hFFFF_FFFF;  // div by 0 error
                end else if (data_rs1_e[31] != data_rs2_e[31]) begin
                  data_rd_e = ~div_qot_reg + 1'b1;
                  // data_rd_e= ((~div_qot_reg)+(1'b1*(|(~div_qot_reg)))+(&div_qot_reg * ({32{1'b1}})));
                  //(((~div_qot_reg) | ({{31{&div_qot_reg}}, 1'b0})) + 1'b1);
                end else begin
                  data_rd_e = div_qot_reg;  // case falls here (should be 3)
                end
              end
            end
            3'b101: begin
              if (insn_from_imem[31:25] == 7'd0) begin
                //srl
                regfile_we = 1'b1;
                data_rd_e  = data_rs1_e >> (data_rs2_e[4:0]);
              end else if (insn_from_imem[31:25] == 7'b0100000) begin
                //sra
                regfile_we = 1'b1;
                data_rd_e  = $signed(data_rs1_e) >>> $signed((data_rs2_e[4:0]));
              end else if (insn_from_imem[31:25] == 7'b0000001) begin
                //divu
                if (flag_div == 1) begin
                  regfile_we = 1'b1;  //enable writing back to RF
                  if (data_rs2_e == 0) begin
                    data_rd_e = 32'hFFFF_FFFF;  // div by 0 error
                  end else begin
                    data_rd_e = div_u_qot_reg;  //we can write the quotient
                  end
                end else begin
                  regfile_we = 1'b0;  //disable writing back to RF
                end
              end
            end
            3'b110: begin
              regfile_we = 1'b1;
              if (insn_from_imem[31:25] == 7'd0) begin
                //or
                data_rd_e = data_rs1_e | data_rs2_e;
              end else if (insn_from_imem[31:25] == 7'b0000001) begin
                //rem
                if (data_rs1_e[31]) begin
                  data_rd_e = ((~div_rem_reg) + 1'b1);
                end else begin
                  data_rd_e = div_rem_reg;
                end
                // if (flag_div) begin
                //   flag_div = 1'b0;
                // end else begin
                //   flag_div = 1'b1;
                // end
              end
            end
            3'b111: begin
              regfile_we = 1'b1;
              if (insn_from_imem[31:25] == 7'd0) begin
                //and
                data_rd_e = data_rs1_e & data_rs2_e;
              end else if (insn_from_imem[31:25] == 7'b0000001) begin
                //remu
                data_rd_e = div_u_rem_reg;
                // if (flag_div) begin
                //   flag_div = 1'b0;
                // end else begin
                //   flag_div = 1'b1;
                // end
              end
            end
            default: begin
              illegal_insn = 1'b1;
              regfile_we   = 1'b0;
            end
          endcase
        end
        OpcodeJal: begin
          regfile_we = 1'b1;
          data_rd_e  = f_pc_current + 4;
          f_pc_next  = f_pc_current + execute_state.imm_j_sext_e;
        end
        OpcodeJalr: begin
          regfile_we = 1'b1;
          data_rd_e = f_pc_current + 4;
          f_pc_next = ((data_rs1_e + execute_state.imm_i_sext_e) &
                (32'b11111111111111111111111111111110));
        end
        OpcodeLoad: begin
          regfile_we = 1'b1;
          // addr_to_dmem = {{temp_load_casing[31:2]}, 2'b00};
          case (insn_from_imem[14:12])
            3'b000: begin
              // lb loads an 8-bit value from mem, SEXT to 32 bits, then stores in rd
              // Ensure addres is aligned
              temp_addr = data_rs1_e + execute_state.imm_i_sext_e;
              case (temp_addr[1:0])
                2'b00:
                // aligned so we grab the first byte
                data_rd_e = {
                  {24{load_data_from_dmem[7]}}, load_data_from_dmem[7:0]
                };
                2'b01:
                // mod 1 -> grab the second byte
                data_rd_e = {
                  {24{load_data_from_dmem[15]}}, load_data_from_dmem[15:8]
                };
                2'b10:
                // mod 2 -> grab the third byte
                data_rd_e = {
                  {24{load_data_from_dmem[23]}}, load_data_from_dmem[23:16]
                };
                2'b11:
                // mod 3 -> grab the 4th byte
                data_rd_e = {
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
              // Align to the nearest lower half-word boundary
              // Assuming memory access returns a 32-bit word
              temp_addr = data_rs1_e + execute_state.imm_i_sext_e;
              case (temp_addr[1])
                1'b0: begin
                  // Aligned access so we grab the first 16 bits
                  data_rd_e = {{16{load_data_from_dmem[15]}}, load_data_from_dmem[15:0]};
                end
                1'b1: begin
                  // Unaligned access, half-word crosses 32-bit word boundary
                  // Grab the second 16 bits
                  data_rd_e = {{16{load_data_from_dmem[31]}}, load_data_from_dmem[31:16]};
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
              temp_addr = data_rs1_e + execute_state.imm_i_sext_e;
              data_rd_e = load_data_from_dmem;  // Data loaded from memory
            end
            3'b100: begin
              // lbu loads an 8-bit value from mem, zext to 32 bits, then stores in rd
              // Sign-extend based on the lowest 2 bits of the address
              temp_addr = data_rs1_e + execute_state.imm_i_sext_e;
              case (temp_addr[1:0])
                2'b00: data_rd_e = {24'b0, load_data_from_dmem[7:0]};  //mul of 4 (mod 0)
                2'b01: data_rd_e = {24'b0, load_data_from_dmem[15:8]};  //mod 1
                2'b10: data_rd_e = {24'b0, load_data_from_dmem[23:16]};  // mod 2
                2'b11: data_rd_e = {24'b0, load_data_from_dmem[31:24]};  // mod 3
                default: begin
                  regfile_we   = 1'b0;
                  illegal_insn = 1'b1;
                end
              endcase
            end
            3'b101: begin
              // lhu loads a 16-bit value from mem, 0-fills to 32-bits, then stores in rd
              // Assuming memory access returns a 32-bit word
              temp_addr = data_rs1_e + execute_state.imm_i_sext_e;
              case (temp_addr[1])
                1'b0: begin
                  // Aligned access
                  data_rd_e = {16'b0, load_data_from_dmem[15:0]};
                end
                1'b1: begin
                  // Unaligned access, half-word crosses 32-bit word boundary
                  // Grab the second 16 bits
                  data_rd_e = {16'b0, load_data_from_dmem[31:16]};
                end
                default: begin
                  illegal_insn = 1'b1;
                  regfile_we   = 1'b0;
                end
              endcase
            end
            default: begin
              temp_addr = 'd0;
              illegal_insn = 1'b1;
              regfile_we = 1'b0;
            end
          endcase
          addr_to_dmem = {{temp_addr[31:2]}, 2'b00};
        end
        OpcodeStore: begin
          // temp_addr = data_rs1_e + imm_s_sext;
          temp_addr = data_rs1_e + execute_state.imm_s_sext_e;
          if (insn_sb) begin
            //store byte
            // addr_to_dmem = {temp_addr[31:2], 2'b00};
            case (temp_addr[1:0])
              //aligned
              2'b00: begin
                store_data_to_dmem[7:0] = data_rs2_e[7:0];
                store_we_to_dmem = 4'b0001;
              end
              2'b01: begin
                store_data_to_dmem[15:8] = data_rs2_e[7:0];
                //mod 1
                store_we_to_dmem = 4'b0010;
              end
              2'b10: begin
                store_data_to_dmem[23 : 16] = data_rs2_e[7:0];
                //mod 2
                store_we_to_dmem = 4'b0100;
              end
              //mod3
              2'b11: begin
                store_data_to_dmem[31 : 24] = data_rs2_e[7:0];
                store_we_to_dmem = 4'b1000;
              end
              default: begin
                regfile_we   = 1'b0;
                illegal_insn = 1'b1;
              end
            endcase
          end else if (insn_sh) begin
            //store half
            temp_addr = data_rs1_e + execute_state.imm_s_sext_e;
            // addr_to_dmem = {temp_add[31:2], 2'b00};
            //allignment
            case (temp_addr[1])
              1'b0: begin
                //aligned
                store_data_to_dmem[15:0] = data_rs2_e[15:0];
                store_we_to_dmem = 4'b0011;
              end
              1'b1: begin
                // mod 1
                store_data_to_dmem[31:16] = data_rs2_e[15:0];
                store_we_to_dmem = 4'b1100;
              end
              default: begin
                regfile_we   = 1'b0;
                illegal_insn = 1'b1;
              end
            endcase
          end else if (insn_sw) begin
            //store word -> assuming fullt aligned
            store_we_to_dmem = 4'b1111;
            temp_addr = data_rs1_e + execute_state.imm_s_sext_e;
            // addr_to_dmem = {temp_add[31:2], 2'b00};
            store_data_to_dmem[31:0] = data_rs2_e;
          end else begin
            temp_addr = 'd0;
            regfile_we = 1'b0;
            illegal_insn = 1'b1;
          end
          addr_to_dmem = {{temp_addr[31:2]}, 2'b00};
        end
        default: begin
        end
      endcase
    end
    // f_pc_next = f_pc_current+4
    //^^^^^ relocated to inside case statements to allow for branching logic
  end
endmodule

module MemorySingleCycle #(
    parameter int NUM_WORDS = 512
) (
    // rst for both imem and dmem
    input wire rst,

    // clock for both imem and dmem. The memory reads/writes on @(negedge clk)
    input wire clk,

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

  always @(negedge clk) begin
    if (rst) begin
    end else begin
      insn_from_imem <= mem[{pc_to_imem[AddrMsb:AddrLsb]}];
    end
  end

  always @(negedge clk) begin
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

/* This design has just one clock for both processor and memory. */
module RiscvProcessor (
    input wire clk,
    input wire rst,
    output logic halt,
    output wire [`REG_SIZE] trace_writeback_pc,
    output wire [`INSN_SIZE] trace_writeback_insn,
    output cycle_status_e trace_writeback_cycle_status
);

  wire [`INSN_SIZE] insn_from_imem;
  wire [`REG_SIZE] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [3:0] mem_data_we;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) the_mem (
      .rst                (rst),
      .clk                (clk),
      // imem is read-only
      .pc_to_imem         (pc_to_imem),
      .insn_from_imem     (insn_from_imem),
      // dmem is read-write
      .addr_to_dmem       (mem_data_addr),
      .load_data_from_dmem(mem_data_loaded_value),
      .store_data_to_dmem (mem_data_to_write),
      .store_we_to_dmem   (mem_data_we)
  );

  DatapathPipelined datapath (
      .clk(clk),
      .rst(rst),
      .pc_to_imem(pc_to_imem),
      .insn_from_imem(insn_from_imem),
      .addr_to_dmem(mem_data_addr),
      .store_data_to_dmem(mem_data_to_write),
      .store_we_to_dmem(mem_data_we),
      .load_data_from_dmem(mem_data_loaded_value),
      .halt(halt),
      .trace_writeback_pc(trace_writeback_pc),
      .trace_writeback_insn(trace_writeback_insn),
      .trace_writeback_cycle_status(trace_writeback_cycle_status)
  );

endmodule
