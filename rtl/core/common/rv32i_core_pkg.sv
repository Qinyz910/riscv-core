// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

package rv32i_core_pkg;

  localparam int unsigned XLEN = 32;

  typedef enum logic [4:0] {
    ALU_OP_ADD   = 5'd0,
    ALU_OP_SUB   = 5'd1,
    ALU_OP_AND   = 5'd2,
    ALU_OP_OR    = 5'd3,
    ALU_OP_XOR   = 5'd4,
    ALU_OP_SLL   = 5'd5,
    ALU_OP_SRL   = 5'd6,
    ALU_OP_SRA   = 5'd7,
    ALU_OP_SLT   = 5'd8,
    ALU_OP_SLTU  = 5'd9,
    ALU_OP_PASS_B= 5'd10
  } alu_op_e;

  typedef enum logic [2:0] {
    IMM_NONE = 3'd0,
    IMM_I    = 3'd1,
    IMM_S    = 3'd2,
    IMM_B    = 3'd3,
    IMM_U    = 3'd4,
    IMM_J    = 3'd5
  } imm_type_e;

  typedef enum logic [1:0] {
    OP_A_RS1  = 2'b00,
    OP_A_PC   = 2'b01,
    OP_A_ZERO = 2'b10
  } op_a_sel_e;

  typedef enum logic [1:0] {
    OP_B_RS2    = 2'b00,
    OP_B_IMM    = 2'b01,
    OP_B_CONST4 = 2'b10,
    OP_B_ZERO   = 2'b11
  } op_b_sel_e;

  typedef enum logic [2:0] {
    BR_NONE = 3'd0,
    BR_EQ   = 3'd1,
    BR_NE   = 3'd2,
    BR_LT   = 3'd3,
    BR_GE   = 3'd4,
    BR_LTU  = 3'd5,
    BR_GEU  = 3'd6
  } branch_type_e;

  typedef enum logic [1:0] {
    MEM_SIZE_BYTE = 2'b00,
    MEM_SIZE_HALF = 2'b01,
    MEM_SIZE_WORD = 2'b10
  } mem_size_e;

  typedef enum logic [1:0] {
    WB_FROM_ALU = 2'b00,
    WB_FROM_MEM = 2'b01,
    WB_FROM_PC4 = 2'b10,
    WB_FROM_NONE= 2'b11
  } wb_sel_e;

  typedef struct packed {
    logic [31:0] pc;
    logic [31:0] instr;
  } if_id_payload_t;

  typedef struct packed {
    logic [31:0] pc;
    logic [31:0] pc_plus4;
    logic [31:0] instr;
    logic [31:0] imm;
    logic [31:0] rs1_data;
    logic [31:0] rs2_data;
    logic [4:0]  rs1_addr;
    logic [4:0]  rs2_addr;
    logic [4:0]  rd_addr;
    op_a_sel_e   op_a_sel;
    op_b_sel_e   op_b_sel;
    alu_op_e     alu_op;
    wb_sel_e     wb_sel;
    branch_type_e branch_type;
    logic        branch;
    logic        jump;
    logic        jalr;
    logic        mem_read;
    logic        mem_write;
    mem_size_e   mem_size;
    logic        mem_unsigned;
    logic        reg_write;
  } id_ex_payload_t;

  typedef struct packed {
    logic [31:0] pc;
    logic [31:0] pc_plus4;
    logic [31:0] alu_result;
    logic [31:0] rs2_data;
    logic [4:0]  rd_addr;
    wb_sel_e     wb_sel;
    logic        mem_read;
    logic        mem_write;
    mem_size_e   mem_size;
    logic        mem_unsigned;
    logic        reg_write;
    branch_type_e branch_type;
    logic        branch;
    logic        jump;
    logic        jalr;
  } ex_mem_payload_t;

  typedef struct packed {
    logic [31:0] pc;
    logic [31:0] pc_plus4;
    logic [31:0] alu_result;
    logic [31:0] mem_rdata;
    logic [4:0]  rd_addr;
    wb_sel_e     wb_sel;
    logic        reg_write;
  } mem_wb_payload_t;

  typedef struct packed {
    logic        valid;
    logic [4:0]  rd;
    logic [4:0]  rs1;
    logic [4:0]  rs2;
    op_a_sel_e   op_a_sel;
    op_b_sel_e   op_b_sel;
    alu_op_e     alu_op;
    imm_type_e   imm_type;
    wb_sel_e     wb_sel;
    branch_type_e branch_type;
    logic        branch;
    logic        jump;
    logic        jalr;
    logic        mem_read;
    logic        mem_write;
    mem_size_e   mem_size;
    logic        mem_unsigned;
    logic        reg_write;
  } decode_ctrl_t;

  function automatic logic [3:0] mem_size_to_be(mem_size_e size, logic [1:0] addr);
    logic [3:0] be;
    case (size)
      MEM_SIZE_BYTE: be = 4'b0001 << addr;
      MEM_SIZE_HALF: be = addr[1] ? 4'b1100 : 4'b0011;
      default:       be = 4'b1111;
    endcase
    return be;
  endfunction

endpackage : rv32i_core_pkg
