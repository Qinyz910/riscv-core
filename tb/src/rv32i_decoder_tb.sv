// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_core_pkg::*;

module rv32i_decoder_tb;

  logic [31:0] instr;
  decode_ctrl_t ctrl;
  logic illegal;

  rv32i_decoder dut (
    .instr_i   (instr),
    .ctrl_o    (ctrl),
    .illegal_o (illegal)
  );

  function automatic logic [31:0] encode_r_type(
    input logic [6:0] funct7,
    input logic [4:0] rs2,
    input logic [4:0] rs1,
    input logic [2:0] funct3,
    input logic [4:0] rd,
    input logic [6:0] opcode
  );
    return {funct7, rs2, rs1, funct3, rd, opcode};
  endfunction

  function automatic logic [31:0] encode_i_type(
    input logic signed [11:0] imm,
    input logic [4:0] rs1,
    input logic [2:0] funct3,
    input logic [4:0] rd,
    input logic [6:0] opcode
  );
    logic [11:0] imm_bits;
    imm_bits = imm;
    return {imm_bits, rs1, funct3, rd, opcode};
  endfunction

  function automatic logic [31:0] encode_s_type(
    input logic signed [11:0] imm,
    input logic [4:0] rs2,
    input logic [4:0] rs1,
    input logic [2:0] funct3,
    input logic [6:0] opcode
  );
    logic [11:0] imm_bits;
    imm_bits = imm;
    return {imm_bits[11:5], rs2, rs1, funct3, imm_bits[4:0], opcode};
  endfunction

  function automatic logic [31:0] encode_b_type(
    input logic signed [12:0] imm,
    input logic [4:0] rs2,
    input logic [4:0] rs1,
    input logic [2:0] funct3,
    input logic [6:0] opcode
  );
    logic [12:0] imm_bits;
    imm_bits = imm;
    return {imm_bits[12], imm_bits[10:5], rs2, rs1, funct3, imm_bits[4:1], imm_bits[11], opcode};
  endfunction

  function automatic logic [31:0] encode_u_type(
    input logic [19:0] imm,
    input logic [4:0] rd,
    input logic [6:0] opcode
  );
    return {imm, rd, opcode};
  endfunction

  function automatic logic [31:0] encode_j_type(
    input logic signed [20:0] imm,
    input logic [4:0] rd,
    input logic [6:0] opcode
  );
    logic [20:0] imm_bits;
    imm_bits = imm;
    return {imm_bits[20], imm_bits[10:1], imm_bits[11], imm_bits[19:12], rd, opcode};
  endfunction

  task automatic check(input string name, input bit condition);
    if (!condition) begin
      $display("[decoder_tb] FAIL: %s (instr=0x%08x)", name, instr);
      $fatal(1);
    end else begin
      $display("[decoder_tb] PASS: %s", name);
    end
  endtask

  initial begin
    instr = 32'h0000_0000;
    #1;
    check("illegal opcode flagged", illegal && !ctrl.valid);

    instr = encode_u_type(20'h12345, 5'd5, 7'b0110111);
    #1;
    check("LUI valid", ctrl.valid && !illegal);
    check("LUI control fields", ctrl.rd == 5'd5 && ctrl.op_a_sel == OP_A_ZERO && ctrl.op_b_sel == OP_B_IMM);
    check("LUI immediate type", ctrl.imm_type == IMM_U && ctrl.alu_op == ALU_OP_PASS_B);
    check("LUI writeback", ctrl.wb_sel == WB_FROM_ALU && ctrl.reg_write);

    instr = encode_u_type(20'h0ABCD, 5'd7, 7'b0010111);
    #1;
    check("AUIPC valid", ctrl.valid && !illegal);
    check("AUIPC controls", ctrl.rd == 5'd7 && ctrl.op_a_sel == OP_A_PC && ctrl.op_b_sel == OP_B_IMM);
    check("AUIPC operations", ctrl.alu_op == ALU_OP_ADD && ctrl.imm_type == IMM_U);

    instr = encode_j_type(21'd32, 5'd1, 7'b1101111);
    #1;
    check("JAL valid", ctrl.valid && !illegal);
    check("JAL jump flags", ctrl.jump && !ctrl.branch && !ctrl.jalr);
    check("JAL control selections", ctrl.op_a_sel == OP_A_PC && ctrl.op_b_sel == OP_B_IMM && ctrl.imm_type == IMM_J);
    check("JAL writeback", ctrl.wb_sel == WB_FROM_PC4 && ctrl.reg_write);

    instr = encode_i_type(12'd12, 5'd6, 3'b000, 5'd5, 7'b1100111);
    #1;
    check("JALR valid", ctrl.valid && !illegal);
    check("JALR flags", ctrl.jump && ctrl.jalr && !ctrl.branch);
    check("JALR controls", ctrl.rs1 == 5'd6 && ctrl.rd == 5'd5 && ctrl.op_a_sel == OP_A_RS1 && ctrl.op_b_sel == OP_B_IMM);
    check("JALR writeback", ctrl.wb_sel == WB_FROM_PC4 && ctrl.alu_op == ALU_OP_ADD && ctrl.imm_type == IMM_I);

    instr = encode_b_type(13'd16, 5'd2, 5'd1, 3'b000, 7'b1100011);
    #1;
    check("BEQ valid", ctrl.valid && !illegal);
    check("BEQ branch fields", ctrl.branch && !ctrl.jump && ctrl.branch_type == BR_EQ);
    check("BEQ operands", ctrl.rs1 == 5'd1 && ctrl.rs2 == 5'd2 && ctrl.op_a_sel == OP_A_PC && ctrl.op_b_sel == OP_B_IMM);

    instr = encode_b_type(-13'sd8, 5'd4, 5'd3, 3'b110, 7'b1100011);
    #1;
    check("BLTU valid", ctrl.valid && !illegal);
    check("BLTU branch type", ctrl.branch_type == BR_LTU && ctrl.branch);

    instr = encode_i_type(12'd8, 5'd1, 3'b010, 5'd5, 7'b0000011);
    #1;
    check("LW valid", ctrl.valid && !illegal);
    check("LW controls", ctrl.mem_read && !ctrl.mem_write && ctrl.mem_size == MEM_SIZE_WORD && !ctrl.mem_unsigned);
    check("LW writeback", ctrl.wb_sel == WB_FROM_MEM && ctrl.reg_write && ctrl.rs1 == 5'd1 && ctrl.rd == 5'd5);

    instr = encode_i_type(12'd4, 5'd2, 3'b100, 5'd6, 7'b0000011);
    #1;
    check("LBU valid", ctrl.valid && !illegal);
    check("LBU unsigned", ctrl.mem_read && ctrl.mem_size == MEM_SIZE_BYTE && ctrl.mem_unsigned);

    instr = encode_s_type(12'd12, 5'd7, 5'd3, 3'b010, 7'b0100011);
    #1;
    check("SW valid", ctrl.valid && !illegal);
    check("SW controls", ctrl.mem_write && !ctrl.mem_read && ctrl.mem_size == MEM_SIZE_WORD && ctrl.wb_sel == WB_FROM_NONE);

    instr = encode_i_type(-12'sd1, 5'd4, 3'b000, 5'd8, 7'b0010011);
    #1;
    check("ADDI valid", ctrl.valid && !illegal);
    check("ADDI control", ctrl.rs1 == 5'd4 && ctrl.rd == 5'd8 && ctrl.op_a_sel == OP_A_RS1 && ctrl.op_b_sel == OP_B_IMM);

    instr = encode_i_type({7'b0100000, 5'b11111}, 5'd10, 3'b101, 5'd9, 7'b0010011);
    #1;
    check("SRAI valid", ctrl.valid && !illegal);
    check("SRAI operation", ctrl.alu_op == ALU_OP_SRA && ctrl.imm_type == IMM_I);

    instr = encode_r_type(7'b0000000, 5'd13, 5'd12, 3'b111, 5'd11, 7'b0110011);
    #1;
    check("AND valid", ctrl.valid && !illegal);
    check("AND controls", ctrl.rs1 == 5'd12 && ctrl.rs2 == 5'd13 && ctrl.rd == 5'd11 && ctrl.alu_op == ALU_OP_AND);

    instr = encode_b_type(13'd4, 5'd2, 5'd1, 3'b010, 7'b1100011);
    #1;
    check("branch funct3 illegal", !ctrl.valid && illegal);

    instr = encode_i_type({7'b0100000, 5'b00001}, 5'd2, 3'b001, 5'd3, 7'b0010011);
    #1;
    check("SLLI invalid funct7", !ctrl.valid && illegal);

    instr = encode_r_type(7'b0000001, 5'd2, 5'd1, 3'b000, 5'd3, 7'b0110011);
    #1;
    check("OP with unsupported funct7", !ctrl.valid && illegal);

    $display("[decoder_tb] All decoder scenarios passed");
    #5 $finish;
  end

endmodule : rv32i_decoder_tb
