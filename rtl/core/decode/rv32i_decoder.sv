// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_core_pkg::*;

module rv32i_decoder (
  input  logic [31:0]  instr_i,
  output decode_ctrl_t ctrl_o,
  output logic         illegal_o
);

  logic [6:0] opcode;
  logic [2:0] funct3;
  logic [6:0] funct7;
  logic [4:0] rd;
  logic [4:0] rs1;
  logic [4:0] rs2;

  decode_ctrl_t ctrl;
  logic         illegal;

  assign opcode = instr_i[6:0];
  assign funct3 = instr_i[14:12];
  assign funct7 = instr_i[31:25];
  assign rd     = instr_i[11:7];
  assign rs1    = instr_i[19:15];
  assign rs2    = instr_i[24:20];

  always_comb begin
    ctrl = '{
      valid:        1'b0,
      rd:           5'd0,
      rs1:          5'd0,
      rs2:          5'd0,
      op_a_sel:     OP_A_ZERO,
      op_b_sel:     OP_B_ZERO,
      alu_op:       ALU_OP_ADD,
      imm_type:     IMM_NONE,
      wb_sel:       WB_FROM_ALU,
      branch_type:  BR_NONE,
      branch:       1'b0,
      jump:         1'b0,
      jalr:         1'b0,
      mem_read:     1'b0,
      mem_write:    1'b0,
      mem_size:     MEM_SIZE_WORD,
      mem_unsigned: 1'b0,
      reg_write:    1'b0
    };
    illegal = 1'b0;

    unique case (opcode)
      7'b0110111: begin // LUI
        ctrl.valid        = 1'b1;
        ctrl.rd           = rd;
        ctrl.alu_op       = ALU_OP_PASS_B;
        ctrl.op_a_sel     = OP_A_ZERO;
        ctrl.op_b_sel     = OP_B_IMM;
        ctrl.imm_type     = IMM_U;
        ctrl.wb_sel       = WB_FROM_ALU;
        ctrl.reg_write    = 1'b1;
      end
      7'b0010111: begin // AUIPC
        ctrl.valid        = 1'b1;
        ctrl.rd           = rd;
        ctrl.op_a_sel     = OP_A_PC;
        ctrl.op_b_sel     = OP_B_IMM;
        ctrl.alu_op       = ALU_OP_ADD;
        ctrl.imm_type     = IMM_U;
        ctrl.wb_sel       = WB_FROM_ALU;
        ctrl.reg_write    = 1'b1;
      end
      7'b1101111: begin // JAL
        ctrl.valid        = 1'b1;
        ctrl.rd           = rd;
        ctrl.op_a_sel     = OP_A_PC;
        ctrl.op_b_sel     = OP_B_IMM;
        ctrl.alu_op       = ALU_OP_ADD;
        ctrl.imm_type     = IMM_J;
        ctrl.jump         = 1'b1;
        ctrl.wb_sel       = WB_FROM_PC4;
        ctrl.reg_write    = 1'b1;
      end
      7'b1100111: begin // JALR
        ctrl.valid        = 1'b1;
        ctrl.rd           = rd;
        ctrl.rs1          = rs1;
        ctrl.op_a_sel     = OP_A_RS1;
        ctrl.op_b_sel     = OP_B_IMM;
        ctrl.alu_op       = ALU_OP_ADD;
        ctrl.imm_type     = IMM_I;
        ctrl.jump         = 1'b1;
        ctrl.jalr         = 1'b1;
        ctrl.wb_sel       = WB_FROM_PC4;
        ctrl.reg_write    = 1'b1;
      end
      7'b1100011: begin // Branch
        ctrl.valid     = 1'b1;
        ctrl.rs1       = rs1;
        ctrl.rs2       = rs2;
        ctrl.op_a_sel  = OP_A_PC;
        ctrl.op_b_sel  = OP_B_IMM;
        ctrl.alu_op    = ALU_OP_ADD;
        ctrl.imm_type  = IMM_B;
        ctrl.branch    = 1'b1;
        unique case (funct3)
          3'b000: ctrl.branch_type = BR_EQ;
          3'b001: ctrl.branch_type = BR_NE;
          3'b100: ctrl.branch_type = BR_LT;
          3'b101: ctrl.branch_type = BR_GE;
          3'b110: ctrl.branch_type = BR_LTU;
          3'b111: ctrl.branch_type = BR_GEU;
          default: begin
            ctrl.valid  = 1'b0;
            illegal     = 1'b1;
          end
        endcase
      end
      7'b0000011: begin // Load
        ctrl.valid        = 1'b1;
        ctrl.rd           = rd;
        ctrl.rs1          = rs1;
        ctrl.op_a_sel     = OP_A_RS1;
        ctrl.op_b_sel     = OP_B_IMM;
        ctrl.alu_op       = ALU_OP_ADD;
        ctrl.imm_type     = IMM_I;
        ctrl.mem_read     = 1'b1;
        ctrl.wb_sel       = WB_FROM_MEM;
        ctrl.reg_write    = 1'b1;
        unique case (funct3)
          3'b000: begin ctrl.mem_size = MEM_SIZE_BYTE; ctrl.mem_unsigned = 1'b0; end // LB
          3'b001: begin ctrl.mem_size = MEM_SIZE_HALF; ctrl.mem_unsigned = 1'b0; end // LH
          3'b010: begin ctrl.mem_size = MEM_SIZE_WORD; ctrl.mem_unsigned = 1'b0; end // LW
          3'b100: begin ctrl.mem_size = MEM_SIZE_BYTE; ctrl.mem_unsigned = 1'b1; end // LBU
          3'b101: begin ctrl.mem_size = MEM_SIZE_HALF; ctrl.mem_unsigned = 1'b1; end // LHU
          default: begin
            ctrl.valid  = 1'b0;
            illegal     = 1'b1;
          end
        endcase
      end
      7'b0100011: begin // Store
        ctrl.valid        = 1'b1;
        ctrl.rs1          = rs1;
        ctrl.rs2          = rs2;
        ctrl.op_a_sel     = OP_A_RS1;
        ctrl.op_b_sel     = OP_B_IMM;
        ctrl.alu_op       = ALU_OP_ADD;
        ctrl.imm_type     = IMM_S;
        ctrl.mem_write    = 1'b1;
        ctrl.wb_sel       = WB_FROM_NONE;
        unique case (funct3)
          3'b000: ctrl.mem_size = MEM_SIZE_BYTE; // SB
          3'b001: ctrl.mem_size = MEM_SIZE_HALF; // SH
          3'b010: ctrl.mem_size = MEM_SIZE_WORD; // SW
          default: begin
            ctrl.valid  = 1'b0;
            illegal     = 1'b1;
          end
        endcase
      end
      7'b0010011: begin // OP-IMM
        ctrl.valid        = 1'b1;
        ctrl.rd           = rd;
        ctrl.rs1          = rs1;
        ctrl.op_a_sel     = OP_A_RS1;
        ctrl.op_b_sel     = OP_B_IMM;
        ctrl.imm_type     = IMM_I;
        ctrl.wb_sel       = WB_FROM_ALU;
        ctrl.reg_write    = 1'b1;
        unique case (funct3)
          3'b000: ctrl.alu_op = ALU_OP_ADD;  // ADDI
          3'b010: ctrl.alu_op = ALU_OP_SLT;  // SLTI
          3'b011: ctrl.alu_op = ALU_OP_SLTU; // SLTIU
          3'b100: ctrl.alu_op = ALU_OP_XOR;  // XORI
          3'b110: ctrl.alu_op = ALU_OP_OR;   // ORI
          3'b111: ctrl.alu_op = ALU_OP_AND;  // ANDI
          3'b001: begin // SLLI
            if (funct7 == 7'b0000000) begin
              ctrl.alu_op = ALU_OP_SLL;
            end else begin
              ctrl.valid  = 1'b0;
              illegal     = 1'b1;
            end
          end
          3'b101: begin
            if (funct7 == 7'b0000000) begin
              ctrl.alu_op = ALU_OP_SRL; // SRLI
            end else if (funct7 == 7'b0100000) begin
              ctrl.alu_op = ALU_OP_SRA; // SRAI
            end else begin
              ctrl.valid  = 1'b0;
              illegal     = 1'b1;
            end
          end
          default: begin
            ctrl.valid  = 1'b0;
            illegal     = 1'b1;
          end
        endcase
      end
      7'b0110011: begin // OP
        ctrl.valid        = 1'b1;
        ctrl.rd           = rd;
        ctrl.rs1          = rs1;
        ctrl.rs2          = rs2;
        ctrl.op_a_sel     = OP_A_RS1;
        ctrl.op_b_sel     = OP_B_RS2;
        ctrl.imm_type     = IMM_NONE;
        ctrl.wb_sel       = WB_FROM_ALU;
        ctrl.reg_write    = 1'b1;
        unique case ({funct7, funct3})
          {7'b0000000,3'b000}: ctrl.alu_op = ALU_OP_ADD;
          {7'b0100000,3'b000}: ctrl.alu_op = ALU_OP_SUB;
          {7'b0000000,3'b001}: ctrl.alu_op = ALU_OP_SLL;
          {7'b0000000,3'b010}: ctrl.alu_op = ALU_OP_SLT;
          {7'b0000000,3'b011}: ctrl.alu_op = ALU_OP_SLTU;
          {7'b0000000,3'b100}: ctrl.alu_op = ALU_OP_XOR;
          {7'b0000000,3'b101}: ctrl.alu_op = ALU_OP_SRL;
          {7'b0100000,3'b101}: ctrl.alu_op = ALU_OP_SRA;
          {7'b0000000,3'b110}: ctrl.alu_op = ALU_OP_OR;
          {7'b0000000,3'b111}: ctrl.alu_op = ALU_OP_AND;
          default: begin
            ctrl.valid  = 1'b0;
            illegal     = 1'b1;
          end
        endcase
      end
      7'b0001111: begin // FENCE / NOP
        ctrl.valid        = 1'b1;
        ctrl.rd           = rd;
        ctrl.rs1          = rs1;
        ctrl.reg_write    = 1'b0;
      end
      default: begin
        ctrl.valid  = 1'b0;
        illegal     = 1'b1;
      end
    endcase
  end

  assign ctrl_o    = ctrl;
  assign illegal_o = illegal;

endmodule : rv32i_decoder
