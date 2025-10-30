// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_core_pkg::*;

module rv32i_ex_stage (
  input  logic            id_valid_i,
  input  id_ex_payload_t  id_payload_i,
  output logic            ex_valid_o,
  output ex_mem_payload_t ex_payload_o,
  output logic            branch_taken_o,
  output logic [31:0]     branch_target_o
);

  logic [31:0] operand_a;
  logic [31:0] operand_b;
  logic [31:0] alu_result;
  logic        cmp_eq;
  logic        cmp_lt;
  logic        cmp_ltu;
  logic        alu_result_ready;
  logic        alu_cmp_ready;
  logic [31:0] pc_plus_imm;
  logic [31:0] jalr_target;
  logic        branch_condition_met;
  logic        branch_taken;

  always_comb begin
    unique case (id_payload_i.op_a_sel)
      OP_A_RS1:  operand_a = id_payload_i.rs1_data;
      OP_A_PC:   operand_a = id_payload_i.pc;
      default:   operand_a = 32'd0;
    endcase

    unique case (id_payload_i.op_b_sel)
      OP_B_RS2:    operand_b = id_payload_i.rs2_data;
      OP_B_IMM:    operand_b = id_payload_i.imm;
      OP_B_CONST4: operand_b = 32'd4;
      default:     operand_b = 32'd0;
    endcase
  end

  rv32i_alu alu_i (
    .operand_a_i     (operand_a),
    .operand_b_i     (operand_b),
    .op_i            (id_payload_i.alu_op),
    .result_o        (alu_result),
    .cmp_eq_o        (cmp_eq),
    .cmp_lt_o        (cmp_lt),
    .cmp_ltu_o       (cmp_ltu),
    .result_ready_o  (alu_result_ready),
    .cmp_ready_o     (alu_cmp_ready)
  );

  assign pc_plus_imm = id_payload_i.pc + id_payload_i.imm;
  assign jalr_target = {alu_result[31:1], 1'b0};

  always_comb begin
    branch_condition_met = 1'b0;
    if (alu_cmp_ready) begin
      unique case (id_payload_i.branch_type)
        BR_EQ:  branch_condition_met = cmp_eq;
        BR_NE:  branch_condition_met = !cmp_eq;
        BR_LT:  branch_condition_met = cmp_lt;
        BR_GE:  branch_condition_met = !cmp_lt;
        BR_LTU: branch_condition_met = cmp_ltu;
        BR_GEU: branch_condition_met = !cmp_ltu;
        default: branch_condition_met = 1'b0;
      endcase
    end
  end

  assign branch_taken   = id_valid_i && ((id_payload_i.branch && branch_condition_met) || id_payload_i.jump);
  assign branch_target_o= id_payload_i.jalr ? jalr_target : pc_plus_imm;
  assign branch_taken_o = branch_taken;

  always_comb begin
    ex_payload_o = '0;
    ex_payload_o.pc           = id_payload_i.pc;
    ex_payload_o.pc_plus4     = id_payload_i.pc_plus4;
    ex_payload_o.alu_result   = alu_result;
    ex_payload_o.rs2_data     = id_payload_i.rs2_data;
    ex_payload_o.rd_addr      = id_payload_i.rd_addr;
    ex_payload_o.wb_sel       = id_payload_i.wb_sel;
    ex_payload_o.mem_read     = id_payload_i.mem_read;
    ex_payload_o.mem_write    = id_payload_i.mem_write;
    ex_payload_o.mem_size     = id_payload_i.mem_size;
    ex_payload_o.mem_unsigned = id_payload_i.mem_unsigned;
    ex_payload_o.reg_write    = id_payload_i.reg_write;
    ex_payload_o.branch_type  = id_payload_i.branch_type;
    ex_payload_o.branch       = id_payload_i.branch;
    ex_payload_o.jump         = id_payload_i.jump;
    ex_payload_o.jalr         = id_payload_i.jalr;
  end

  assign ex_valid_o = id_valid_i && alu_result_ready;

`ifndef SYNTHESIS
  always_comb begin
    if ($isunknown({alu_result_ready, alu_cmp_ready})) begin
      $fatal(1, "[rv32i_ex_stage] ALU ready signals contain X/Z values");
    end else if (!alu_result_ready || !alu_cmp_ready) begin
      $fatal(1, "[rv32i_ex_stage] ALU ready signals deasserted in single-cycle configuration");
    end
  end
`endif

endmodule : rv32i_ex_stage
