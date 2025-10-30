// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_core_pkg::*;

/**
 * rv32i_alu
 * ---------
 * Combinational arithmetic and logic unit covering the RV32I base integer
 * instruction set. The unit is fully combinational and always ready to accept
 * new operands; `result_ready_o` and `cmp_ready_o` remain asserted so the stage
 * that instantiates the ALU can be wired into future ready/valid pipelines
 * without interface changes.
 */
module rv32i_alu #(
  parameter int unsigned XLEN_P = XLEN
) (
  input  logic [XLEN_P-1:0] operand_a_i,
  input  logic [XLEN_P-1:0] operand_b_i,
  input  alu_op_e           op_i,
  output logic [XLEN_P-1:0] result_o,
  output logic              cmp_eq_o,
  output logic              cmp_lt_o,
  output logic              cmp_ltu_o,
  output logic              result_ready_o,
  output logic              cmp_ready_o
);

  localparam int unsigned SHIFT_WIDTH_P = (XLEN_P > 1) ? $clog2(XLEN_P) : 1;

  logic [SHIFT_WIDTH_P-1:0] shamt;
  logic [XLEN_P-1:0]        add_result;
  logic [XLEN_P-1:0]        sub_result;
  logic [XLEN_P-1:0]        shift_left;
  logic [XLEN_P-1:0]        shift_right_logical;
  logic [XLEN_P-1:0]        shift_right_arith;
  logic [XLEN_P-1:0]        result;
  logic                     cmp_eq;
  logic                     cmp_lt_signed;
  logic                     cmp_lt_unsigned;

  assign shamt               = operand_b_i[SHIFT_WIDTH_P-1:0];
  assign add_result          = operand_a_i + operand_b_i;
  assign sub_result          = operand_a_i - operand_b_i;
  assign shift_left          = operand_a_i << shamt;
  assign shift_right_logical = operand_a_i >> shamt;
  assign shift_right_arith   = $signed(operand_a_i) >>> shamt;

  assign cmp_eq          = (operand_a_i == operand_b_i);
  assign cmp_lt_signed   = ($signed(operand_a_i) < $signed(operand_b_i));
  assign cmp_lt_unsigned = (operand_a_i < operand_b_i);

  always_comb begin
    result = '0;
    unique case (op_i)
      ALU_OP_ADD:    result = add_result;
      ALU_OP_SUB:    result = sub_result;
      ALU_OP_AND:    result = operand_a_i & operand_b_i;
      ALU_OP_OR:     result = operand_a_i | operand_b_i;
      ALU_OP_XOR:    result = operand_a_i ^ operand_b_i;
      ALU_OP_SLL:    result = shift_left;
      ALU_OP_SRL:    result = shift_right_logical;
      ALU_OP_SRA:    result = shift_right_arith;
      ALU_OP_SLT:    result = {{(XLEN_P-1){1'b0}}, cmp_lt_signed};
      ALU_OP_SLTU:   result = {{(XLEN_P-1){1'b0}}, cmp_lt_unsigned};
      ALU_OP_PASS_B: result = operand_b_i;
      default:       result = '0;
    endcase
  end

  assign result_o     = result;
  assign cmp_eq_o     = cmp_eq;
  assign cmp_lt_o     = cmp_lt_signed;
  assign cmp_ltu_o    = cmp_lt_unsigned;
  assign result_ready_o = 1'b1;
  assign cmp_ready_o    = 1'b1;

`ifndef SYNTHESIS
  always_comb begin
    if ($isunknown(op_i)) begin
      $fatal(1, "[rv32i_alu] op_i contains X/Z values");
    end
  end
`endif

endmodule : rv32i_alu
