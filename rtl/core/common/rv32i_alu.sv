// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_core_pkg::*;

module rv32i_alu #(
  parameter int unsigned XLEN_P = XLEN
) (
  input  logic [XLEN_P-1:0] operand_a_i,
  input  logic [XLEN_P-1:0] operand_b_i,
  input  alu_op_e           op_i,
  output logic [XLEN_P-1:0] result_o,
  output logic              cmp_eq_o,
  output logic              cmp_lt_o,
  output logic              cmp_ltu_o
);

  logic [XLEN_P-1:0] add_result;
  logic [XLEN_P-1:0] sub_result;
  logic [XLEN_P-1:0] shift_result;
  logic [XLEN_P-1:0] result;
  logic               cmp_eq;
  logic               cmp_lt_signed;
  logic               cmp_lt_unsigned;

  assign add_result = operand_a_i + operand_b_i;
  assign sub_result = operand_a_i - operand_b_i;

  assign cmp_eq          = (operand_a_i == operand_b_i);
  assign cmp_lt_signed   = ($signed(operand_a_i) < $signed(operand_b_i));
  assign cmp_lt_unsigned = (operand_a_i < operand_b_i);

  always_comb begin
    shift_result = '0;
    case (op_i)
      ALU_OP_SLL: shift_result = operand_a_i << operand_b_i[$clog2(XLEN_P)-1:0];
      ALU_OP_SRL: shift_result = operand_a_i >> operand_b_i[$clog2(XLEN_P)-1:0];
      ALU_OP_SRA: shift_result = $signed(operand_a_i) >>> operand_b_i[$clog2(XLEN_P)-1:0];
      default:    shift_result = '0;
    endcase
  end

  always_comb begin
    result = '0;
    unique case (op_i)
      ALU_OP_ADD:    result = add_result;
      ALU_OP_SUB:    result = sub_result;
      ALU_OP_AND:    result = operand_a_i & operand_b_i;
      ALU_OP_OR:     result = operand_a_i | operand_b_i;
      ALU_OP_XOR:    result = operand_a_i ^ operand_b_i;
      ALU_OP_SLL,
      ALU_OP_SRL,
      ALU_OP_SRA:    result = shift_result;
      ALU_OP_SLT:    result = {{(XLEN_P-1){1'b0}}, cmp_lt_signed};
      ALU_OP_SLTU:   result = {{(XLEN_P-1){1'b0}}, cmp_lt_unsigned};
      ALU_OP_PASS_B: result = operand_b_i;
      default:       result = '0;
    endcase
  end

  assign result_o  = result;
  assign cmp_eq_o  = cmp_eq;
  assign cmp_lt_o  = cmp_lt_signed;
  assign cmp_ltu_o = cmp_lt_unsigned;

endmodule : rv32i_alu
