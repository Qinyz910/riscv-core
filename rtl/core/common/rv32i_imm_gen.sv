// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_core_pkg::*;

/**
 * rv32i_imm_gen
 * --------------
 * Produces sign-extended immediates for the RV32I instruction formats. The
 * module is purely combinational and covers I, S, B, U, and J encodings. For
 * instructions without an immediate, the output defaults to zero.
 */
module rv32i_imm_gen #(
  parameter int unsigned XLEN_P = XLEN
) (
  input  logic [31:0] instr_i,
  input  imm_type_e   imm_type_i,
  output logic [XLEN_P-1:0] imm_o
);

  logic [XLEN_P-1:0] imm_value;

  initial begin
    if (XLEN_P != 32) begin
      $fatal(1, "[rv32i_imm_gen] Only XLEN=32 is supported in this implementation (got %0d)", XLEN_P);
    end
  end

  always_comb begin
    unique case (imm_type_i)
      IMM_I: imm_value = {{20{instr_i[31]}}, instr_i[31:20]};
      IMM_S: imm_value = {{20{instr_i[31]}}, instr_i[31:25], instr_i[11:7]};
      IMM_B: imm_value = {{19{instr_i[31]}}, instr_i[31], instr_i[7],
                          instr_i[30:25], instr_i[11:8], 1'b0};
      IMM_U: imm_value = {instr_i[31:12], 12'b0};
      IMM_J: imm_value = {{11{instr_i[31]}}, instr_i[31], instr_i[19:12],
                          instr_i[20], instr_i[30:21], 1'b0};
      default: imm_value = '0;
    endcase
  end

  assign imm_o = imm_value;

`ifndef SYNTHESIS
  always_comb begin
    if ($isunknown(imm_type_i)) begin
      $fatal(1, "[rv32i_imm_gen] imm_type_i contains X/Z values");
    end
  end
`endif

endmodule : rv32i_imm_gen
