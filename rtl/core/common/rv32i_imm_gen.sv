// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_core_pkg::*;

module rv32i_imm_gen (
  input  logic [31:0] instr_i,
  input  imm_type_e   imm_type_i,
  output logic [31:0] imm_o
);

  logic [31:0] imm_value;

  always_comb begin
    imm_value = '0;
    unique case (imm_type_i)
      IMM_I: imm_value = {{20{instr_i[31]}}, instr_i[31:20]};
      IMM_S: imm_value = {{20{instr_i[31]}}, instr_i[31:25], instr_i[11:7]};
      IMM_B: imm_value = {{19{instr_i[31]}}, instr_i[31], instr_i[7], instr_i[30:25], instr_i[11:8], 1'b0};
      IMM_U: imm_value = {instr_i[31:12], 12'b0};
      IMM_J: imm_value = {{11{instr_i[31]}}, instr_i[31], instr_i[19:12], instr_i[20], instr_i[30:21], 1'b0};
      default: imm_value = 32'h0000_0000;
    endcase
  end

  assign imm_o = imm_value;

endmodule : rv32i_imm_gen
