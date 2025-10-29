// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_control_pkg::*;

module rv32i_forwarding_unit #(
  parameter bit PRIORITIZE_MEM_STAGE = 1'b1
) (
  input  logic [4:0] ex_rs1_addr_i,
  input  logic [4:0] ex_rs2_addr_i,
  input  logic [4:0] mem_rd_addr_i,
  input  logic       mem_regwrite_i,
  input  logic [4:0] wb_rd_addr_i,
  input  logic       wb_regwrite_i,
  output logic [1:0] forward_a_sel_o,
  output logic [1:0] forward_b_sel_o
);

  forwarding_sel_e forward_a_sel;
  forwarding_sel_e forward_b_sel;

  logic mem_matches_rs1;
  logic mem_matches_rs2;
  logic wb_matches_rs1;
  logic wb_matches_rs2;

  assign mem_matches_rs1 = mem_regwrite_i && (mem_rd_addr_i != 5'd0) &&
                           (mem_rd_addr_i == ex_rs1_addr_i);
  assign mem_matches_rs2 = mem_regwrite_i && (mem_rd_addr_i != 5'd0) &&
                           (mem_rd_addr_i == ex_rs2_addr_i);

  assign wb_matches_rs1  = wb_regwrite_i && (wb_rd_addr_i != 5'd0) &&
                           (wb_rd_addr_i == ex_rs1_addr_i);
  assign wb_matches_rs2  = wb_regwrite_i && (wb_rd_addr_i != 5'd0) &&
                           (wb_rd_addr_i == ex_rs2_addr_i);

  always_comb begin
    forward_a_sel = FORWARD_NONE;
    forward_b_sel = FORWARD_NONE;

    if (PRIORITIZE_MEM_STAGE) begin
      if (mem_matches_rs1) begin
        forward_a_sel = FORWARD_FROM_MEM;
      end else if (wb_matches_rs1) begin
        forward_a_sel = FORWARD_FROM_WB;
      end

      if (mem_matches_rs2) begin
        forward_b_sel = FORWARD_FROM_MEM;
      end else if (wb_matches_rs2) begin
        forward_b_sel = FORWARD_FROM_WB;
      end
    end else begin
      if (wb_matches_rs1) begin
        forward_a_sel = FORWARD_FROM_WB;
      end else if (mem_matches_rs1) begin
        forward_a_sel = FORWARD_FROM_MEM;
      end

      if (wb_matches_rs2) begin
        forward_b_sel = FORWARD_FROM_WB;
      end else if (mem_matches_rs2) begin
        forward_b_sel = FORWARD_FROM_MEM;
      end
    end
  end

  assign forward_a_sel_o = forward_a_sel;
  assign forward_b_sel_o = forward_b_sel;

endmodule : rv32i_forwarding_unit
