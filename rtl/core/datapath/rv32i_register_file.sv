// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_core_pkg::*;

module rv32i_register_file #(
  parameter int unsigned XLEN_P = XLEN
) (
  input  logic                   clk_i,
  input  logic                   rst_ni,
  input  logic [4:0]             rs1_addr_i,
  input  logic [4:0]             rs2_addr_i,
  output logic [XLEN_P-1:0]      rs1_data_o,
  output logic [XLEN_P-1:0]      rs2_data_o,
  input  logic                   rd_we_i,
  input  logic [4:0]             rd_addr_i,
  input  logic [XLEN_P-1:0]      rd_wdata_i
);

  logic [XLEN_P-1:0] regs_q [0:31];

  integer idx;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      for (idx = 0; idx < 32; idx++) begin
        regs_q[idx] <= '0;
      end
    end else begin
      if (rd_we_i && (rd_addr_i != 5'd0)) begin
        regs_q[rd_addr_i] <= rd_wdata_i;
      end
      regs_q[0] <= '0;
    end
  end

  logic [XLEN_P-1:0] rs1_raw;
  logic [XLEN_P-1:0] rs2_raw;

  assign rs1_raw = (rs1_addr_i == 5'd0) ? '0 : regs_q[rs1_addr_i];
  assign rs2_raw = (rs2_addr_i == 5'd0) ? '0 : regs_q[rs2_addr_i];

  assign rs1_data_o = (rd_we_i && (rd_addr_i == rs1_addr_i) && (rd_addr_i != 5'd0))
                    ? rd_wdata_i : rs1_raw;
  assign rs2_data_o = (rd_we_i && (rd_addr_i == rs2_addr_i) && (rd_addr_i != 5'd0))
                    ? rd_wdata_i : rs2_raw;

endmodule : rv32i_register_file
