// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_core_pkg::*;

/**
 * rv32i_register_file
 * --------------------
 * Dual-read, single-write register file with a hard-wired zero register and
 * optional depth parameterisation. Writes occur on the rising edge of the
 * clock, while reads are asynchronous and support same-cycle bypassing when
 * the destination register matches a read address.
 */
module rv32i_register_file #(
  parameter int unsigned XLEN_P       = XLEN,
  parameter int unsigned DEPTH_P      = 32,
  parameter int unsigned ADDR_WIDTH_P = (DEPTH_P > 1) ? $clog2(DEPTH_P) : 1
) (
  input  logic                     clk_i,
  input  logic                     rst_ni,
  input  logic [ADDR_WIDTH_P-1:0]  rs1_addr_i,
  input  logic [ADDR_WIDTH_P-1:0]  rs2_addr_i,
  output logic [XLEN_P-1:0]        rs1_data_o,
  output logic [XLEN_P-1:0]        rs2_data_o,
  input  logic                     rd_we_i,
  input  logic [ADDR_WIDTH_P-1:0]  rd_addr_i,
  input  logic [XLEN_P-1:0]        rd_wdata_i
);

  localparam int unsigned ZERO_REG_INDEX = 0;

  logic [XLEN_P-1:0] regs_q [0:DEPTH_P-1];
  logic [XLEN_P-1:0] rs1_raw;
  logic [XLEN_P-1:0] rs2_raw;
  logic              rs1_addr_in_range;
  logic              rs2_addr_in_range;
  logic              rd_addr_in_range;

  integer idx;

  initial begin
    if (DEPTH_P < 1) begin
      $fatal(1, "[rv32i_register_file] DEPTH_P must be at least 1 (got %0d)", DEPTH_P);
    end
    if (ZERO_REG_INDEX >= DEPTH_P) begin
      $fatal(1, "[rv32i_register_file] ZERO register index %0d outside DEPTH %0d",
             ZERO_REG_INDEX, DEPTH_P);
    end
    if (ADDR_WIDTH_P < $clog2(DEPTH_P)) begin
      $fatal(1, "[rv32i_register_file] ADDR_WIDTH_P (%0d) insufficient for DEPTH_P (%0d)",
             ADDR_WIDTH_P, DEPTH_P);
    end
  end

  assign rs1_addr_in_range = (rs1_addr_i < DEPTH_P);
  assign rs2_addr_in_range = (rs2_addr_i < DEPTH_P);
  assign rd_addr_in_range  = (rd_addr_i  < DEPTH_P);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      for (idx = 0; idx < DEPTH_P; idx++) begin
        regs_q[idx] <= '0;
      end
    end else begin
      if (rd_we_i && (rd_addr_i != ZERO_REG_INDEX) && rd_addr_in_range) begin
        regs_q[rd_addr_i] <= rd_wdata_i;
      end
      regs_q[ZERO_REG_INDEX] <= '0;
    end
  end

  assign rs1_raw = (rs1_addr_i == ZERO_REG_INDEX) ? '0 :
                   (rs1_addr_in_range ? regs_q[rs1_addr_i] : '0);
  assign rs2_raw = (rs2_addr_i == ZERO_REG_INDEX) ? '0 :
                   (rs2_addr_in_range ? regs_q[rs2_addr_i] : '0);

  assign rs1_data_o = (rd_we_i && (rd_addr_i == rs1_addr_i) &&
                       (rd_addr_i != ZERO_REG_INDEX) && rd_addr_in_range)
                      ? rd_wdata_i : rs1_raw;
  assign rs2_data_o = (rd_we_i && (rd_addr_i == rs2_addr_i) &&
                       (rd_addr_i != ZERO_REG_INDEX) && rd_addr_in_range)
                      ? rd_wdata_i : rs2_raw;

`ifndef SYNTHESIS
  // Assertions catch protocol violations and ensure x0 remains hard-wired to zero.
  property p_zero_reg_constant;
    @(posedge clk_i) disable iff (!rst_ni)
      regs_q[ZERO_REG_INDEX] == '0;
  endproperty

  property p_ignore_zero_reg_writes;
    @(posedge clk_i) disable iff (!rst_ni)
      (rd_we_i && !$isunknown(rd_addr_i) && (rd_addr_i == ZERO_REG_INDEX))
        |-> regs_q[ZERO_REG_INDEX] == '0;
  endproperty

  property p_addresses_in_range;
    @(posedge clk_i) disable iff (!rst_ni)
      (rd_we_i && !$isunknown(rd_addr_i)) |-> rd_addr_in_range;
  endproperty

  assert property (p_zero_reg_constant)
    else $fatal(1, "[rv32i_register_file] x0 register changed from zero");

  assert property (p_ignore_zero_reg_writes)
    else $fatal(1, "[rv32i_register_file] write enable modified x0");

  assert property (p_addresses_in_range)
    else $fatal(1, "[rv32i_register_file] write address %0d outside depth %0d", rd_addr_i, DEPTH_P);

`endif

endmodule : rv32i_register_file
