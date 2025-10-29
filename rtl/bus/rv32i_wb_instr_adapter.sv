// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_wb_pkg::*;

module rv32i_wb_instr_adapter #(
  parameter int unsigned ADDR_WIDTH = WB_ADDR_WIDTH,
  parameter int unsigned DATA_WIDTH = WB_DATA_WIDTH
) (
  input  logic                     clk_i,
  input  logic                     rst_ni,

  // Pipeline side (IF stage)
  input  logic                     req_i,
  input  logic [ADDR_WIDTH-1:0]    addr_i,
  output logic                     gnt_o,
  output logic                     rsp_valid_o,
  output logic [DATA_WIDTH-1:0]    rsp_rdata_o,
  output logic                     rsp_err_o,

  // Wishbone master interface
  output logic                     wb_cyc_o,
  output logic                     wb_stb_o,
  output logic                     wb_we_o,
  output logic [DATA_WIDTH/8-1:0]  wb_sel_o,
  output logic [ADDR_WIDTH-1:0]    wb_adr_o,
  output logic [DATA_WIDTH-1:0]    wb_dat_o,
  input  logic [DATA_WIDTH-1:0]    wb_dat_i,
  input  logic                     wb_ack_i,
  input  logic                     wb_err_i,
  input  logic                     wb_stall_i
);

  logic                       pending_q;
  logic [ADDR_WIDTH-1:0]      addr_q;
  logic                       rsp_valid_q;
  logic [DATA_WIDTH-1:0]      rsp_rdata_q;
  logic                       rsp_err_q;

  logic accept_req;
  logic complete_transfer;

  assign accept_req       = (!pending_q) && req_i && !wb_stall_i;
  assign complete_transfer = pending_q && (wb_ack_i || wb_err_i);

  // Grant pulses when we capture the request.
  assign gnt_o = accept_req;

  // Wishbone command signals remain asserted while a request is pending.
  assign wb_cyc_o  = pending_q;
  assign wb_stb_o  = pending_q;
  assign wb_we_o   = 1'b0;
  assign wb_sel_o  = {DATA_WIDTH/8{1'b1}};
  assign wb_adr_o  = addr_q;
  assign wb_dat_o  = '0;

  // Response output registers
  assign rsp_valid_o = rsp_valid_q;
  assign rsp_rdata_o = rsp_rdata_q;
  assign rsp_err_o   = rsp_err_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pending_q     <= 1'b0;
      addr_q        <= '0;
      rsp_valid_q   <= 1'b0;
      rsp_rdata_q   <= '0;
      rsp_err_q     <= 1'b0;
    end else begin
      rsp_valid_q <= 1'b0;
      if (accept_req) begin
        pending_q <= 1'b1;
        addr_q    <= addr_i;
      end else if (complete_transfer) begin
        pending_q   <= 1'b0;
        rsp_valid_q <= 1'b1;
        rsp_rdata_q <= wb_dat_i;
        rsp_err_q   <= wb_err_i;
      end
    end
  end

  // ---------------------------------------------------------------------------
  // Assertions
  // ---------------------------------------------------------------------------

  // No new request should be accepted while one is already pending.
  property p_no_overlap;
    @(posedge clk_i) disable iff (!rst_ni)
      pending_q |-> !accept_req;
  endproperty
  assert property (p_no_overlap)
    else $fatal(1, "[rv32i_wb_instr_adapter] Overlapping fetch requests detected");

  // Wishbone acknowledgment must only occur when a command is active.
  property p_ack_only_when_pending;
    @(posedge clk_i) disable iff (!rst_ni)
      (wb_ack_i || wb_err_i) |-> pending_q;
  endproperty
  assert property (p_ack_only_when_pending)
    else $fatal(1, "[rv32i_wb_instr_adapter] Response observed without an active transaction");

endmodule : rv32i_wb_instr_adapter
