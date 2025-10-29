// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

module rv32i_if_stage #(
  parameter logic [31:0] RESET_PC = 32'h0000_0000
) (
  input  logic        clk_i,
  input  logic        rst_ni,
  input  logic        stall_i,
  input  logic        flush_i,
  input  logic        redirect_i,
  input  logic [31:0] redirect_pc_i,
  output logic        instr_req_o,
  output logic [31:0] instr_addr_o,
  input  logic        instr_gnt_i,
  input  logic        instr_rvalid_i,
  input  logic [31:0] instr_rdata_i,
  output logic        fetch_valid_o,
  output logic [31:0] fetch_pc_o,
  output logic [31:0] fetch_instr_o,
  input  logic        fetch_ready_i
);

  logic [31:0] pc_q;
  logic [31:0] issue_pc_q;
  logic        outstanding_q;
  logic        buffer_valid_q;
  logic [31:0] buffer_pc_q;
  logic [31:0] buffer_instr_q;
  logic        drop_response_q;

  logic        request_ok;
  logic        advance_pc;

  assign instr_addr_o = pc_q;

  assign request_ok = !stall_i && !redirect_i && !buffer_valid_q && !outstanding_q;
  assign instr_req_o = request_ok;

  assign fetch_valid_o = buffer_valid_q;
  assign fetch_pc_o    = buffer_pc_q;
  assign fetch_instr_o = buffer_instr_q;

  assign advance_pc = (buffer_valid_q && fetch_ready_i && !stall_i && !redirect_i);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pc_q           <= RESET_PC;
      outstanding_q  <= 1'b0;
      issue_pc_q     <= RESET_PC;
      buffer_valid_q <= 1'b0;
      buffer_pc_q    <= RESET_PC;
      buffer_instr_q <= 32'h00000013; // NOP
      drop_response_q<= 1'b0;
    end else begin
      if (redirect_i) begin
        pc_q <= redirect_pc_i;
      end else if (advance_pc) begin
        pc_q <= pc_q + 32'd4;
      end

      if (request_ok && instr_gnt_i) begin
        outstanding_q <= 1'b1;
        issue_pc_q    <= pc_q;
      end

      if (instr_rvalid_i) begin
        outstanding_q <= 1'b0;
        if (drop_response_q) begin
          drop_response_q <= 1'b0;
        end else begin
          buffer_valid_q <= 1'b1;
          buffer_pc_q    <= issue_pc_q;
          buffer_instr_q <= instr_rdata_i;
        end
      end

      if (flush_i) begin
        buffer_valid_q <= 1'b0;
        if (outstanding_q) begin
          drop_response_q <= 1'b1;
        end
      end

      if (redirect_i) begin
        buffer_valid_q <= 1'b0;
        if (outstanding_q) begin
          drop_response_q <= 1'b1;
        end
      end

      if (buffer_valid_q && fetch_ready_i) begin
        buffer_valid_q <= 1'b0;
      end

      if (!outstanding_q && !drop_response_q && !buffer_valid_q && redirect_i) begin
        drop_response_q <= 1'b0;
      end
    end
  end

endmodule : rv32i_if_stage
