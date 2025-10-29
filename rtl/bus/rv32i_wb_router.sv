// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_wb_pkg::*;

module rv32i_wb_router #(
  parameter int unsigned ADDR_WIDTH      = WB_ADDR_WIDTH,
  parameter int unsigned DATA_WIDTH      = WB_DATA_WIDTH,
  parameter logic [ADDR_WIDTH-1:0] IMEM_BASE_ADDR = 'h0000_0000,
  parameter int unsigned          IMEM_DEPTH_WORDS = 4096,
  parameter logic [ADDR_WIDTH-1:0] DMEM_BASE_ADDR = 'h8000_0000,
  parameter int unsigned          DMEM_DEPTH_WORDS = 4096
) (
  input  logic                     clk_i,
  input  logic                     rst_ni,

  // Master-facing Wishbone port
  input  logic                     m_cyc_i,
  input  logic                     m_stb_i,
  input  logic                     m_we_i,
  input  logic [DATA_WIDTH/8-1:0]  m_sel_i,
  input  logic [ADDR_WIDTH-1:0]    m_adr_i,
  input  logic [DATA_WIDTH-1:0]    m_dat_i,
  output logic [DATA_WIDTH-1:0]    m_dat_o,
  output logic                     m_ack_o,
  output logic                     m_err_o,
  output logic                     m_stall_o,

  // Instruction memory (ROM) slave port
  output logic                     imem_cyc_o,
  output logic                     imem_stb_o,
  output logic                     imem_we_o,
  output logic [DATA_WIDTH/8-1:0]  imem_sel_o,
  output logic [ADDR_WIDTH-1:0]    imem_adr_o,
  output logic [DATA_WIDTH-1:0]    imem_dat_o,
  input  logic [DATA_WIDTH-1:0]    imem_dat_i,
  input  logic                     imem_ack_i,
  input  logic                     imem_err_i,
  input  logic                     imem_stall_i,

  // Data memory (RAM) slave port
  output logic                     dmem_cyc_o,
  output logic                     dmem_stb_o,
  output logic                     dmem_we_o,
  output logic [DATA_WIDTH/8-1:0]  dmem_sel_o,
  output logic [ADDR_WIDTH-1:0]    dmem_adr_o,
  output logic [DATA_WIDTH-1:0]    dmem_dat_o,
  input  logic [DATA_WIDTH-1:0]    dmem_dat_i,
  input  logic                     dmem_ack_i,
  input  logic                     dmem_err_i,
  input  logic                     dmem_stall_i
);

  localparam int unsigned BYTES_PER_WORD = DATA_WIDTH/8;
  localparam longint unsigned IMEM_SIZE_BYTES = IMEM_DEPTH_WORDS * BYTES_PER_WORD;
  localparam longint unsigned DMEM_SIZE_BYTES = DMEM_DEPTH_WORDS * BYTES_PER_WORD;

  typedef enum logic [1:0] {
    TARGET_NONE    = 2'b00,
    TARGET_IMEM    = 2'b01,
    TARGET_DMEM    = 2'b10,
    TARGET_INVALID = 2'b11
  } target_e;

  target_e target_q;
  logic    pending_q;
  logic    invalid_pending_q;
  logic    invalid_ack_q;

  function automatic target_e decode_target(input logic [ADDR_WIDTH-1:0] addr);
    longint unsigned addr_u;
    longint unsigned imem_base_u;
    longint unsigned dmem_base_u;
    addr_u      = longint unsigned'(addr);
    imem_base_u = longint unsigned'(IMEM_BASE_ADDR);
    dmem_base_u = longint unsigned'(DMEM_BASE_ADDR);
    if ((addr_u >= imem_base_u) && (addr_u < (imem_base_u + IMEM_SIZE_BYTES))) begin
      return TARGET_IMEM;
    end
    if ((addr_u >= dmem_base_u) && (addr_u < (dmem_base_u + DMEM_SIZE_BYTES))) begin
      return TARGET_DMEM;
    end
    return TARGET_INVALID;
  endfunction

  target_e target_sel;

  always_comb begin
    if (pending_q) begin
      target_sel = target_q;
    end else if (invalid_pending_q) begin
      target_sel = TARGET_INVALID;
    end else if (m_cyc_i && m_stb_i) begin
      target_sel = decode_target(m_adr_i);
    end else begin
      target_sel = TARGET_NONE;
    end
  end

  logic selected_imem;
  logic selected_dmem;
  assign selected_imem = (target_sel == TARGET_IMEM);
  assign selected_dmem = (target_sel == TARGET_DMEM);

  // Stall back-pressure propagates from the selected slave. Invalid regions stall until the
  // synthetic error response is produced.
  assign m_stall_o = (target_sel == TARGET_INVALID) ? invalid_pending_q :
                     (selected_imem ? imem_stall_i :
                      selected_dmem ? dmem_stall_i : 1'b0);

  // Drive the slave ports.
  assign imem_cyc_o = m_cyc_i && selected_imem;
  assign imem_stb_o = m_stb_i && selected_imem;
  assign imem_we_o  = m_we_i;
  assign imem_sel_o = m_sel_i;
  assign imem_adr_o = m_adr_i;
  assign imem_dat_o = m_dat_i;

  assign dmem_cyc_o = m_cyc_i && selected_dmem;
  assign dmem_stb_o = m_stb_i && selected_dmem;
  assign dmem_we_o  = m_we_i;
  assign dmem_sel_o = m_sel_i;
  assign dmem_adr_o = m_adr_i;
  assign dmem_dat_o = m_dat_i;

  logic ack_from_slave;
  logic err_from_slave;
  logic [DATA_WIDTH-1:0] data_from_slave;

  always_comb begin
    ack_from_slave   = 1'b0;
    err_from_slave   = 1'b0;
    data_from_slave  = '0;
    case (target_sel)
      TARGET_IMEM: begin
        ack_from_slave  = imem_ack_i;
        err_from_slave  = imem_err_i;
        data_from_slave = imem_dat_i;
      end
      TARGET_DMEM: begin
        ack_from_slave  = dmem_ack_i;
        err_from_slave  = dmem_err_i;
        data_from_slave = dmem_dat_i;
      end
      default: begin
        ack_from_slave  = 1'b0;
        err_from_slave  = 1'b0;
        data_from_slave = '0;
      end
    endcase
  end

  assign m_dat_o = data_from_slave;
  assign m_ack_o = ack_from_slave || invalid_ack_q;
  assign m_err_o = err_from_slave || invalid_ack_q;

  // Track outstanding requests to ensure only one in flight at a time.
  logic new_request;
  target_e decoded_target;
  logic complete_valid;

  assign decoded_target = decode_target(m_adr_i);
  assign new_request = (!pending_q) && !invalid_pending_q && m_cyc_i && m_stb_i && !m_stall_o;

  assign complete_valid = (target_q == TARGET_IMEM && (imem_ack_i || imem_err_i)) ||
                          (target_q == TARGET_DMEM && (dmem_ack_i || dmem_err_i));

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pending_q         <= 1'b0;
      target_q          <= TARGET_NONE;
      invalid_pending_q <= 1'b0;
      invalid_ack_q     <= 1'b0;
    end else begin
      invalid_ack_q <= invalid_pending_q;

      if (invalid_pending_q) begin
        invalid_pending_q <= 1'b0;
      end

      if (new_request) begin
        if (decoded_target == TARGET_INVALID) begin
          invalid_pending_q <= 1'b1;
          pending_q         <= 1'b0;
          target_q          <= TARGET_NONE;
        end else begin
          pending_q <= 1'b1;
          target_q  <= decoded_target;
        end
      end else if (complete_valid) begin
        pending_q <= 1'b0;
        target_q  <= TARGET_NONE;
      end
    end
  end

  // ---------------------------------------------------------------------------
  // Assertions
  // ---------------------------------------------------------------------------

  property p_no_overlap;
    @(posedge clk_i) disable iff (!rst_ni)
      pending_q |-> !new_request;
  endproperty
  assert property (p_no_overlap)
    else $fatal(1, "[rv32i_wb_router] New request issued while previous transfer is pending");

  property p_invalid_ack_one_shot;
    @(posedge clk_i) disable iff (!rst_ni)
      invalid_ack_q |-> !invalid_pending_q;
  endproperty
  assert property (p_invalid_ack_one_shot)
    else $fatal(1, "[rv32i_wb_router] Invalid-region response glitch detected");

endmodule : rv32i_wb_router
