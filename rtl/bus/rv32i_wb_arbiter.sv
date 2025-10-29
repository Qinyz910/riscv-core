// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_wb_pkg::*;

module rv32i_wb_arbiter #(
  parameter int unsigned ADDR_WIDTH = WB_ADDR_WIDTH,
  parameter int unsigned DATA_WIDTH = WB_DATA_WIDTH
) (
  input  logic                     clk_i,
  input  logic                     rst_ni,

  // Instruction side master
  input  logic                     instr_cyc_i,
  input  logic                     instr_stb_i,
  input  logic                     instr_we_i,
  input  logic [DATA_WIDTH/8-1:0]  instr_sel_i,
  input  logic [ADDR_WIDTH-1:0]    instr_adr_i,
  input  logic [DATA_WIDTH-1:0]    instr_dat_i,
  output logic [DATA_WIDTH-1:0]    instr_dat_o,
  output logic                     instr_ack_o,
  output logic                     instr_err_o,
  output logic                     instr_stall_o,

  // Data side master (priority over instruction)
  input  logic                     data_cyc_i,
  input  logic                     data_stb_i,
  input  logic                     data_we_i,
  input  logic [DATA_WIDTH/8-1:0]  data_sel_i,
  input  logic [ADDR_WIDTH-1:0]    data_adr_i,
  input  logic [DATA_WIDTH-1:0]    data_dat_i,
  output logic [DATA_WIDTH-1:0]    data_dat_o,
  output logic                     data_ack_o,
  output logic                     data_err_o,
  output logic                     data_stall_o,

  // Combined bus toward downstream fabric
  output logic                     bus_cyc_o,
  output logic                     bus_stb_o,
  output logic                     bus_we_o,
  output logic [DATA_WIDTH/8-1:0]  bus_sel_o,
  output logic [ADDR_WIDTH-1:0]    bus_adr_o,
  output logic [DATA_WIDTH-1:0]    bus_dat_o,
  input  logic [DATA_WIDTH-1:0]    bus_dat_i,
  input  logic                     bus_ack_i,
  input  logic                     bus_err_i,
  input  logic                     bus_stall_i
);

  typedef enum logic [1:0] {
    GRANT_NONE  = 2'b00,
    GRANT_INSTR = 2'b01,
    GRANT_DATA  = 2'b10
  } grant_e;

  grant_e grant_q;
  logic   instr_req;
  logic   data_req;

  assign instr_req = instr_cyc_i && instr_stb_i;
  assign data_req  = data_cyc_i  && data_stb_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      grant_q <= GRANT_NONE;
    end else begin
      case (grant_q)
        GRANT_NONE: begin
          if (data_req) begin
            grant_q <= GRANT_DATA;
          end else if (instr_req) begin
            grant_q <= GRANT_INSTR;
          end
        end
        GRANT_INSTR: begin
          if ((!instr_req) || (bus_ack_i || bus_err_i)) begin
            grant_q <= GRANT_NONE;
          end
        end
        GRANT_DATA: begin
          if ((!data_req) || (bus_ack_i || bus_err_i)) begin
            grant_q <= GRANT_NONE;
          end
        end
        default: grant_q <= GRANT_NONE;
      endcase
    end
  end

  // Drive shared bus from the granted master.
  always_comb begin
    bus_cyc_o = 1'b0;
    bus_stb_o = 1'b0;
    bus_we_o  = 1'b0;
    bus_sel_o = '0;
    bus_adr_o = '0;
    bus_dat_o = '0;
    unique case (grant_q)
      GRANT_INSTR: begin
        bus_cyc_o = instr_cyc_i;
        bus_stb_o = instr_stb_i;
        bus_we_o  = instr_we_i;
        bus_sel_o = instr_sel_i;
        bus_adr_o = instr_adr_i;
        bus_dat_o = instr_dat_i;
      end
      GRANT_DATA: begin
        bus_cyc_o = data_cyc_i;
        bus_stb_o = data_stb_i;
        bus_we_o  = data_we_i;
        bus_sel_o = data_sel_i;
        bus_adr_o = data_adr_i;
        bus_dat_o = data_dat_i;
      end
      default: ;
    endcase
  end

  // Route responses back to the granted master.
  assign instr_dat_o   = bus_dat_i;
  assign instr_ack_o   = (grant_q == GRANT_INSTR) ? bus_ack_i  : 1'b0;
  assign instr_err_o   = (grant_q == GRANT_INSTR) ? bus_err_i  : 1'b0;
  assign instr_stall_o = (grant_q == GRANT_INSTR) ? bus_stall_i : instr_req;

  assign data_dat_o    = bus_dat_i;
  assign data_ack_o    = (grant_q == GRANT_DATA) ? bus_ack_i  : 1'b0;
  assign data_err_o    = (grant_q == GRANT_DATA) ? bus_err_i  : 1'b0;
  assign data_stall_o  = (grant_q == GRANT_DATA) ? bus_stall_i : data_req;

  // ---------------------------------------------------------------------------
  // Assertions
  // ---------------------------------------------------------------------------

  property p_exclusive_grant;
    @(posedge clk_i) disable iff (!rst_ni)
      (grant_q == GRANT_INSTR) |-> !data_req;
  endproperty
  assert property (p_exclusive_grant)
    else $warning("[rv32i_wb_arbiter] Data request observed while instruction port granted; request will wait");

  property p_ack_requires_grant;
    @(posedge clk_i) disable iff (!rst_ni)
      (bus_ack_i || bus_err_i) |-> (grant_q != GRANT_NONE);
  endproperty
  assert property (p_ack_requires_grant)
    else $fatal(1, "[rv32i_wb_arbiter] Response returned with no active grant");

endmodule : rv32i_wb_arbiter
