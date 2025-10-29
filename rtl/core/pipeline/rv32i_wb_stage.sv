// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_core_pkg::*;

module rv32i_wb_stage (
  input  logic            mem_valid_i,
  input  mem_wb_payload_t mem_payload_i,
  output logic            rd_we_o,
  output logic [4:0]      rd_addr_o,
  output logic [31:0]     rd_wdata_o
);

  logic [31:0] wb_data;

  always_comb begin
    unique case (mem_payload_i.wb_sel)
      WB_FROM_MEM: wb_data = mem_payload_i.mem_rdata;
      WB_FROM_PC4: wb_data = mem_payload_i.pc_plus4;
      default:     wb_data = mem_payload_i.alu_result;
    endcase
  end

  assign rd_we_o    = mem_valid_i && mem_payload_i.reg_write && (mem_payload_i.rd_addr != 5'd0);
  assign rd_addr_o  = mem_payload_i.rd_addr;
  assign rd_wdata_o = wb_data;

endmodule : rv32i_wb_stage
