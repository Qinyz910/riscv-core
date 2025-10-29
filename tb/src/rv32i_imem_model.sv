// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_tb_pkg::*;

module rv32i_imem_model #(
  parameter string NAME = "imem",
  parameter int unsigned MEM_DEPTH_WORDS = 4096
) (
  input  logic         clk_i,
  input  logic         rst_ni,
  input  logic         req_i,
  output logic         gnt_o,
  input  logic [31:0]  addr_i,
  output logic         rvalid_o,
  output logic [31:0]  rdata_o
);

  localparam int unsigned ADDR_LSB = 2;
  localparam int unsigned ADDR_WIDTH = (MEM_DEPTH_WORDS > 1) ? $clog2(MEM_DEPTH_WORDS) : 1;

  logic [31:0] mem [0:MEM_DEPTH_WORDS-1];

  logic                        req_q;
  logic [ADDR_WIDTH-1:0]       index_d;
  logic [ADDR_WIDTH-1:0]       index_q;

  assign gnt_o = req_i;

  function automatic bit addr_aligned(input logic [31:0] addr);
    return (addr[ADDR_LSB-1:0] == '0);
  endfunction

  function automatic bit file_exists(input string path);
    int fd;
    fd = $fopen(path, "r");
    if (fd != 0) begin
      $fclose(fd);
      return 1;
    end
    return 0;
  endfunction

  task automatic load_hex(input string path);
    if (path.len() == 0) begin
      $display("[%s] No program image provided; leaving instruction memory unchanged", NAME);
      return;
    end
    if (!file_exists(path)) begin
      $fatal(1, "[%s] Unable to open program image '%s'", NAME, path);
    end
    $display("[%s] Loading program image '%s'", NAME, path);
    $readmemh(path, mem);
  endtask

  task automatic clear_memory(input logic [31:0] value = 32'h00000013);
    for (int unsigned idx = 0; idx < MEM_DEPTH_WORDS; idx++) begin
      mem[idx] = value;
    end
  endtask

  initial begin
    clear_memory(32'h00000013); // NOPs by default
    req_q    = 1'b0;
    rvalid_o = 1'b0;
    rdata_o  = '0;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      req_q    <= 1'b0;
      rvalid_o <= 1'b0;
      index_q  <= '0;
      rdata_o  <= '0;
    end else begin
      req_q    <= req_i;
      rvalid_o <= req_q;
      if (req_i) begin
        if (!addr_aligned(addr_i)) begin
          $fatal(1, "[%s] Instruction fetch address 0x%08h is not word aligned", NAME, addr_i);
        end
        index_d = addr_i[ADDR_LSB +: ADDR_WIDTH];
        if (index_d >= MEM_DEPTH_WORDS) begin
          $fatal(1, "[%s] Instruction fetch address 0x%08h exceeds memory depth (%0d words)",
                  NAME, addr_i, MEM_DEPTH_WORDS);
        end
        index_q <= index_d;
      end
      if (req_q) begin
        rdata_o <= mem[index_q];
      end
    end
  end

  // Simple protocol assertions to ensure we answer every request exactly once.
  property p_req_ack;
    @(posedge clk_i) disable iff (!rst_ni)
      req_i |-> gnt_o;
  endproperty
  assert property (p_req_ack)
    else $fatal(1, "[%s] Instruction request dropped without grant", NAME);

  property p_response_follows_request;
    @(posedge clk_i) disable iff (!rst_ni)
      rvalid_o |-> req_q;
  endproperty
  assert property (p_response_follows_request)
    else $fatal(1, "[%s] Response asserted without a pending request", NAME);

endmodule : rv32i_imem_model
