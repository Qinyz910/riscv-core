// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_tb_pkg::*;

module rv32i_dmem_model #(
  parameter string NAME = "dmem",
  parameter int unsigned MEM_DEPTH_WORDS = 4096
) (
  input  logic         clk_i,
  input  logic         rst_ni,
  input  logic         req_i,
  input  logic         we_i,
  input  logic  [3:0]  be_i,
  input  logic [31:0]  addr_i,
  input  logic [31:0]  wdata_i,
  output logic         rvalid_o,
  output logic [31:0]  rdata_o,
  output logic         store_valid_o,
  output logic [31:0]  store_addr_o,
  output logic [31:0]  store_data_o
);

  localparam int unsigned ADDR_LSB = 2;
  localparam int unsigned ADDR_WIDTH = (MEM_DEPTH_WORDS > 1) ? $clog2(MEM_DEPTH_WORDS) : 1;

  logic [31:0] mem [0:MEM_DEPTH_WORDS-1];

  logic                        req_q;
  logic                        we_q;
  logic  [3:0]                 be_q;
  logic [31:0]                 addr_q;
  logic [31:0]                 wdata_q;
  logic [ADDR_WIDTH-1:0]       index_d;
  logic [ADDR_WIDTH-1:0]       index_q;

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
      return;
    end
    if (!file_exists(path)) begin
      $fatal(1, "[%s] Unable to open data memory image '%s'", NAME, path);
    end
    $display("[%s] Loading data image '%s'", NAME, path);
    $readmemh(path, mem);
  endtask

  task automatic clear_memory(input logic [31:0] value = '0);
    for (int unsigned idx = 0; idx < MEM_DEPTH_WORDS; idx++) begin
      mem[idx] = value;
    end
  endtask

  initial begin
    clear_memory('0);
    req_q          = 1'b0;
    we_q           = 1'b0;
    be_q           = '0;
    addr_q         = '0;
    wdata_q        = '0;
    rvalid_o       = 1'b0;
    rdata_o        = '0;
    store_valid_o  = 1'b0;
    store_addr_o   = '0;
    store_data_o   = '0;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      req_q         <= 1'b0;
      we_q          <= 1'b0;
      be_q          <= '0;
      addr_q        <= '0;
      wdata_q       <= '0;
      index_q       <= '0;
      rvalid_o      <= 1'b0;
      rdata_o       <= '0;
      store_valid_o <= 1'b0;
      store_addr_o  <= '0;
      store_data_o  <= '0;
    end else begin
      req_q    <= req_i;
      we_q     <= we_i;
      be_q     <= be_i;
      addr_q   <= addr_i;
      wdata_q  <= wdata_i;

      rvalid_o      <= req_q && !we_q;
      store_valid_o <= req_q && we_q;

      if (req_i) begin
        if (!addr_aligned(addr_i)) begin
          $fatal(1, "[%s] Data access address 0x%08h is not word aligned", NAME, addr_i);
        end
        index_d = addr_i[ADDR_LSB +: ADDR_WIDTH];
        if (index_d >= MEM_DEPTH_WORDS) begin
          $fatal(1, "[%s] Data address 0x%08h exceeds memory depth (%0d words)", NAME, addr_i, MEM_DEPTH_WORDS);
        end
        index_q <= index_d;
      end

      if (req_q) begin
        logic [31:0] word_q;
        logic [31:0] updated_word;
        word_q = mem[index_q];
        updated_word = word_q;
        if (we_q) begin
          for (int b = 0; b < 4; b++) begin
            if (be_q[b]) begin
              updated_word[b*8 +: 8] = wdata_q[b*8 +: 8];
            end
          end
          mem[index_q] <= updated_word;
          store_addr_o <= addr_q;
          store_data_o <= updated_word;
        end else begin
          rdata_o <= word_q;
        end
      end


    end
  end

  // Assertions to flag suspicious protocol behaviour.
  property p_load_response;
    @(posedge clk_i) disable iff (!rst_ni)
      (req_i && !we_i) |-> ##1 rvalid_o;
  endproperty
  assert property (p_load_response)
    else $fatal(1, "[%s] Load request did not receive a response", NAME);

  property p_store_eventually_seen;
    @(posedge clk_i) disable iff (!rst_ni)
      (req_i && we_i) |-> ##1 store_valid_o;
  endproperty
  assert property (p_store_eventually_seen)
    else $fatal(1, "[%s] Store request did not produce a commit event", NAME);

endmodule : rv32i_dmem_model
