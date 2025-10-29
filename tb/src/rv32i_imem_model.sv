// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_wb_pkg::*;

module rv32i_imem_model #(
  parameter string      NAME                = "imem",
  parameter int unsigned MEM_DEPTH_WORDS    = 4096,
  parameter logic [31:0] BASE_ADDR          = 32'h0000_0000,
  parameter int unsigned FIXED_WAIT_CYCLES  = 0,
  parameter bit          ENABLE_RANDOM_WAIT = 1'b0,
  parameter int unsigned RANDOM_WAIT_MAX    = 0,
  parameter logic [31:0] RANDOM_SEED        = 32'h1
) (
  input  logic         clk_i,
  input  logic         rst_ni,
  input  logic         wb_cyc_i,
  input  logic         wb_stb_i,
  input  logic         wb_we_i,
  input  logic [WB_SEL_WIDTH-1:0] wb_sel_i,
  input  logic [WB_ADDR_WIDTH-1:0] wb_adr_i,
  input  logic [WB_DATA_WIDTH-1:0] wb_dat_i,
  output logic [WB_DATA_WIDTH-1:0] wb_dat_o,
  output logic         wb_ack_o,
  output logic         wb_err_o,
  output logic         wb_stall_o
);

  localparam int unsigned ADDR_LSB          = $clog2(WB_DATA_WIDTH/8);
  localparam int unsigned ADDR_WIDTH_WORDS  = (MEM_DEPTH_WORDS > 1) ? $clog2(MEM_DEPTH_WORDS) : 1;
  localparam int unsigned MAX_WAIT_CYCLES   = FIXED_WAIT_CYCLES + (ENABLE_RANDOM_WAIT ? RANDOM_WAIT_MAX : 0);
  localparam int unsigned WAIT_COUNTER_WIDTH = (MAX_WAIT_CYCLES > 0) ? $clog2(MAX_WAIT_CYCLES + 1) : 1;
  localparam int unsigned BYTES_PER_WORD    = WB_DATA_WIDTH / 8;

  logic [WB_DATA_WIDTH-1:0] mem [0:MEM_DEPTH_WORDS-1];

  // Unused Wishbone write-path inputs are tied off but tracked to avoid lint warnings.
  logic unused_write_path;
  assign unused_write_path = ^{1'b0, wb_sel_i, wb_dat_i};

  logic pending_q;
  logic [ADDR_WIDTH_WORDS-1:0] index_q;
  logic [WAIT_COUNTER_WIDTH-1:0] wait_counter_q;
  logic                        ack_q;
  logic [WB_DATA_WIDTH-1:0]     rdata_q;
  logic [31:0]                  prng_q;

  assign wb_dat_o   = rdata_q;
  assign wb_ack_o   = ack_q;
  assign wb_err_o   = 1'b0;
  assign wb_stall_o = pending_q;

  function automatic bit addr_aligned(input logic [WB_ADDR_WIDTH-1:0] addr);
    return (addr[ADDR_LSB-1:0] == '0);
  endfunction

  function automatic logic [31:0] prng_next(input logic [31:0] current);
    logic feedback;
    feedback = current[31] ^ current[21] ^ current[1] ^ current[0];
    return {current[30:0], feedback};
  endfunction

  task automatic clear_memory(input logic [WB_DATA_WIDTH-1:0] value = 32'h0000_0013);
    for (int unsigned idx = 0; idx < MEM_DEPTH_WORDS; idx++) begin
      mem[idx] = value;
    end
  endtask

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

  initial begin
    clear_memory(32'h0000_0013);
    pending_q        = 1'b0;
    wait_counter_q   = '0;
    ack_q            = 1'b0;
    rdata_q          = '0;
    prng_q           = (RANDOM_SEED != '0) ? RANDOM_SEED : 32'h1;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pending_q      <= 1'b0;
      index_q        <= '0;
      wait_counter_q <= '0;
      ack_q          <= 1'b0;
      rdata_q        <= '0;
      prng_q         <= (RANDOM_SEED != '0) ? RANDOM_SEED : 32'h1;
    end else begin
      ack_q <= 1'b0;

      if (!pending_q) begin
        if (wb_cyc_i && wb_stb_i) begin
          if (wb_we_i) begin
            $fatal(1, "[%s] Wishbone write attempted against ROM at address 0x%08h", NAME, wb_adr_i);
          end
          if (!addr_aligned(wb_adr_i)) begin
            $fatal(1, "[%s] Instruction fetch address 0x%08h is not aligned", NAME, wb_adr_i);
          end

          longint unsigned addr_u;
          longint unsigned base_u;
          longint unsigned offset_u;
          addr_u   = longint unsigned'(wb_adr_i);
          base_u   = longint unsigned'(BASE_ADDR);
          if (addr_u < base_u) begin
            $fatal(1, "[%s] Instruction fetch address 0x%08h below base 0x%08h", NAME, wb_adr_i, BASE_ADDR);
          end
          offset_u = addr_u - base_u;
          if (offset_u >= (MEM_DEPTH_WORDS * BYTES_PER_WORD)) begin
            $fatal(1, "[%s] Instruction fetch address 0x%08h exceeds depth (%0d words)", NAME, wb_adr_i, MEM_DEPTH_WORDS);
          end
          index_q <= logic [ADDR_WIDTH_WORDS-1:0]'(offset_u >> ADDR_LSB);

          int unsigned wait_value;
          wait_value = FIXED_WAIT_CYCLES;
          if (ENABLE_RANDOM_WAIT) begin
            logic [31:0] prng_nxt;
            prng_nxt = prng_next(prng_q);
            prng_q   <= prng_nxt;
            if (RANDOM_WAIT_MAX != 0) begin
              wait_value = wait_value + (prng_nxt % (RANDOM_WAIT_MAX + 1));
            end
          end
          wait_counter_q <= logic [WAIT_COUNTER_WIDTH-1:0]'(wait_value);
          pending_q      <= 1'b1;
        end
      end else begin
        if (wait_counter_q != '0) begin
          wait_counter_q <= wait_counter_q - 1'b1;
        end else begin
          rdata_q   <= mem[index_q];
          ack_q     <= 1'b1;
          pending_q <= 1'b0;
        end
      end
    end
  end

  // ---------------------------------------------------------------------------
  // Assertions
  // ---------------------------------------------------------------------------

  property p_ack_implies_access;
    @(posedge clk_i) disable iff (!rst_ni)
      ack_q |-> (wb_cyc_i && wb_stb_i);
  endproperty
  assert property (p_ack_implies_access)
    else $fatal(1, "[%s] Acknowledge without active request", NAME);

endmodule : rv32i_imem_model
