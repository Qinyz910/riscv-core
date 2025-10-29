// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_core_pkg::*;

module rv32i_mem_stage (
  input  logic            clk_i,
  input  logic            rst_ni,
  input  logic            ex_valid_i,
  input  ex_mem_payload_t ex_payload_i,
  output logic            ex_hold_o,

  output logic            data_req_o,
  output logic            data_we_o,
  output logic [3:0]      data_be_o,
  output logic [31:0]     data_addr_o,
  output logic [31:0]     data_wdata_o,
  input  logic            data_rvalid_i,
  input  logic [31:0]     data_rdata_i,

  output logic            mem_valid_o,
  output mem_wb_payload_t mem_payload_o
);

  logic                    load_pending_q;
  ex_mem_payload_t          pending_payload_q;
  logic [1:0]               pending_addr_offset_q;
  mem_wb_payload_t          mem_payload_q;
  logic                     mem_valid_q;

  logic                     start_load;
  logic                     start_store;
  logic [1:0]               curr_addr_offset;
  logic [3:0]               curr_store_be;
  logic [31:0]              curr_store_data;

  assign start_load  = ex_valid_i && ex_payload_i.mem_read  && !load_pending_q;
  assign start_store = ex_valid_i && ex_payload_i.mem_write && !load_pending_q;

  assign curr_addr_offset = ex_payload_i.alu_result[1:0];

  always_comb begin
    curr_store_data = 32'h0000_0000;
    if (ex_payload_i.mem_write) begin
      unique case (ex_payload_i.mem_size)
        MEM_SIZE_BYTE: curr_store_data = {{24{1'b0}}, ex_payload_i.rs2_data[7:0]} << (curr_addr_offset << 3);
        MEM_SIZE_HALF: curr_store_data = {{16{1'b0}}, ex_payload_i.rs2_data[15:0]} << (curr_addr_offset << 3);
        default:       curr_store_data = ex_payload_i.rs2_data;
      endcase
    end
  end

  assign curr_store_be = start_store
      ? mem_size_to_be(ex_payload_i.mem_size, curr_addr_offset)
      : 4'b0000;

  function automatic logic [31:0] extend_load_data(
    input mem_size_e size,
    input logic      is_unsigned,
    input logic [31:0] data,
    input logic [1:0] offset
  );
    logic [31:0] shifted;
    logic [7:0]  byte_val;
    logic [15:0] half_val;
    logic [31:0] result;
    shifted  = data >> (offset << 3);
    byte_val = shifted[7:0];
    half_val = shifted[15:0];
    unique case (size)
      MEM_SIZE_BYTE: result = is_unsigned ? {24'h0, byte_val} : {{24{byte_val[7]}}, byte_val};
      MEM_SIZE_HALF: result = is_unsigned ? {16'h0, half_val} : {{16{half_val[15]}}, half_val};
      default:       result = shifted;
    endcase
    return result;
  endfunction

  assign data_req_o   = start_load || start_store;
  assign data_we_o    = start_store;
  assign data_addr_o  = ex_payload_i.alu_result;
  assign data_be_o    = curr_store_be;
  assign data_wdata_o = curr_store_data;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      load_pending_q          <= 1'b0;
      pending_payload_q       <= '0;
      pending_addr_offset_q   <= 2'b00;
      mem_payload_q           <= '0;
      mem_valid_q             <= 1'b0;
    end else begin
      mem_valid_q <= 1'b0;

      if (load_pending_q) begin
        if (data_rvalid_i) begin
          load_pending_q        <= 1'b0;
          mem_valid_q           <= 1'b1;
          mem_payload_q.pc          <= pending_payload_q.pc;
          mem_payload_q.pc_plus4    <= pending_payload_q.pc_plus4;
          mem_payload_q.alu_result  <= pending_payload_q.alu_result;
          mem_payload_q.mem_rdata   <= extend_load_data(
                                         pending_payload_q.mem_size,
                                         pending_payload_q.mem_unsigned,
                                         data_rdata_i,
                                         pending_addr_offset_q
                                       );
          mem_payload_q.rd_addr     <= pending_payload_q.rd_addr;
          mem_payload_q.wb_sel      <= pending_payload_q.wb_sel;
          mem_payload_q.reg_write   <= pending_payload_q.reg_write;
        end
      end else if (ex_valid_i) begin
        if (ex_payload_i.mem_read) begin
          load_pending_q        <= 1'b1;
          pending_payload_q     <= ex_payload_i;
          pending_addr_offset_q <= curr_addr_offset;
        end else begin
          mem_valid_q           <= 1'b1;
          mem_payload_q.pc         <= ex_payload_i.pc;
          mem_payload_q.pc_plus4   <= ex_payload_i.pc_plus4;
          mem_payload_q.alu_result <= ex_payload_i.alu_result;
          mem_payload_q.mem_rdata  <= '0;
          mem_payload_q.rd_addr    <= ex_payload_i.rd_addr;
          mem_payload_q.wb_sel     <= ex_payload_i.wb_sel;
          mem_payload_q.reg_write  <= ex_payload_i.reg_write;
        end
      end
    end
  end


  assign ex_hold_o    = load_pending_q || start_load;
  assign mem_valid_o  = mem_valid_q;
  assign mem_payload_o= mem_payload_q;

endmodule : rv32i_mem_stage
