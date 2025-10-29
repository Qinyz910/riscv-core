// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_core_pkg::*;

/*
 * --------------------------------------------------------------------------
 * rv32i_core: five-stage in-order pipeline
 * --------------------------------------------------------------------------
 *
 *   IF  -> IF/ID -> ID -> ID/EX -> EX -> EX/MEM -> MEM -> MEM/WB -> WB
 *    |                ^                     |                        |
 *    |                |                     |                        |
 *    |                '----- register file (read)         register file (write)
 *    '----- branch/jump redirects from EX ----- pipeline hold requests from MEM
 *
 * Control flow is resolved in the EX stage; branch or jump redirects flush the
 * IF and ID stages while updating the program counter in IF.  The MEM stage
 * raises a hold request when waiting on a load response, back-pressuring earlier
 * stages so the pipeline can stall cleanly without losing state.
 */
module rv32i_core #(
  parameter logic [31:0] RESET_VECTOR = 32'h0000_0000
) (
  input  logic        clk_i,
  input  logic        rst_ni,

  output logic        instr_req_o,
  input  logic        instr_gnt_i,
  input  logic        instr_rvalid_i,
  output logic [31:0] instr_addr_o,
  input  logic [31:0] instr_rdata_i,

  output logic        data_req_o,
  output logic        data_we_o,
  output logic [3:0]  data_be_o,
  output logic [31:0] data_addr_o,
  output logic [31:0] data_wdata_o,
  input  logic        data_rvalid_i,
  input  logic [31:0] data_rdata_i,

  input  logic        irq_timer_i,
  input  logic        irq_external_i,
  input  logic        irq_soft_i,
  input  logic        dbg_req_i,
  output logic        dbg_halted_o
);

  // Instruction fetch stage signals
  logic             if_fetch_valid;
  logic [31:0]      if_fetch_pc;
  logic [31:0]      if_fetch_instr;
  logic             instr_req;
  logic [31:0]      instr_addr;

  // IF/ID pipeline register
  logic             if_id_valid;
  if_id_payload_t   if_id_payload;

  // ID stage and register file
  logic             id_stage_valid;
  id_ex_payload_t   id_stage_payload;
  logic [4:0]       id_rs1_addr;
  logic [4:0]       id_rs2_addr;
  logic [31:0]      rf_rs1_data;
  logic [31:0]      rf_rs2_data;

  // ID/EX pipeline register
  logic             id_ex_valid;
  id_ex_payload_t   id_ex_payload;

  // EX stage
  logic             ex_stage_valid;
  ex_mem_payload_t  ex_stage_payload;
  logic             branch_taken;
  logic [31:0]      branch_target;

  // EX/MEM pipeline register
  logic             ex_mem_valid;
  ex_mem_payload_t  ex_mem_payload;

  // MEM stage
  logic             mem_stage_valid;
  mem_wb_payload_t  mem_stage_payload;
  logic             ex_stage_hold;
  logic             data_req;
  logic             data_we;
  logic [3:0]       data_be;
  logic [31:0]      data_addr;
  logic [31:0]      data_wdata;

  // MEM/WB pipeline register
  logic             mem_wb_valid;
  mem_wb_payload_t  mem_wb_payload;

  // WB stage / register file write-back
  logic             wb_rd_we;
  logic [4:0]       wb_rd_addr;
  logic [31:0]      wb_rd_wdata;

  // Global pipeline hold derived from MEM stage back-pressure
  logic             pipeline_hold;
  logic             pipeline_flush_if;
  logic             pipeline_flush_id;

  // ---------------------------------------------------------------------------
  // Instruction Fetch
  // ---------------------------------------------------------------------------

  rv32i_if_stage #(
    .RESET_PC (RESET_VECTOR)
  ) if_stage_i (
    .clk_i          (clk_i),
    .rst_ni         (rst_ni),
    .stall_i        (pipeline_hold),
    .flush_i        (pipeline_flush_if),
    .redirect_i     (branch_taken),
    .redirect_pc_i  (branch_target),
    .instr_req_o    (instr_req),
    .instr_addr_o   (instr_addr),
    .instr_gnt_i    (instr_gnt_i),
    .instr_rvalid_i (instr_rvalid_i),
    .instr_rdata_i  (instr_rdata_i),
    .fetch_valid_o  (if_fetch_valid),
    .fetch_pc_o     (if_fetch_pc),
    .fetch_instr_o  (if_fetch_instr),
    .fetch_ready_i  (!pipeline_hold)
  );

  // IF/ID pipeline register
  rv32i_pipeline_reg #(
    .T(if_id_payload_t)
  ) if_id_reg_i (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .hold_i   (pipeline_hold),
    .flush_i  (pipeline_flush_if),
    .valid_i  (if_fetch_valid),
    .data_i   ('{pc: if_fetch_pc, instr: if_fetch_instr}),
    .valid_o  (if_id_valid),
    .data_o   (if_id_payload)
  );

  // ---------------------------------------------------------------------------
  // Instruction Decode
  // ---------------------------------------------------------------------------

  rv32i_id_stage id_stage_i (
    .if_valid_i    (if_id_valid),
    .if_payload_i  (if_id_payload),
    .id_valid_o    (id_stage_valid),
    .id_payload_o  (id_stage_payload),
    .rf_rs1_addr_o (id_rs1_addr),
    .rf_rs2_addr_o (id_rs2_addr),
    .rf_rs1_data_i (rf_rs1_data),
    .rf_rs2_data_i (rf_rs2_data)
  );

  rv32i_pipeline_reg #(
    .T(id_ex_payload_t)
  ) id_ex_reg_i (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .hold_i   (pipeline_hold),
    .flush_i  (pipeline_flush_id),
    .valid_i  (id_stage_valid),
    .data_i   (id_stage_payload),
    .valid_o  (id_ex_valid),
    .data_o   (id_ex_payload)
  );

  // ---------------------------------------------------------------------------
  // Execute
  // ---------------------------------------------------------------------------

  rv32i_ex_stage ex_stage_i (
    .id_valid_i      (id_ex_valid),
    .id_payload_i    (id_ex_payload),
    .ex_valid_o      (ex_stage_valid),
    .ex_payload_o    (ex_stage_payload),
    .branch_taken_o  (branch_taken),
    .branch_target_o (branch_target)
  );

  rv32i_pipeline_reg #(
    .T(ex_mem_payload_t)
  ) ex_mem_reg_i (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .hold_i   (ex_stage_hold),
    .flush_i  (1'b0),
    .valid_i  (ex_stage_valid),
    .data_i   (ex_stage_payload),
    .valid_o  (ex_mem_valid),
    .data_o   (ex_mem_payload)
  );

  // ---------------------------------------------------------------------------
  // Memory
  // ---------------------------------------------------------------------------

  rv32i_mem_stage mem_stage_i (
    .clk_i         (clk_i),
    .rst_ni        (rst_ni),
    .ex_valid_i    (ex_mem_valid),
    .ex_payload_i  (ex_mem_payload),
    .ex_hold_o     (ex_stage_hold),
    .data_req_o    (data_req),
    .data_we_o     (data_we),
    .data_be_o     (data_be),
    .data_addr_o   (data_addr),
    .data_wdata_o  (data_wdata),
    .data_rvalid_i (data_rvalid_i),
    .data_rdata_i  (data_rdata_i),
    .mem_valid_o   (mem_stage_valid),
    .mem_payload_o (mem_stage_payload)
  );

  rv32i_pipeline_reg #(
    .T(mem_wb_payload_t)
  ) mem_wb_reg_i (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .hold_i   (1'b0),
    .flush_i  (1'b0),
    .valid_i  (mem_stage_valid),
    .data_i   (mem_stage_payload),
    .valid_o  (mem_wb_valid),
    .data_o   (mem_wb_payload)
  );

  // ---------------------------------------------------------------------------
  // Write-back
  // ---------------------------------------------------------------------------

  rv32i_wb_stage wb_stage_i (
    .mem_valid_i  (mem_wb_valid),
    .mem_payload_i(mem_wb_payload),
    .rd_we_o      (wb_rd_we),
    .rd_addr_o    (wb_rd_addr),
    .rd_wdata_o   (wb_rd_wdata)
  );

  // ---------------------------------------------------------------------------
  // Register file
  // ---------------------------------------------------------------------------

  rv32i_register_file rf_i (
    .clk_i       (clk_i),
    .rst_ni      (rst_ni),
    .rs1_addr_i  (id_rs1_addr),
    .rs2_addr_i  (id_rs2_addr),
    .rs1_data_o  (rf_rs1_data),
    .rs2_data_o  (rf_rs2_data),
    .rd_we_i     (wb_rd_we),
    .rd_addr_i   (wb_rd_addr),
    .rd_wdata_i  (wb_rd_wdata)
  );

  // ---------------------------------------------------------------------------
  // Control plumbing
  // ---------------------------------------------------------------------------

  assign pipeline_hold     = ex_stage_hold;
  assign pipeline_flush_if = branch_taken;
  assign pipeline_flush_id = branch_taken;

  assign instr_req_o   = instr_req;
  assign instr_addr_o  = instr_addr;

  assign data_req_o    = data_req;
  assign data_we_o     = data_we;
  assign data_be_o     = data_be;
  assign data_addr_o   = data_addr;
  assign data_wdata_o  = data_wdata;

  assign dbg_halted_o  = 1'b0;

endmodule : rv32i_core
