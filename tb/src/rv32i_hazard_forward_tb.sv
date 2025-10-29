// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_control_pkg::*;

module rv32i_hazard_forward_tb;

  localparam time CLK_PERIOD = 10ns;

  logic clk;
  logic rst_ni;

  // Hazard unit inputs
  logic [4:0] id_rs1_addr;
  logic [4:0] id_rs2_addr;
  logic [4:0] ex_rd_addr;
  logic       ex_regwrite;
  logic       ex_memread;
  logic [2:0] pipeline_valid;
  logic       branch_flush;
  logic       structural_hazard;
  logic       hazard_stall;
  logic       hazard_flush;

  // Forwarding unit inputs/outputs
  logic [4:0] ex_rs1_addr;
  logic [4:0] ex_rs2_addr;
  logic [4:0] mem_rd_addr;
  logic       mem_regwrite;
  logic [4:0] wb_rd_addr;
  logic       wb_regwrite;
  logic [1:0] forward_a_sel;
  logic [1:0] forward_b_sel;

  rv32i_hazard_unit #(
    .ENABLE_ASSERTIONS(1'b1)
  ) hazard_i (
    .clk_i               (clk),
    .rst_ni              (rst_ni),
    .id_rs1_addr_i       (id_rs1_addr),
    .id_rs2_addr_i       (id_rs2_addr),
    .ex_rd_addr_i        (ex_rd_addr),
    .ex_regwrite_i       (ex_regwrite),
    .ex_memread_i        (ex_memread),
    .pipeline_valid_i    (pipeline_valid),
    .branch_flush_i      (branch_flush),
    .structural_hazard_i (structural_hazard),
    .stall_o             (hazard_stall),
    .flush_o             (hazard_flush)
  );

  rv32i_forwarding_unit forwarding_i (
    .ex_rs1_addr_i   (ex_rs1_addr),
    .ex_rs2_addr_i   (ex_rs2_addr),
    .mem_rd_addr_i   (mem_rd_addr),
    .mem_regwrite_i  (mem_regwrite),
    .wb_rd_addr_i    (wb_rd_addr),
    .wb_regwrite_i   (wb_regwrite),
    .forward_a_sel_o (forward_a_sel),
    .forward_b_sel_o (forward_b_sel)
  );

  // Clock generation
  initial begin
    clk = 1'b0;
    forever #(CLK_PERIOD/2) clk = ~clk;
  end

  // Reset generation
  initial begin
    rst_ni = 1'b0;
    repeat (2) @(posedge clk);
    rst_ni = 1'b1;
  end

  task automatic check(input string name, input bit condition);
    if (!condition) begin
      $fatal(1, "[hazard_forward_tb] %s", name);
    end else begin
      $display("[hazard_forward_tb] PASS: %s", name);
    end
  endtask

  initial begin
    id_rs1_addr       = '0;
    id_rs2_addr       = '0;
    ex_rd_addr        = '0;
    ex_regwrite       = 1'b0;
    ex_memread        = 1'b0;
    pipeline_valid    = 3'b000;
    branch_flush      = 1'b0;
    structural_hazard = 1'b0;

    ex_rs1_addr   = '0;
    ex_rs2_addr   = '0;
    mem_rd_addr   = '0;
    mem_regwrite  = 1'b0;
    wb_rd_addr    = '0;
    wb_regwrite   = 1'b0;

    @(posedge rst_ni);
    @(posedge clk);

    check("no hazard by default", hazard_stall == 1'b0 && hazard_flush == 1'b0);

    // Load-use hazard on RS1 triggers stall
    id_rs1_addr    = 5'd5;
    pipeline_valid = 3'b011; // ID and EX valid
    ex_rd_addr     = 5'd5;
    ex_regwrite    = 1'b1;
    ex_memread     = 1'b1;
    @(posedge clk);
    check("load-use hazard triggers stall", hazard_stall == 1'b1 && hazard_flush == 1'b0);

    // Branch flush overrides stall request
    branch_flush = 1'b1;
    @(posedge clk);
    check("branch flush overrides stall", hazard_stall == 1'b0 && hazard_flush == 1'b1);
    branch_flush = 1'b0;

    // Structural hazard request
    ex_memread        = 1'b0;
    ex_regwrite       = 1'b0;
    ex_rd_addr        = 5'd0;
    structural_hazard = 1'b1;
    @(posedge clk);
    check("structural hazard triggers stall", hazard_stall == 1'b1 && hazard_flush == 1'b0);
    structural_hazard = 1'b0;
    pipeline_valid    = 3'b000;

    // Forwarding: MEM provides RS1, WB provides RS2
    ex_rs1_addr  = 5'd2;
    ex_rs2_addr  = 5'd3;
    mem_rd_addr  = 5'd2;
    mem_regwrite = 1'b1;
    wb_rd_addr   = 5'd3;
    wb_regwrite  = 1'b1;
    @(posedge clk);
    check("forward A selects MEM", forward_a_sel == FORWARD_FROM_MEM);
    check("forward B selects WB", forward_b_sel == FORWARD_FROM_WB);

    // MEM priority when both match
    wb_rd_addr = 5'd2;
    @(posedge clk);
    check("MEM priority over WB for operand A", forward_a_sel == FORWARD_FROM_MEM);

    // WB only scenario
    mem_regwrite = 1'b0;
    wb_rd_addr   = 5'd3;
    wb_regwrite  = 1'b1;
    @(posedge clk);
    check("WB forwarding when MEM inactive", forward_b_sel == FORWARD_FROM_WB);

    // No forwarding required
    wb_regwrite  = 1'b0;
    ex_rs1_addr  = 5'd10;
    ex_rs2_addr  = 5'd11;
    @(posedge clk);
    check("no forwarding when addresses differ", forward_a_sel == FORWARD_NONE && forward_b_sel == FORWARD_NONE);

    $display("[hazard_forward_tb] All hazard and forwarding scenarios passed");
    #5 $finish;
  end

endmodule : rv32i_hazard_forward_tb
