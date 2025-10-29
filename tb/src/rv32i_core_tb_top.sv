// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_tb_pkg::*;
import rv32i_wb_pkg::*;

module rv32i_core_tb_top;

  timeunit 1ns;
  timeprecision 1ps;

  localparam time CLK_PERIOD = 10ns;

  logic clk;
  logic rst_ni;

  // DUT <-> memory interfaces
  logic        instr_req;
  logic        instr_gnt;
  logic        instr_rvalid;
  logic [31:0] instr_addr;
  logic [31:0] instr_rdata;

  logic        data_req;
  logic        data_we;
  logic  [3:0] data_be;
  logic [31:0] data_addr;
  logic [31:0] data_wdata;
  logic        data_rvalid;
  logic [31:0] data_rdata;
  logic        data_gnt;

  logic        dbg_halted;

  // Scoreboard observation signals
  logic        store_valid;
  logic [31:0] store_addr;
  logic [31:0] store_data;

  // Internal Wishbone interconnect wires
  logic        if_wb_cyc;
  logic        if_wb_stb;
  logic        if_wb_we;
  logic [WB_SEL_WIDTH-1:0] if_wb_sel;
  logic [WB_ADDR_WIDTH-1:0] if_wb_adr;
  logic [WB_DATA_WIDTH-1:0] if_wb_wdata;
  logic [WB_DATA_WIDTH-1:0] if_wb_rdata;
  logic        if_wb_ack;
  logic        if_wb_err;
  logic        if_wb_stall;

  logic        mem_wb_cyc;
  logic        mem_wb_stb;
  logic        mem_wb_we;
  logic [WB_SEL_WIDTH-1:0] mem_wb_sel;
  logic [WB_ADDR_WIDTH-1:0] mem_wb_adr;
  logic [WB_DATA_WIDTH-1:0] mem_wb_wdata;
  logic [WB_DATA_WIDTH-1:0] mem_wb_rdata;
  logic        mem_wb_ack;
  logic        mem_wb_err;
  logic        mem_wb_stall;

  logic        wb_bus_cyc;
  logic        wb_bus_stb;
  logic        wb_bus_we;
  logic [WB_SEL_WIDTH-1:0] wb_bus_sel;
  logic [WB_ADDR_WIDTH-1:0] wb_bus_adr;
  logic [WB_DATA_WIDTH-1:0] wb_bus_wdata;
  logic [WB_DATA_WIDTH-1:0] wb_bus_rdata;
  logic        wb_bus_ack;
  logic        wb_bus_err;
  logic        wb_bus_stall;

  logic        imem_wb_cyc;
  logic        imem_wb_stb;
  logic        imem_wb_we;
  logic [WB_SEL_WIDTH-1:0] imem_wb_sel;
  logic [WB_ADDR_WIDTH-1:0] imem_wb_adr;
  logic [WB_DATA_WIDTH-1:0] imem_wb_wdata;
  logic [WB_DATA_WIDTH-1:0] imem_wb_rdata;
  logic        imem_wb_ack;
  logic        imem_wb_err;
  logic        imem_wb_stall;

  logic        dmem_wb_cyc;
  logic        dmem_wb_stb;
  logic        dmem_wb_we;
  logic [WB_SEL_WIDTH-1:0] dmem_wb_sel;
  logic [WB_ADDR_WIDTH-1:0] dmem_wb_adr;
  logic [WB_DATA_WIDTH-1:0] dmem_wb_wdata;
  logic [WB_DATA_WIDTH-1:0] dmem_wb_rdata;
  logic        dmem_wb_ack;
  logic        dmem_wb_err;
  logic        dmem_wb_stall;

  logic        instr_rsp_err;
  logic        data_rsp_err;

  // Simulation configuration

  string       project_root;
  string       program_path;
  string       expect_path;
  string       dmem_path;
  string       wavefile_path;

  int unsigned timeout_cycles;
  bit          wave_enable;

  // Timeouts and bookkeeping
  int unsigned cycle_count;

  rv32i_wb_instr_adapter instr_adapter_i (
    .clk_i        (clk),
    .rst_ni       (rst_ni),
    .req_i        (instr_req),
    .addr_i       (instr_addr),
    .gnt_o        (instr_gnt),
    .rsp_valid_o  (instr_rvalid),
    .rsp_rdata_o  (instr_rdata),
    .rsp_err_o    (instr_rsp_err),
    .wb_cyc_o     (if_wb_cyc),
    .wb_stb_o     (if_wb_stb),
    .wb_we_o      (if_wb_we),
    .wb_sel_o     (if_wb_sel),
    .wb_adr_o     (if_wb_adr),
    .wb_dat_o     (if_wb_wdata),
    .wb_dat_i     (if_wb_rdata),
    .wb_ack_i     (if_wb_ack),
    .wb_err_i     (if_wb_err),
    .wb_stall_i   (if_wb_stall)
  );

  rv32i_wb_data_adapter data_adapter_i (
    .clk_i            (clk),
    .rst_ni           (rst_ni),
    .req_i            (data_req),
    .we_i             (data_we),
    .be_i             (data_be),
    .addr_i           (data_addr),
    .wdata_i          (data_wdata),
    .gnt_o            (data_gnt),
    .rsp_valid_o      (data_rvalid),
    .rsp_rdata_o      (data_rdata),
    .rsp_err_o        (data_rsp_err),
    .store_complete_o (),
    .store_err_o      (),
    .wb_cyc_o         (mem_wb_cyc),
    .wb_stb_o         (mem_wb_stb),
    .wb_we_o          (mem_wb_we),
    .wb_sel_o         (mem_wb_sel),
    .wb_adr_o         (mem_wb_adr),
    .wb_dat_o         (mem_wb_wdata),
    .wb_dat_i         (mem_wb_rdata),
    .wb_ack_i         (mem_wb_ack),
    .wb_err_i         (mem_wb_err),
    .wb_stall_i       (mem_wb_stall)
  );

  rv32i_wb_arbiter wb_arb_i (
    .clk_i         (clk),
    .rst_ni        (rst_ni),
    .instr_cyc_i   (if_wb_cyc),
    .instr_stb_i   (if_wb_stb),
    .instr_we_i    (if_wb_we),
    .instr_sel_i   (if_wb_sel),
    .instr_adr_i   (if_wb_adr),
    .instr_dat_i   (if_wb_wdata),
    .instr_dat_o   (if_wb_rdata),
    .instr_ack_o   (if_wb_ack),
    .instr_err_o   (if_wb_err),
    .instr_stall_o (if_wb_stall),
    .data_cyc_i    (mem_wb_cyc),
    .data_stb_i    (mem_wb_stb),
    .data_we_i     (mem_wb_we),
    .data_sel_i    (mem_wb_sel),
    .data_adr_i    (mem_wb_adr),
    .data_dat_i    (mem_wb_wdata),
    .data_dat_o    (mem_wb_rdata),
    .data_ack_o    (mem_wb_ack),
    .data_err_o    (mem_wb_err),
    .data_stall_o  (mem_wb_stall),
    .bus_cyc_o     (wb_bus_cyc),
    .bus_stb_o     (wb_bus_stb),
    .bus_we_o      (wb_bus_we),
    .bus_sel_o     (wb_bus_sel),
    .bus_adr_o     (wb_bus_adr),
    .bus_dat_o     (wb_bus_wdata),
    .bus_dat_i     (wb_bus_rdata),
    .bus_ack_i     (wb_bus_ack),
    .bus_err_i     (wb_bus_err),
    .bus_stall_i   (wb_bus_stall)
  );

  rv32i_wb_router #(
    .IMEM_BASE_ADDR   (32'h0000_0000),
    .IMEM_DEPTH_WORDS (4096),
    .DMEM_BASE_ADDR   (32'h8000_0000),
    .DMEM_DEPTH_WORDS (4096)
  ) wb_router_i (
    .clk_i        (clk),
    .rst_ni       (rst_ni),
    .m_cyc_i      (wb_bus_cyc),
    .m_stb_i      (wb_bus_stb),
    .m_we_i       (wb_bus_we),
    .m_sel_i      (wb_bus_sel),
    .m_adr_i      (wb_bus_adr),
    .m_dat_i      (wb_bus_wdata),
    .m_dat_o      (wb_bus_rdata),
    .m_ack_o      (wb_bus_ack),
    .m_err_o      (wb_bus_err),
    .m_stall_o    (wb_bus_stall),
    .imem_cyc_o   (imem_wb_cyc),
    .imem_stb_o   (imem_wb_stb),
    .imem_we_o    (imem_wb_we),
    .imem_sel_o   (imem_wb_sel),
    .imem_adr_o   (imem_wb_adr),
    .imem_dat_o   (imem_wb_wdata),
    .imem_dat_i   (imem_wb_rdata),
    .imem_ack_i   (imem_wb_ack),
    .imem_err_i   (imem_wb_err),
    .imem_stall_i (imem_wb_stall),
    .dmem_cyc_o   (dmem_wb_cyc),
    .dmem_stb_o   (dmem_wb_stb),
    .dmem_we_o    (dmem_wb_we),
    .dmem_sel_o   (dmem_wb_sel),
    .dmem_adr_o   (dmem_wb_adr),
    .dmem_dat_o   (dmem_wb_wdata),
    .dmem_dat_i   (dmem_wb_rdata),
    .dmem_ack_i   (dmem_wb_ack),
    .dmem_err_i   (dmem_wb_err),
    .dmem_stall_i (dmem_wb_stall)
  );

  rv32i_imem_model #(
    .NAME("imem"),
    .MEM_DEPTH_WORDS(4096),
    .BASE_ADDR(32'h0000_0000)
  ) imem_i (
    .clk_i      (clk),
    .rst_ni     (rst_ni),
    .wb_cyc_i   (imem_wb_cyc),
    .wb_stb_i   (imem_wb_stb),
    .wb_we_i    (imem_wb_we),
    .wb_sel_i   (imem_wb_sel),
    .wb_adr_i   (imem_wb_adr),
    .wb_dat_i   (imem_wb_wdata),
    .wb_dat_o   (imem_wb_rdata),
    .wb_ack_o   (imem_wb_ack),
    .wb_err_o   (imem_wb_err),
    .wb_stall_o (imem_wb_stall)
  );

  rv32i_dmem_model #(
    .NAME("dmem"),
    .MEM_DEPTH_WORDS(4096),
    .BASE_ADDR(32'h8000_0000)
  ) dmem_i (
    .clk_i         (clk),
    .rst_ni        (rst_ni),
    .wb_cyc_i      (dmem_wb_cyc),
    .wb_stb_i      (dmem_wb_stb),
    .wb_we_i       (dmem_wb_we),
    .wb_sel_i      (dmem_wb_sel),
    .wb_adr_i      (dmem_wb_adr),
    .wb_dat_i      (dmem_wb_wdata),
    .wb_dat_o      (dmem_wb_rdata),
    .wb_ack_o      (dmem_wb_ack),
    .wb_err_o      (dmem_wb_err),
    .wb_stall_o    (dmem_wb_stall),
    .store_valid_o (store_valid),
    .store_addr_o  (store_addr),
    .store_data_o  (store_data)
  );

  logic scoreboard_done;
  logic scoreboard_pass;

  rv32i_scoreboard #(
    .NAME("scoreboard")
  ) scoreboard_i (
    .clk_i        (clk),
    .rst_ni       (rst_ni),
    .store_valid_i(store_valid),
    .store_addr_i (store_addr),
    .store_data_i (store_data),
    .done_o       (scoreboard_done),
    .pass_o       (scoreboard_pass)
  );

  // Flag Wishbone error responses in simulation.
  always_ff @(posedge clk) begin
    if (instr_rsp_err) begin
      $fatal(1, "[tb] Instruction bus error observed at time %0t", $time);
    end
    if (data_rsp_err) begin
      $fatal(1, "[tb] Data bus error observed at time %0t", $time);
    end
  end

  // Clock generation
  initial begin
    clk = 1'b0;
    forever #(CLK_PERIOD/2) clk = ~clk;
  end

  // Reset sequence
  initial begin
    rst_ni = 1'b0;
    repeat (10) @(posedge clk);
    rst_ni = 1'b1;
    $display("[tb] Reset deasserted at %0t", $time);
  end

  // DUT instantiation (defined externally in the RTL tree)
  rv32i_core dut (
    .clk_i          (clk),
    .rst_ni         (rst_ni),
    .instr_req_o    (instr_req),
    .instr_gnt_i    (instr_gnt),
    .instr_rvalid_i (instr_rvalid),
    .instr_addr_o   (instr_addr),
    .instr_rdata_i  (instr_rdata),
    .data_req_o     (data_req),
    .data_we_o      (data_we),
    .data_be_o      (data_be),
    .data_addr_o    (data_addr),
    .data_wdata_o   (data_wdata),
    .data_rvalid_i  (data_rvalid),
    .data_rdata_i   (data_rdata),
    .irq_timer_i    (1'b0),
    .irq_external_i (1'b0),
    .irq_soft_i     (1'b0),
    .dbg_req_i      (1'b0),
    .dbg_halted_o   (dbg_halted)
  );

  task automatic configure_wave_dump();
    string resolved;
    resolved = wavefile_path;
    if (resolved.len() == 0 && wave_enable) begin
      resolved = {test_name, ".vcd"};
    end

    if (resolved.len() == 0) begin
      return;
    end

    if (str_ends_with(resolved, ".vcd")) begin
      $display("[tb] Writing VCD dump to '%s'", resolved);
      $dumpfile(resolved);
      $dumpvars(0, rv32i_core_tb_top);
    end else if (str_ends_with(resolved, ".vpd")) begin
`ifdef VCS
      $display("[tb] Writing VPD dump to '%s'", resolved);
      $vcdplusfile(resolved);
      $vcdpluson(0, rv32i_core_tb_top);
`else
      $display("[tb] Requested VPD output '%s' but simulator does not support VPD; falling back to VCD", resolved);
      $dumpfile({resolved, ".fallback.vcd"});
      $dumpvars(0, rv32i_core_tb_top);
`endif
    end else if (str_ends_with(resolved, ".fsdb")) begin
`ifdef FSDB
      $display("[tb] Writing FSDB dump to '%s'", resolved);
      $fsdbDumpfile(resolved);
      $fsdbDumpvars(0, rv32i_core_tb_top);
`else
      $display("[tb] Requested FSDB output '%s' but FSDB support is not enabled; falling back to VCD", resolved);
      $dumpfile({resolved, ".fallback.vcd"});
      $dumpvars(0, rv32i_core_tb_top);
`endif
    end else begin
      $display("[tb] Writing generic VCD dump to '%s'", resolved);
      $dumpfile(resolved);
      $dumpvars(0, rv32i_core_tb_top);
    end
  endtask

  function automatic string getenv_or_default(input string name, input string default_value);
    string env_value;
    env_value = $getenv(name);
    if (env_value.len() != 0) begin
      return env_value;
    end
    return default_value;
  endfunction

  task automatic configure_environment();
    int unsigned timeout_override;

    timeout_cycles = DEFAULT_TIMEOUT_CYCLES;
    wave_enable    = 1'b0;
    test_name      = "smoke";
    project_root   = getenv_or_default("PROJECT_ROOT", "..");
    program_path   = "";
    expect_path    = "";
    dmem_path      = "";
    wavefile_path  = "";

    if (!$value$plusargs("TEST=%s", test_name)) begin
      test_name = "smoke";
    end
    void'($value$plusargs("PROJECT_ROOT=%s", project_root));
    void'($value$plusargs("PROGRAM=%s", program_path));
    void'($value$plusargs("EXPECT=%s", expect_path));
    void'($value$plusargs("DMEM=%s", dmem_path));
    if ($value$plusargs("WAVEFILE=%s", wavefile_path)) begin
      wave_enable = 1'b1;
    end else begin
      wave_enable = $test$plusargs("WAVE");
    end
    if ($value$plusargs("TIMEOUT=%d", timeout_override)) begin
      timeout_cycles = timeout_override;
    end

    if (program_path.len() == 0) begin
      program_path = {project_root, "/tb/programs/", test_name, ".hex"};
    end

    if (expect_path.len() == 0) begin
      expect_path = replace_file_ext(program_path, ".exp");
    end

    $display("[tb] ------------------------------------------------------------");
    $display("[tb] Test configuration:");
    $display("[tb]   TEST          : %s", test_name);
    $display("[tb]   PROJECT_ROOT  : %s", project_root);
    $display("[tb]   PROGRAM       : %s", program_path);
    $display("[tb]   EXPECT        : %s", expect_path);
    if (dmem_path.len() != 0) begin
      $display("[tb]   DMEM INIT     : %s", dmem_path);
    end
    $display("[tb]   TIMEOUT       : %0d cycles", timeout_cycles);
    if (wave_enable) begin
      $display("[tb]   WAVES         : enabled (%s)", wavefile_path.len() ? wavefile_path : $sformatf("%s.vcd", test_name));
    end else begin
      $display("[tb]   WAVES         : disabled");
    end
    $display("[tb] ------------------------------------------------------------");
  endtask

  initial begin
    configure_environment();

    imem_i.clear_memory(32'h00000013);
    imem_i.load_hex(program_path);

    dmem_i.clear_memory('0);
    if (dmem_path.len() != 0) begin
      dmem_i.load_hex(dmem_path);
    end

    scoreboard_i.set_expectation_file(expect_path);
    scoreboard_i.load_expectations();

    configure_wave_dump();
  end

  // Timeout watchdog
  always_ff @(posedge clk or negedge rst_ni) begin
    if (!rst_ni) begin
      cycle_count <= 0;
    end else if (!scoreboard_done) begin
      cycle_count <= cycle_count + 1;
      if (cycle_count >= timeout_cycles) begin
        $fatal(1, "[tb] Timeout reached after %0d cycles", timeout_cycles);
      end
    end
  end

  // Completion detection
  always_ff @(posedge clk) begin
    if (scoreboard_done) begin
      if (scoreboard_pass) begin
        $display("[tb] TEST '%s' PASSED", test_name);
        #20 $finish;
      end else begin
        $fatal(1, "[tb] TEST '%s' FAILED (scoreboard mismatch)", test_name);
      end
    end
  end

  // If the DUT halts before the scoreboard triggers, surface the status.
  always_ff @(posedge clk) begin
    if (dbg_halted && !scoreboard_done) begin
      $display("[tb] DUT entered debug halt state before scoreboard completion at %0t", $time);
    end
  end

  final begin
    if (!scoreboard_done) begin
      $display("[tb] Simulation finished without scoreboard verdict.");
    end
  end

endmodule : rv32i_core_tb_top
