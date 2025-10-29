// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_tb_pkg::*;

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

  logic        dbg_halted;

  // Scoreboard observation signals
  logic        store_valid;
  logic [31:0] store_addr;
  logic [31:0] store_data;

  // Simulation configuration
  string       test_name;
  string       project_root;
  string       program_path;
  string       expect_path;
  string       dmem_path;
  string       wavefile_path;

  int unsigned timeout_cycles;
  bit          wave_enable;

  // Timeouts and bookkeeping
  int unsigned cycle_count;

  rv32i_imem_model #(
    .NAME("imem"),
    .MEM_DEPTH_WORDS(4096)
  ) imem_i (
    .clk_i     (clk),
    .rst_ni    (rst_ni),
    .req_i     (instr_req),
    .gnt_o     (instr_gnt),
    .addr_i    (instr_addr),
    .rvalid_o  (instr_rvalid),
    .rdata_o   (instr_rdata)
  );

  rv32i_dmem_model #(
    .NAME("dmem"),
    .MEM_DEPTH_WORDS(4096)
  ) dmem_i (
    .clk_i         (clk),
    .rst_ni        (rst_ni),
    .req_i         (data_req),
    .we_i          (data_we),
    .be_i          (data_be),
    .addr_i        (data_addr),
    .wdata_i       (data_wdata),
    .rvalid_o      (data_rvalid),
    .rdata_o       (data_rdata),
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
