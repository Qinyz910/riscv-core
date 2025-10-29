// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_tb_pkg::*;

module rv32i_scoreboard #(
  parameter string NAME = "scoreboard",
  parameter string EXPECT_DEFAULT = ""
) (
  input  logic        clk_i,
  input  logic        rst_ni,
  input  logic        store_valid_i,
  input  logic [31:0] store_addr_i,
  input  logic [31:0] store_data_i,
  output logic        done_o,
  output logic        pass_o
);

  store_event_t expectations[$];

  string expectation_path;
  bit    expectations_loaded;

  int unsigned next_index;
  logic        done_q;
  logic        pass_q;
  logic        fail_q;

  function automatic void set_expectation_file(input string path);
    expectation_path = path;
  endfunction

  function automatic int unsigned expectation_count();
    return expectations.size();
  endfunction

  function automatic bit expectations_available();
    return expectations_loaded;
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

  task automatic load_expectations();
    int fd;
    string line;
    store_event_t entry;
    longint unsigned addr_value;
    longint unsigned data_value;

    expectations.delete();
    next_index           = 0;
    done_q               = 1'b0;
    pass_q               = 1'b0;
    fail_q               = 1'b0;
    expectations_loaded  = 1'b0;

    if (expectation_path.len() == 0) begin
      $display("[%s] No expectation file provided; relying on tohost convention", NAME);
      return;
    end
    if (!file_exists(expectation_path)) begin
      $display("[%s] Expectation file '%s' not found; relying on tohost convention", NAME, expectation_path);
      return;
    end

    fd = $fopen(expectation_path, "r");
    if (fd == 0) begin
      $fatal(1, "[%s] Unable to open expectation file '%s'", NAME, expectation_path);
    end

    while ($fgets(line, fd)) begin
      line = str_trim(line);
      if (line.len() == 0) begin
        continue;
      end
      if (str_starts_with(line, "#")) begin
        continue;
      end
      if ($sscanf(line, "%h %h", addr_value, data_value) == 2) begin
        entry.addr = addr_value[31:0];
        entry.data = data_value[31:0];
        expectations.push_back(entry);
      end else begin
        $display("[%s] Ignoring malformed expectation line: '%s'", NAME, line);
      end
    end
    $fclose(fd);

    if (expectations.size() > 0) begin
      expectations_loaded = 1'b1;
      $display("[%s] Loaded %0d expectation entries from '%s'", NAME, expectations.size(), expectation_path);
    end else begin
      $display("[%s] Expectation file '%s' was empty; relying on tohost convention", NAME, expectation_path);
    end
  endtask

  function automatic bit has_failed();
    return fail_q;
  endfunction

  initial begin
    expectation_path    = EXPECT_DEFAULT;
    expectations_loaded = 1'b0;
    next_index          = 0;
    done_q              = 1'b0;
    pass_q              = 1'b0;
    fail_q              = 1'b0;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      next_index <= 0;
      done_q     <= 1'b0;
      pass_q     <= 1'b0;
      fail_q     <= 1'b0;
    end else begin
      if (!done_q && store_valid_i) begin
        if (expectations_loaded) begin
          if (next_index >= expectations.size()) begin
            $error("[%s] Unexpected store to 0x%08h (data=0x%08h) after expectations were met",
                   NAME, store_addr_i, store_data_i);
            done_q <= 1'b1;
            pass_q <= 1'b0;
            fail_q <= 1'b1;
          end else begin
            store_event_t expected;
            expected = expectations[next_index];
            if ((store_addr_i !== expected.addr) || (store_data_i !== expected.data)) begin
              $error("[%s] Store mismatch at entry %0d: expected addr=0x%08h data=0x%08h, got addr=0x%08h data=0x%08h",
                     NAME, next_index, expected.addr, expected.data, store_addr_i, store_data_i);
              done_q <= 1'b1;
              pass_q <= 1'b0;
              fail_q <= 1'b1;
            end else begin
              $display("[%s] Store %0d matched (addr=0x%08h data=0x%08h)",
                       NAME, next_index, store_addr_i, store_data_i);
              next_index <= next_index + 1;
              if ((next_index + 1) >= expectations.size()) begin
                done_q <= 1'b1;
                pass_q <= 1'b1;
              end
            end
          end
        end else begin
          if (store_addr_i == TOHOST_ADDR) begin
            done_q <= 1'b1;
            pass_q <= (store_data_i == 32'h1);
            fail_q <= (store_data_i != 32'h1);
            if (store_data_i == 32'h1) begin
              $display("[%s] PASS signalled via tohost", NAME);
            end else begin
              $error("[%s] FAIL signalled via tohost value 0x%08h", NAME, store_data_i);
            end
          end
        end
      end
    end
  end

  assign done_o = done_q;
  assign pass_o = pass_q;

endmodule : rv32i_scoreboard
