// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

package rv32i_tb_pkg;

  parameter int unsigned XLEN = 32;
  parameter logic [XLEN-1:0] TOHOST_ADDR = 32'h8000_0000;
  parameter int unsigned DEFAULT_TIMEOUT_CYCLES = 200_000;

  typedef struct packed {
    logic [XLEN-1:0] addr;
    logic [XLEN-1:0] data;
  } store_event_t;

  function automatic string str_trim(input string value);
    string result;
    int unsigned start;
    int unsigned finish;
    start = 0;
    while (start < value.len() && (value[start] == " " || value[start] == "\t")) begin
      start++;
    end
    finish = value.len();
    while (finish > start && (value[finish-1] == " " || value[finish-1] == "\t" || value[finish-1] == "\n")) begin
      finish--;
    end
    for (int unsigned idx = start; idx < finish; idx++) begin
      result = {result, value[idx]};
    end
    return result;
  endfunction

  function automatic bit str_starts_with(input string value, input string prefix);
    if (prefix.len() > value.len()) begin
      return 0;
    end
    for (int unsigned idx = 0; idx < prefix.len(); idx++) begin
      if (value[idx] != prefix[idx]) begin
        return 0;
      end
    end
    return 1;
  endfunction

  function automatic bit str_ends_with(input string value, input string suffix);
    if (suffix.len() > value.len()) begin
      return 0;
    end
    for (int unsigned idx = 0; idx < suffix.len(); idx++) begin
      if (value[value.len() - suffix.len() + idx] != suffix[idx]) begin
        return 0;
      end
    end
    return 1;
  endfunction

  function automatic string replace_file_ext(input string path, input string new_ext);
    string base;
    int dot_index;
    dot_index = -1;
    for (int i = path.len(); i > 0; i--) begin
      if (path[i-1] == ".") begin
        dot_index = i-1;
        break;
      end
    end
    if (dot_index >= 0) begin
      for (int j = 0; j < dot_index; j++) begin
        base = {base, path[j]};
      end
      return {base, new_ext};
    end
    return {path, new_ext};
  endfunction

endpackage : rv32i_tb_pkg
