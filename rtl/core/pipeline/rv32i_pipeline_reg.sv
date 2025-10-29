// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

module rv32i_pipeline_reg #(
  parameter type T = logic
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic hold_i,
  input  logic flush_i,
  input  logic valid_i,
  input  T     data_i,
  output logic valid_o,
  output T     data_o
);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid_o <= 1'b0;
      data_o  <= '0;
    end else begin
      if (flush_i) begin
        valid_o <= 1'b0;
      end else if (!hold_i) begin
        valid_o <= valid_i;
        data_o  <= data_i;
      end
    end
  end

endmodule : rv32i_pipeline_reg
