// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

module rv32i_hazard_unit #(
  parameter bit ENABLE_ASSERTIONS = 1'b1
) (
  input  logic        clk_i,
  input  logic        rst_ni,
  input  logic [4:0]  id_rs1_addr_i,
  input  logic [4:0]  id_rs2_addr_i,
  input  logic [4:0]  ex_rd_addr_i,
  input  logic        ex_regwrite_i,
  input  logic        ex_memread_i,
  input  logic [2:0]  pipeline_valid_i,
  input  logic        branch_flush_i,
  input  logic        structural_hazard_i,
  output logic        stall_o,
  output logic        flush_o
);

  logic id_valid;
  logic ex_valid;
  logic rs1_hazard;
  logic rs2_hazard;
  logic load_use_hazard;
  logic stall_req;

  assign id_valid = pipeline_valid_i[0];
  assign ex_valid = pipeline_valid_i[1];

  assign rs1_hazard = id_valid && ex_valid && ex_memread_i && ex_regwrite_i &&
                      (id_rs1_addr_i != 5'd0) &&
                      (id_rs1_addr_i == ex_rd_addr_i);

  assign rs2_hazard = id_valid && ex_valid && ex_memread_i && ex_regwrite_i &&
                      (id_rs2_addr_i != 5'd0) &&
                      (id_rs2_addr_i == ex_rd_addr_i);

  assign load_use_hazard = rs1_hazard || rs2_hazard;

  assign stall_req = structural_hazard_i || load_use_hazard;

  always_comb begin
    flush_o = branch_flush_i;
    if (flush_o) begin
      stall_o = 1'b0;
    end else begin
      stall_o = stall_req;
    end
  end

  generate
    if (ENABLE_ASSERTIONS) begin : gen_hazard_assertions
      property p_no_simultaneous_stall_flush;
        @(posedge clk_i) disable iff (!rst_ni)
          !(stall_o && flush_o);
      endproperty
      assert property (p_no_simultaneous_stall_flush)
        else $fatal(1, "[hazard] stall_o and flush_o asserted simultaneously");
    end
  endgenerate

endmodule : rv32i_hazard_unit
