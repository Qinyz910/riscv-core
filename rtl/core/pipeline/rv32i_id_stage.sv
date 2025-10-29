// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

import rv32i_core_pkg::*;

module rv32i_id_stage (
  input  logic            if_valid_i,
  input  if_id_payload_t  if_payload_i,
  output logic            id_valid_o,
  output id_ex_payload_t  id_payload_o,
  output logic [4:0]      rf_rs1_addr_o,
  output logic [4:0]      rf_rs2_addr_o,
  input  logic [31:0]     rf_rs1_data_i,
  input  logic [31:0]     rf_rs2_data_i
);

  decode_ctrl_t decode_ctrl;
  logic         illegal_instr;
  logic [31:0]  imm_value;

  rv32i_decoder decoder_i (
    .instr_i   (if_payload_i.instr),
    .ctrl_o    (decode_ctrl),
    .illegal_o (illegal_instr)
  );

  rv32i_imm_gen imm_gen_i (
    .instr_i    (if_payload_i.instr),
    .imm_type_i (decode_ctrl.imm_type),
    .imm_o      (imm_value)
  );

  assign rf_rs1_addr_o = decode_ctrl.rs1;
  assign rf_rs2_addr_o = decode_ctrl.rs2;

  always_comb begin
    id_payload_o = '0;
    id_valid_o   = if_valid_i && decode_ctrl.valid && !illegal_instr;

    if (id_valid_o) begin
      id_payload_o.pc          = if_payload_i.pc;
      id_payload_o.pc_plus4    = if_payload_i.pc + 32'd4;
      id_payload_o.instr       = if_payload_i.instr;
      id_payload_o.imm         = imm_value;
      id_payload_o.rs1_data    = rf_rs1_data_i;
      id_payload_o.rs2_data    = rf_rs2_data_i;
      id_payload_o.rs1_addr    = decode_ctrl.rs1;
      id_payload_o.rs2_addr    = decode_ctrl.rs2;
      id_payload_o.rd_addr     = decode_ctrl.rd;
      id_payload_o.op_a_sel    = decode_ctrl.op_a_sel;
      id_payload_o.op_b_sel    = decode_ctrl.op_b_sel;
      id_payload_o.alu_op      = decode_ctrl.alu_op;
      id_payload_o.wb_sel      = decode_ctrl.wb_sel;
      id_payload_o.branch_type = decode_ctrl.branch_type;
      id_payload_o.branch      = decode_ctrl.branch;
      id_payload_o.jump        = decode_ctrl.jump;
      id_payload_o.jalr        = decode_ctrl.jalr;
      id_payload_o.mem_read    = decode_ctrl.mem_read;
      id_payload_o.mem_write   = decode_ctrl.mem_write;
      id_payload_o.mem_size    = decode_ctrl.mem_size;
      id_payload_o.mem_unsigned= decode_ctrl.mem_unsigned;
      id_payload_o.reg_write   = decode_ctrl.reg_write;
    end
  end

`ifndef SYNTHESIS
  always @(*) begin
    if (if_valid_i && illegal_instr) begin
      $fatal(1, "[rv32i_id_stage] Illegal instruction 0x%08x at PC 0x%08x", if_payload_i.instr, if_payload_i.pc);
    end
  end
`endif

endmodule : rv32i_id_stage
