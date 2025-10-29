// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

package rv32i_wb_pkg;

  parameter int unsigned WB_ADDR_WIDTH = 32;
  parameter int unsigned WB_DATA_WIDTH = 32;
  parameter int unsigned WB_SEL_WIDTH  = WB_DATA_WIDTH / 8;

  typedef struct packed {
    logic                        cyc;
    logic                        stb;
    logic                        we;
    logic [WB_SEL_WIDTH-1:0]     sel;
    logic [WB_ADDR_WIDTH-1:0]   adr;
    logic [WB_DATA_WIDTH-1:0]   wdata;
  } wb_master_req_t;

  typedef struct packed {
    logic [WB_DATA_WIDTH-1:0]   rdata;
    logic                       ack;
    logic                       err;
    logic                       stall;
  } wb_slave_rsp_t;

  function automatic wb_master_req_t wb_master_req_default();
    wb_master_req_t req;
    req.cyc   = 1'b0;
    req.stb   = 1'b0;
    req.we    = 1'b0;
    req.sel   = '0;
    req.adr   = '0;
    req.wdata = '0;
    return req;
  endfunction

  function automatic wb_slave_rsp_t wb_slave_rsp_default();
    wb_slave_rsp_t rsp;
    rsp.rdata = '0;
    rsp.ack   = 1'b0;
    rsp.err   = 1'b0;
    rsp.stall = 1'b0;
    return rsp;
  endfunction

endpackage : rv32i_wb_pkg
