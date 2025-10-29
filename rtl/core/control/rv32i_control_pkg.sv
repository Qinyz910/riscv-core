// Copyright (c) 2024
// SPDX-License-Identifier: Apache-2.0

`timescale 1ns/1ps

package rv32i_control_pkg;

  typedef enum logic [1:0] {
    FORWARD_NONE = 2'b00,
    FORWARD_FROM_WB  = 2'b01,
    FORWARD_FROM_MEM = 2'b10
  } forwarding_sel_e;

  function automatic string forwarding_sel_name(input forwarding_sel_e sel);
    case (sel)
      FORWARD_NONE:     forwarding_sel_name = "none";
      FORWARD_FROM_WB:  forwarding_sel_name = "wb";
      FORWARD_FROM_MEM: forwarding_sel_name = "mem";
      default:          forwarding_sel_name = "unknown";
    endcase
  endfunction

endpackage : rv32i_control_pkg
