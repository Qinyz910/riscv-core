# Module Interface Specifications

This document summarizes the interfaces for the primary RTL modules that compose the `riscv-core` microarchitecture. Signal names follow SystemVerilog conventions with `_i` and `_o` suffixes denoting input and output ports, respectively. All buses are little-endian and synchronous to the rising edge of `clk_i` unless otherwise stated.

## Common Conventions

- **Clock & Reset**: Each module receives `clk_i` and an active-low synchronous reset `rst_ni`.
- **Handshake Protocols**:
  - Ready/Valid channels use `*_valid_i`/`*_ready_o` for sink modules and `*_valid_o`/`*_ready_i` for source modules.
  - AXI-lite interfaces follow standard naming: `aw_*`, `w_*`, `b_*`, `ar_*`, `r_*`.
- **Parameterized Widths**: Address and data widths default to 32 bits (`ADDR_WIDTH = 32`, `DATA_WIDTH = 32`).

## Top-Level Core (`core_top`)

| Port              | Dir | Width | Description                                                     |
|-------------------|:---:|:-----:|-----------------------------------------------------------------|
| `clk_i`           |  in |   1   | Rising-edge clock.                                              |
| `rst_ni`          |  in |   1   | Active-low synchronous reset.                                   |
| `instr_req_o`     | out |   1   | Instruction fetch request valid.                                |
| `instr_gnt_i`     |  in |   1   | Instruction fetch grant/ready.                                  |
| `instr_rvalid_i`  |  in |   1   | Instruction response valid.                                     |
| `instr_addr_o`    | out |  32   | Instruction fetch address.                                      |
| `instr_rdata_i`   |  in |  32   | Instruction word returned from memory.                          |
| `data_req_o`      | out |   1   | Data access request valid.                                      |
| `data_we_o`       | out |   1   | Data write enable (1=store, 0=load).                            |
| `data_be_o`       | out |   4   | Byte enables for sub-word accesses.                             |
| `data_addr_o`     | out |  32   | Data access address.                                            |
| `data_wdata_o`    | out |  32   | Store data.                                                      |
| `data_rvalid_i`   |  in |   1   | Data response valid.                                            |
| `data_rdata_i`    |  in |  32   | Load data.                                                       |
| `irq_timer_i`     |  in |   1   | Machine timer interrupt.                                        |
| `irq_external_i`  |  in |   1   | Machine external interrupt.                                     |
| `irq_soft_i`      |  in |   1   | Machine software interrupt.                                     |
| `dbg_req_i`       |  in |   1   | Debug request (halt).                                           |
| `dbg_halted_o`    | out |   1   | Debug state indicator.                                          |

## Instruction Fetch Stage (`if_stage`)

| Port               | Dir | Width | Description                                                     |
|--------------------|:---:|:-----:|-----------------------------------------------------------------|
| `clk_i`            |  in |   1   | Clock.                                                          |
| `rst_ni`           |  in |   1   | Reset.                                                          |
| `pc_redirect_i`    |  in |   1   | Redirect request from EX or control unit.                       |
| `pc_redirect_addr_i`| in |  32   | New PC on redirect.                                             |
| `fetch_ready_i`    |  in |   1   | Downstream IF/ID register ready.                                |
| `fetch_valid_o`    | out |   1   | New instruction available.                                      |
| `fetch_pc_o`       | out |  32   | PC of fetched instruction.                                      |
| `fetch_instr_o`    | out |  32   | Instruction word.                                               |
| `mem_req_o`        | out |   1   | Memory request valid.                                           |
| `mem_addr_o`       | out |  32   | Instruction memory address.                                     |
| `mem_ready_i`      |  in |   1   | Memory grant/ready.                                             |
| `mem_rvalid_i`     |  in |   1   | Memory response valid.                                          |
| `mem_rdata_i`      |  in |  32   | Instruction data from memory.                                   |

Protocol: The IF stage issues one outstanding request at a time. When `mem_req_o` and `mem_ready_i` are asserted, the request is accepted. Once `mem_rvalid_i` is high, the instruction is captured and forwarded to ID.

## Instruction Decode Stage (`id_stage`)

| Port                  | Dir | Width | Description                                                    |
|-----------------------|:---:|:-----:|----------------------------------------------------------------|
| `clk_i`, `rst_ni`     |  in |   1   | Clock/reset.                                                   |
| `instr_valid_i`       |  in |   1   | Instruction from IF valid.                                     |
| `instr_pc_i`          |  in |  32   | Instruction PC.                                                |
| `instr_bits_i`        |  in |  32   | Instruction word.                                              |
| `rf_rs1_addr_o`       | out |   5   | Register file RS1 address.                                     |
| `rf_rs2_addr_o`       | out |   5   | Register file RS2 address.                                     |
| `rf_rs1_data_i`       |  in |  32   | RS1 data.                                                      |
| `rf_rs2_data_i`       |  in |  32   | RS2 data.                                                      |
| `csr_req_o`           | out |   1   | CSR access request.                                            |
| `csr_addr_o`          | out |  12   | CSR address.                                                   |
| `hazard_stall_o`      | out |   1   | Request pipeline stall due to hazard.                          |
| `decode_valid_o`      | out |   1   | Control bundle valid to EX.                                    |
| `decode_payload_o`    | out |  --   | Struct containing immediate, control flags, and operands.      |

Protocol: When `hazard_stall_o` is asserted, IF and ID hold their state until hazards clear.

## Execute Stage (`ex_stage`)

| Port                   | Dir | Width | Description                                                    |
|------------------------|:---:|:-----:|----------------------------------------------------------------|
| `clk_i`, `rst_ni`      |  in |   1   | Clock/reset.                                                   |
| `decode_valid_i`       |  in |   1   | Control bundle valid.                                          |
| `decode_payload_i`     |  in |  --   | Control/operand struct from ID.                                |
| `forward_from_mem_i`   |  in |  32   | Forwarded data from MEM.                                       |
| `forward_from_wb_i`    |  in |  32   | Forwarded data from WB.                                        |
| `branch_taken_o`       | out |   1   | Branch resolution flag.                                        |
| `branch_target_o`      | out |  32   | Target PC for taken branches/jumps.                            |
| `alu_result_o`         | out |  32   | Result of ALU operations.                                      |
| `muldiv_result_o`      | out |  32   | Result from multiplier/divider (if enabled).                   |
| `mem_addr_o`           | out |  32   | Effective data address for loads/stores.                       |
| `mem_write_data_o`     | out |  32   | Store data.                                                    |
| `mem_ctrl_o`           | out |  --   | Control struct for MEM (size, type).                           |
| `valid_o`              | out |   1   | EX stage output valid.                                         |

Protocol: Forwarding inputs prioritize MEM over WB results. Branch decisions are broadcast immediately to IF via the control block.

## Memory Stage (`mem_stage`)

| Port                  | Dir | Width | Description                                                     |
|-----------------------|:---:|:-----:|-----------------------------------------------------------------|
| `clk_i`, `rst_ni`     |  in |   1   | Clock/reset.                                                    |
| `ex_valid_i`          |  in |   1   | Incoming EX result valid.                                       |
| `ex_mem_addr_i`       |  in |  32   | Effective address from EX.                                      |
| `ex_mem_ctrl_i`       |  in |  --   | Load/store control struct (size, sign).                         |
| `ex_write_data_i`     |  in |  32   | Store data from EX.                                             |
| `ex_result_i`         |  in |  32   | ALU result for forwarding when no memory access.                |
| `axi_aw_*`            | I/O| var  | AXI-lite write address channel (addr, prot, valid, ready).      |
| `axi_w_*`             | I/O| var  | AXI-lite write data channel (data, strb, valid, ready).         |
| `axi_b_*`             | I/O| var  | AXI-lite write response channel (resp, valid, ready).           |
| `axi_ar_*`            | I/O| var  | AXI-lite read address channel.                                  |
| `axi_r_*`             | I/O| var  | AXI-lite read data channel.                                     |
| `lsu_result_o`        | out |  32   | Load data (aligned and extended).                               |
| `lsu_valid_o`         | out |   1   | Load/store completion valid.                                    |
| `forward_data_o`      | out |  32   | Data forwarded back to EX.                                      |

Protocol: The MEM stage arbitrates AXI-lite channels, ensuring single outstanding write/read operations to keep timing simple. Misaligned accesses raise exceptions flagged to the control unit.

## Write-Back Stage (`wb_stage`)

| Port                | Dir | Width | Description                                                      |
|---------------------|:---:|:-----:|------------------------------------------------------------------|
| `clk_i`, `rst_ni`   |  in |   1   | Clock/reset.                                                     |
| `alu_result_i`      |  in |  32   | ALU result from EX.                                              |
| `muldiv_result_i`   |  in |  32   | Multiplier/divider result.                                       |
| `lsu_result_i`      |  in |  32   | Load data from MEM.                                              |
| `csr_result_i`      |  in |  32   | CSR read data.                                                   |
| `result_valid_i`    |  in |   1   | Valid flag for the selected result.                              |
| `rd_addr_i`         |  in |   5   | Destination register address.                                    |
| `rd_write_o`        | out |   1   | Register file write enable.                                      |
| `rd_addr_o`         | out |   5   | Destination register address forwarded to register file.         |
| `rd_wdata_o`        | out |  32   | Data written to register file.                                   |
| `csr_write_o`       | out |   1   | CSR write strobe.                                                |
| `csr_addr_o`        | out |  12   | CSR address for write.                                           |
| `csr_wdata_o`       | out |  32   | CSR write data.                                                  |

Protocol: Priority mux selects data in the order: CSR > LSU > MUL/DIV > ALU, based on valid flags. Writes to x0 are suppressed.

## Register File (`register_file`)

| Port             | Dir | Width | Description                              |
|------------------|:---:|:-----:|------------------------------------------|
| `clk_i`          |  in |   1   | Clock.                                   |
| `rs1_addr_i`     |  in |   5   | Read port 1 address.                     |
| `rs2_addr_i`     |  in |   5   | Read port 2 address.                     |
| `rs1_data_o`     | out |  32   | Read port 1 data.                        |
| `rs2_data_o`     | out |  32   | Read port 2 data.                        |
| `rd_addr_i`      |  in |   5   | Write port address.                      |
| `rd_data_i`      |  in |  32   | Write port data.                         |
| `rd_write_i`     |  in |   1   | Write enable.                            |

Protocol: Dual-read, single-write synchronous register file with write-through bypass to minimize hazards.

## CSR Unit (`csr_unit`)

| Port             | Dir | Width | Description                                        |
|------------------|:---:|:-----:|----------------------------------------------------|
| `clk_i`, `rst_ni`|  in |   1   | Clock/reset.                                       |
| `csr_req_i`      |  in |   1   | Request from ID or WB.                             |
| `csr_we_i`       |  in |   1   | Write enable.                                      |
| `csr_addr_i`     |  in |  12   | CSR address.                                       |
| `csr_wdata_i`    |  in |  32   | CSR write data.                                    |
| `csr_rdata_o`    | out |  32   | CSR read data.                                     |
| `csr_ready_o`    | out |   1   | Indicates completion/availability.                 |
| `irq_lines_i`    |  in |   3   | Timer, external, and software interrupts.          |
| `trap_taken_o`   | out |   1   | Trap signal to control logic.                      |
| `trap_vector_o`  | out |  32   | Target PC for trap handler.                        |

## Forwarding Unit (`forwarding_unit`)

| Port                   | Dir | Width | Description                                     |
|------------------------|:---:|:-----:|-------------------------------------------------|
| `ex_rs1_addr_i`        |  in |   5   | EX stage RS1 address.                           |
| `ex_rs2_addr_i`        |  in |   5   | EX stage RS2 address.                           |
| `mem_rd_addr_i`        |  in |   5   | MEM stage destination register.                 |
| `mem_regwrite_i`       |  in |   1   | MEM stage write enable.                         |
| `wb_rd_addr_i`         |  in |   5   | WB stage destination register.                  |
| `wb_regwrite_i`        |  in |   1   | WB stage write enable.                          |
| `forward_a_sel_o`      | out |   2   | Select for EX operand A mux (00=RF, 01=WB, 10=MEM). |
| `forward_b_sel_o`      | out |   2   | Select for EX operand B mux.                    |

## Hazard Detection Unit (`hazard_unit`)

| Port                     | Dir | Width | Description                                         |
|--------------------------|:---:|:-----:|-----------------------------------------------------|
| `id_rs1_addr_i`          |  in |   5   | ID stage RS1.                                       |
| `id_rs2_addr_i`          |  in |   5   | ID stage RS2.                                       |
| `ex_rd_addr_i`           |  in |   5   | EX stage destination register.                      |
| `ex_memread_i`           |  in |   1   | Indicates EX is performing a load.                  |
| `pipeline_valid_i`       |  in |   3   | Valid bits for ID/EX/MEM pipeline stages.           |
| `stall_o`                | out |   1   | Request stall insertion.                            |
| `flush_o`                | out |   1   | Request pipeline flush (on branch mispredict).      |

## Interrupt & Debug Interface (`debug_unit`)

| Port                 | Dir | Width | Description                                          |
|----------------------|:---:|:-----:|------------------------------------------------------|
| `clk_i`, `rst_ni`    |  in |   1   | Clock/reset.                                         |
| `dbg_req_i`          |  in |   1   | External debugger halt request.                      |
| `dbg_resume_i`       |  in |   1   | Resume request.                                      |
| `csr_status_i`       |  in |  32   | CSR status snapshot.                                 |
| `halt_o`             | out |   1   | Signal to halt pipeline.                             |
| `halt_ack_o`         | out |   1   | Indicates pipeline has entered debug state.          |
| `pc_snapshot_o`      | out |  32   | Program counter captured on halt.                    |

## Memory Interfaces

### Instruction Memory
- **Protocol**: Wishbone Classic single-beat transactions generated by `rv32i_wb_instr_adapter`.
- **Adapter**: Bridges the IF stage request/grant handshake (`instr_req_o`/`instr_gnt_i`) to Wishbone `cyc/stb` while preserving in-order responses.
- **Error Handling**: `instr_err_i` propagates Wishbone error responses, allowing fetch faults to redirect the pipeline.

### Data Memory
- **Protocol**: Wishbone Classic managed by `rv32i_wb_data_adapter`, supporting one outstanding read or write.
- **Byte Enables**: `data_be_o` are translated to Wishbone `sel` lines for sub-word stores; loads return the full word for MEM-stage alignment/sign extension.
- **Exceptions**: Misaligned or unmapped addresses trigger Wishbone error responses that surface on `data_rsp_err_o` and raise precise traps.

### Simulation Models
- **Instruction ROM**: `rv32i_imem_model` exposes a Wishbone slave with parameterised depth and fixed/random wait-state insertion.
- **Data RAM**: `rv32i_dmem_model` mirrors the Wishbone slave behaviour, applies byte enables, captures store activity for the scoreboard, and supports configurable latency.

## Parameter Summary

| Parameter        | Default | Description                                       |
|------------------|:-------:|---------------------------------------------------|
| `XLEN`           |   32    | Data path width.                                  |
| `RESET_VECTOR`   | `0x00000000` | Reset PC.                                     |
| `ENABLE_M`       | `0`     | Enable RV32M multiplier/divider.                  |
| `ENABLE_C`       | `0`     | Enable compressed instruction support.            |
| `ENABLE_ICACHE`  | `0`     | Integrate instruction cache.                      |
| `ENABLE_DCACHE`  | `0`     | Integrate data cache.                             |
| `ENABLE_DEBUG`   | `1`     | Include debug module and halt interface.          |

## Revision History

| Version | Date       | Description                                      |
|---------|------------|--------------------------------------------------|
| 0.2     | 2024-10-30 | Added Wishbone instruction/data adapters and models. |
| 0.1     | 2024-10-29 | Initial interface snapshot. |
