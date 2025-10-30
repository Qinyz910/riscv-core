# Module Interface Specifications

This document captures the contract for each synthesizable RTL block in the repository.  Combine these descriptions with the higher-level view in [`architecture.md`](architecture.md) when reasoning about integration or modification.

For every module you will find:

- **Purpose** – what role the module plays.
- **Parameters** – compile-time configuration options.
- **Ports** – inputs and outputs with widths and handshake notes.
- **Timing / protocol expectations** – any assumptions that a caller must honour.
- **Integration notes** – practical guidance or examples.

## Core top-level

### `rv32i_core`
- **Location:** `rtl/core/rv32i_core.sv`
- **Purpose:** Top-level five-stage RV32I pipeline exposing instruction and data memory ports plus stubbed interrupt/debug inputs.

| Parameter | Default | Description |
| --- | --- | --- |
| `RESET_VECTOR` | `32'h0000_0000` | Program counter value driven into IF after reset. |

| Port | Dir | Width | Description |
| --- | --- | --- | --- |
| `clk_i` | in | 1 | Rising-edge clock. |
| `rst_ni` | in | 1 | Asynchronous reset, active low. |
| `instr_req_o` | out | 1 | Asserted to request an instruction fetch. |
| `instr_gnt_i` | in | 1 | One-cycle grant/acknowledge for a fetch request. |
| `instr_rvalid_i` | in | 1 | Data valid pulse accompanying `instr_rdata_i`. |
| `instr_addr_o` | out | 32 | Fetch address (word aligned). |
| `instr_rdata_i` | in | 32 | Returned instruction word. |
| `data_req_o` | out | 1 | Asserted to issue a data memory access. |
| `data_we_o` | out | 1 | Write enable (1 = store, 0 = load). |
| `data_be_o` | out | 4 | Byte enables for stores (little-endian). |
| `data_addr_o` | out | 32 | Byte address for load/store. |
| `data_wdata_o` | out | 32 | Store data. |
| `data_rvalid_i` | in | 1 | Data return pulse for loads. |
| `data_rdata_i` | in | 32 | Load data (aligned and sized by external agent). |
| `irq_timer_i`/`irq_external_i`/`irq_soft_i` | in | 1 | Reserved for future exception pipeline (currently unused). |
| `dbg_req_i` | in | 1 | External debug request (unused). |
| `dbg_halted_o` | out | 1 | Debug status (always `0`). |

**Timing & protocol**
- Only one instruction request may be outstanding.  `instr_req_o` remains high until `instr_gnt_i` acknowledges it.
- Loads stall the entire pipeline until `data_rvalid_i` is observed.
- Stores are single-cycle: the core does not wait for an explicit acknowledgement.

**Integration notes**
- The top-level makes no assumptions about bus protocol beyond the ready/valid pulses.  See `rtl/bus` for Wishbone adapters used in simulation.

## Pipeline stages

### `rv32i_if_stage`
- **Location:** `rtl/core/pipeline/rv32i_if_stage.sv`
- **Purpose:** Program counter management, instruction fetch buffering, redirect handling.

| Parameter | Default | Description |
| --- | --- | --- |
| `RESET_PC` | `32'h0000_0000` | PC value loaded on reset. |

| Port | Dir | Width | Description |
| --- | --- | --- | --- |
| `clk_i`, `rst_ni` | in | 1 | Clock/reset. |
| `stall_i` | in | 1 | Freeze the stage (propagated from MEM). |
| `flush_i` | in | 1 | Invalidate buffered fetch (taken branch). |
| `redirect_i` | in | 1 | Redirect request from EX (branch/jump). |
| `redirect_pc_i` | in | 32 | Target PC when `redirect_i` is high. |
| `instr_req_o` | out | 1 | Fetch request. |
| `instr_addr_o` | out | 32 | Address of requested instruction. |
| `instr_gnt_i` | in | 1 | Bus accepts the request. |
| `instr_rvalid_i` | in | 1 | Return data valid. |
| `instr_rdata_i` | in | 32 | Returned instruction. |
| `fetch_valid_o` | out | 1 | Indicates buffered instruction is ready for decode. |
| `fetch_pc_o` | out | 32 | PC associated with buffered instruction. |
| `fetch_instr_o` | out | 32 | Buffered instruction word. |
| `fetch_ready_i` | in | 1 | Downstream ready; when low the buffer holds its data. |

**Protocol notes**
- `instr_req_o` is only asserted when no outstanding fetch exists and the downstream is ready.
- `flush_i` or `redirect_i` clear the buffer and suppress the next response if the request has already been granted.

### `rv32i_pipeline_reg`
- **Location:** `rtl/core/pipeline/rv32i_pipeline_reg.sv`
- **Purpose:** Generic pipeline register with hold/flush controls.

| Parameter | Default | Description |
| --- | --- | --- |
| `T` | `logic` | Packed struct or logic vector carried between stages. |

| Port | Dir | Width | Description |
| --- | --- | --- | --- |
| `clk_i`, `rst_ni` | in | 1 | Clock/reset. |
| `hold_i` | in | 1 | When high, retain previous `valid_o`/`data_o`. |
| `flush_i` | in | 1 | Forces `valid_o` low on the next cycle. |
| `valid_i` | in | 1 | Input side valid. |
| `data_i` | in | `T` | Payload. |
| `valid_o` | out | 1 | Output valid. |
| `data_o` | out | `T` | Output payload. |

### `rv32i_id_stage`
- **Location:** `rtl/core/pipeline/rv32i_id_stage.sv`
- **Purpose:** Decode instructions and assemble the `id_ex_payload_t` structure.

| Port | Dir | Width | Description |
| --- | --- | --- | --- |
| `if_valid_i` | in | 1 | Indicates IF/ID pipeline holds a valid entry. |
| `if_payload_i` | in | `if_id_payload_t` | PC and instruction from IF. |
| `id_valid_o` | out | 1 | High when the output payload is meaningful. |
| `id_payload_o` | out | `id_ex_payload_t` | Control/operand bundle for EX. |
| `rf_rs1_addr_o`, `rf_rs2_addr_o` | out | 5 | Register indices sent to the register file. |
| `rf_rs1_data_i`, `rf_rs2_data_i` | in | 32 | Register file read data. |

**Protocol notes**
- Illegal instructions trigger `$fatal` during simulation; in silicon the output would simply deassert `id_valid_o`.

### `rv32i_ex_stage`
- **Location:** `rtl/core/pipeline/rv32i_ex_stage.sv`
- **Purpose:** Execute ALU operations, evaluate branches, and forward control into MEM.

| Port | Dir | Width | Description |
| --- | --- | --- | --- |
| `id_valid_i` | in | 1 | Input payload valid. |
| `id_payload_i` | in | `id_ex_payload_t` | Control/operands from ID. |
| `ex_valid_o` | out | 1 | High when `ex_payload_o` is valid. |
| `ex_payload_o` | out | `ex_mem_payload_t` | Payload for MEM stage. |
| `branch_taken_o` | out | 1 | Branch/jump resolution. |
| `branch_target_o` | out | 32 | Redirect address (aligned for JALR). |

**Timing**
- Fully combinational w.r.t. operands; produces results in one cycle assuming ALU ready.

### `rv32i_mem_stage`
- **Location:** `rtl/core/pipeline/rv32i_mem_stage.sv`
- **Purpose:** Drive load/store operations and stall the pipeline on load latency.

| Port | Dir | Width | Description |
| --- | --- | --- | --- |
| `clk_i`, `rst_ni` | in | 1 | Clock/reset. |
| `ex_valid_i` | in | 1 | Indicates `ex_payload_i` is valid. |
| `ex_payload_i` | in | `ex_mem_payload_t` | EX stage payload. |
| `ex_hold_o` | out | 1 | Hold request propagated upstream. |
| `data_req_o` | out | 1 | Memory request. |
| `data_we_o` | out | 1 | Write enable. |
| `data_be_o` | out | 4 | Byte enables. |
| `data_addr_o` | out | 32 | Byte address. |
| `data_wdata_o` | out | 32 | Write data (after byte steering). |
| `data_rvalid_i` | in | 1 | Load data valid. |
| `data_rdata_i` | in | 32 | Load return data (word). |
| `mem_valid_o` | out | 1 | Set when `mem_payload_o` is ready for WB. |
| `mem_payload_o` | out | `mem_wb_payload_t` | Payload forwarded to WB. |

**Protocol notes**
- Only one load may be outstanding.  `ex_hold_o` stays high until `data_rvalid_i` arrives.
- Stores assert `data_req_o` for a single cycle; the design assumes a single-cycle write acceptance.

### `rv32i_wb_stage`
- **Location:** `rtl/core/pipeline/rv32i_wb_stage.sv`
- **Purpose:** Select write-back data source and gate register file writes.

| Port | Dir | Width | Description |
| --- | --- | --- | --- |
| `mem_valid_i` | in | 1 | Indicates `mem_payload_i` is valid. |
| `mem_payload_i` | in | `mem_wb_payload_t` | Payload from MEM. |
| `rd_we_o` | out | 1 | Register file write enable. |
| `rd_addr_o` | out | 5 | Destination register. |
| `rd_wdata_o` | out | 32 | Data to write (selected by `wb_sel`). |

### `rv32i_register_file`
- **Location:** `rtl/core/datapath/rv32i_register_file.sv`
- **Purpose:** Dual-read, single-write register file with x0 hard-wired to zero.

| Parameter | Default | Description |
| --- | --- | --- |
| `XLEN_P` | `32` | Width of each register. |
| `DEPTH_P` | `32` | Number of architectural registers. |
| `ADDR_WIDTH_P` | `$clog2(DEPTH_P)` | Address width override (must cover depth). |

| Port | Dir | Width | Description |
| --- | --- | --- | --- |
| `clk_i`, `rst_ni` | in | 1 | Clock/reset. |
| `rs1_addr_i`, `rs2_addr_i` | in | `ADDR_WIDTH_P` | Read addresses. |
| `rs1_data_o`, `rs2_data_o` | out | `XLEN_P` | Asynchronous read data (with same-cycle bypass). |
| `rd_we_i` | in | 1 | Write enable. |
| `rd_addr_i` | in | `ADDR_WIDTH_P` | Write address. |
| `rd_wdata_i` | in | `XLEN_P` | Write data. |

**Timing**
- Writes occur on the rising edge; asynchronous reads update immediately after the clock edge, including same-cycle bypass when addresses match and are non-zero.

## Functional sub-blocks

### `rv32i_decoder`
- **Location:** `rtl/core/decode/rv32i_decoder.sv`
- **Purpose:** Translate the 32-bit instruction into a packed `decode_ctrl_t` record.

| Port | Dir | Width | Description |
| --- | --- | --- | --- |
| `instr_i` | in | 32 | Instruction word. |
| `ctrl_o` | out | `decode_ctrl_t` | Control signals for downstream stages. |
| `illegal_o` | out | 1 | High when the instruction encoding is unsupported. |

### `rv32i_imm_gen`
- **Location:** `rtl/core/common/rv32i_imm_gen.sv`
- **Purpose:** Produce sign-extended immediates for all RV32I formats.

| Parameter | Default | Description |
| --- | --- | --- |
| `XLEN_P` | `XLEN` (32) | Output width (must be 32 in current implementation). |

| Port | Dir | Width | Description |
| --- | --- | --- | --- |
| `instr_i` | in | 32 | Instruction word. |
| `imm_type_i` | in | `imm_type_e` | Encoding type selected by decoder. |
| `imm_o` | out | `XLEN_P` | Sign-extended immediate value. |

### `rv32i_alu`
- **Location:** `rtl/core/common/rv32i_alu.sv`
- **Purpose:** Combinational ALU implementing RV32I arithmetic, logical, and comparison operations.

| Parameter | Default | Description |
| --- | --- | --- |
| `XLEN_P` | `XLEN` (32) | Operand/result width. |

| Port | Dir | Width | Description |
| --- | --- | --- | --- |
| `operand_a_i`, `operand_b_i` | in | `XLEN_P` | ALU operands. |
| `op_i` | in | `alu_op_e` | Operation selector. |
| `result_o` | out | `XLEN_P` | Computed result. |
| `cmp_eq_o`, `cmp_lt_o`, `cmp_ltu_o` | out | 1 | Comparison results reused for branching. |
| `result_ready_o`, `cmp_ready_o` | out | 1 | Always `1` in this single-cycle implementation (provided for future extensibility). |

### `rv32i_core_pkg`
- **Location:** `rtl/core/common/rv32i_core_pkg.sv`
- **Purpose:** Defines enums (`alu_op_e`, `imm_type_e`, `op_a_sel_e`, `op_b_sel_e`, `branch_type_e`, `mem_size_e`, `wb_sel_e`) and the pipeline payload structs used throughout the core.

**Integration notes**
- Import the package (`import rv32i_core_pkg::*;`) before referencing payload types or enums.

### `rv32i_hazard_unit` (optional)
- **Location:** `rtl/core/control/rv32i_hazard_unit.sv`
- **Purpose:** Detect load-use and structural hazards; intended for future integration.

| Parameter | Default | Description |
| --- | --- | --- |
| `ENABLE_ASSERTIONS` | `1'b1` | Compile-time switch for internal assertions. |

| Port | Dir | Width | Description |
| --- | --- | --- | --- |
| `clk_i`, `rst_ni` | in | 1 | Clock/reset. |
| `id_rs1_addr_i`, `id_rs2_addr_i` | in | 5 | Source registers in the ID stage. |
| `ex_rd_addr_i` | in | 5 | Destination register in EX stage. |
| `ex_regwrite_i` | in | 1 | EX stage writes a register. |
| `ex_memread_i` | in | 1 | EX stage is a load. |
| `pipeline_valid_i` | in | 3 | Valid bits for IF/ID, ID/EX, EX/MEM (implementation-specific). |
| `branch_flush_i` | in | 1 | Active when branch redirect in progress. |
| `structural_hazard_i` | in | 1 | External structural hazard indication. |
| `stall_o` | out | 1 | Request to stall younger stages. |
| `flush_o` | out | 1 | Flush signal overriding stall during branch redirects. |

### `rv32i_forwarding_unit` (optional)
- **Location:** `rtl/core/control/rv32i_forwarding_unit.sv`
- **Purpose:** Determine forwarding selections for EX operands based on MEM/WB destinations.

| Parameter | Default | Description |
| --- | --- | --- |
| `PRIORITIZE_MEM_STAGE` | `1'b1` | When set, MEM-stage matches outrank WB matches. |

| Port | Dir | Width | Description |
| --- | --- | --- | --- |
| `ex_rs1_addr_i`, `ex_rs2_addr_i` | in | 5 | EX-stage source register addresses. |
| `mem_rd_addr_i`, `mem_regwrite_i` | in | 5/1 | MEM-stage destination and write enable. |
| `wb_rd_addr_i`, `wb_regwrite_i` | in | 5/1 | WB-stage destination and write enable. |
| `forward_a_sel_o`, `forward_b_sel_o` | out | 2 | Selection codes in `forwarding_sel_e`. |

**Usage**
- The module is currently exercised only by the standalone hazard/forwarding test bench (`tb/src/rv32i_hazard_forward_tb.sv`).

## Wishbone interface components

All modules in this section import `rv32i_wb_pkg` and assume the classic Wishbone B4 handshake (single outstanding request per master).

### `rv32i_wb_instr_adapter`
- **Location:** `rtl/bus/rv32i_wb_instr_adapter.sv`
- **Purpose:** Convert the IF stage handshake into Wishbone master requests.

| Parameter | Default | Description |
| --- | --- | --- |
| `ADDR_WIDTH` | `WB_ADDR_WIDTH` (32) | Address width. |
| `DATA_WIDTH` | `WB_DATA_WIDTH` (32) | Data width. |

| Port | Dir | Width | Description |
| --- | --- | --- | --- |
| `clk_i`, `rst_ni` | in | 1 | Clock/reset. |
| `req_i` | in | 1 | Fetch request from core. |
| `addr_i` | in | `ADDR_WIDTH` | Word-aligned address. |
| `gnt_o` | out | 1 | Pulse when request is latched. |
| `rsp_valid_o` | out | 1 | Pulse with returned data. |
| `rsp_rdata_o` | out | `DATA_WIDTH` | Instruction word. |
| `rsp_err_o` | out | 1 | Indicates Wishbone error response. |
| `wb_cyc_o`, `wb_stb_o`, `wb_we_o` | out | 1 | Wishbone command. |
| `wb_sel_o` | out | `DATA_WIDTH/8` | Byte enables (always all ones). |
| `wb_adr_o` | out | `ADDR_WIDTH` | Wishbone address. |
| `wb_dat_o` | out | `DATA_WIDTH` | Unused (tied to zero). |
| `wb_dat_i`, `wb_ack_i`, `wb_err_i`, `wb_stall_i` | in | — | Standard Wishbone response signals. |

### `rv32i_wb_data_adapter`
- **Location:** `rtl/bus/rv32i_wb_data_adapter.sv`
- **Purpose:** Bridge the MEM stage handshake to Wishbone, handling byte enables and distinguishing load/store responses.

| Parameter | Default | Description |
| --- | --- | --- |
| `ADDR_WIDTH` | `WB_ADDR_WIDTH` | Address width. |
| `DATA_WIDTH` | `WB_DATA_WIDTH` | Data width. |

| Core-side ports |
| --- |
| `req_i`, `we_i`, `be_i`, `addr_i`, `wdata_i` (inputs) – request metadata. |
| `gnt_o` – pulses when the request is accepted (unused by core, available for future use). |
| `rsp_valid_o`, `rsp_rdata_o`, `rsp_err_o` – load response. |
| `store_complete_o`, `store_err_o` – store completion flags. |

| Wishbone ports |
| --- |
| `wb_cyc_o`, `wb_stb_o`, `wb_we_o`, `wb_sel_o`, `wb_adr_o`, `wb_dat_o` – command signals. |
| `wb_dat_i`, `wb_ack_i`, `wb_err_i`, `wb_stall_i` – response signals. |

**Protocol notes**
- Only one request may be pending.  The adapter asserts `wb_cyc_o`/`wb_stb_o` continuously until an acknowledge or error is observed.

### `rv32i_wb_arbiter`
- **Location:** `rtl/bus/rv32i_wb_arbiter.sv`
- **Purpose:** Grant the shared Wishbone bus to either the instruction or data master (data has priority).

| Parameter | Default | Description |
| --- | --- | --- |
| `ADDR_WIDTH` | `WB_ADDR_WIDTH` | Address width. |
| `DATA_WIDTH` | `WB_DATA_WIDTH` | Data width. |

| Ports | Description |
| --- | --- |
| Instruction master interface | Wishbone signals suffixed `_instr_*` (input from IF adapter, output responses). |
| Data master interface | Wishbone signals suffixed `_data_*` (input from data adapter, output responses). |
| Downstream bus interface | Wishbone signals suffixed `_bus_*` toward shared fabric. |

**Protocol notes**
- The arbiter grants the bus to one master at a time until that master observes `ack` or `err`.  Instruction requests are stalled when the data port is active.

### `rv32i_wb_router`
- **Location:** `rtl/bus/rv32i_wb_router.sv`
- **Purpose:** Decode address ranges and steer transfers to instruction ROM vs data RAM.

| Parameter | Default | Description |
| --- | --- | --- |
| `ADDR_WIDTH` | `WB_ADDR_WIDTH` | Address width. |
| `DATA_WIDTH` | `WB_DATA_WIDTH` | Data width. |
| `IMEM_BASE_ADDR` | `32'h0000_0000` | Base address of instruction memory window. |
| `IMEM_DEPTH_WORDS` | `4096` | Instruction memory depth (words). |
| `DMEM_BASE_ADDR` | `32'h8000_0000` | Base address of data memory window. |
| `DMEM_DEPTH_WORDS` | `4096` | Data memory depth (words). |

| Port | Dir | Width | Description |
| --- | --- | --- | --- |
| `m_*` | in/out | — | Master-facing Wishbone port (from arbiter). |
| `imem_*` | out/in | — | Instruction memory Wishbone port. |
| `dmem_*` | out/in | — | Data memory Wishbone port. |

**Protocol notes**
- If an access targets neither window, the router raises `m_err_o`/`m_ack_o` for a single cycle without forwarding the request.

## Verification memory models

### `rv32i_imem_model`
- **Location:** `tb/src/rv32i_imem_model.sv`
- **Purpose:** Behavioural instruction ROM with optional deterministic or random wait states.

| Parameter | Default | Description |
| --- | --- | --- |
| `NAME` | "imem" | Identifier shown in log messages. |
| `MEM_DEPTH_WORDS` | `4096` | Number of 32-bit words stored. |
| `BASE_ADDR` | `32'h0000_0000` | Base address expected by the router. |
| `FIXED_WAIT_CYCLES` | `0` | Deterministic latency before acknowledging requests. |
| `ENABLE_RANDOM_WAIT` | `1'b0` | When set, adds pseudo-random delay up to `RANDOM_WAIT_MAX`. |
| `RANDOM_WAIT_MAX` | `0` | Maximum additional wait cycles when random wait enabled. |
| `RANDOM_SEED` | `32'h1` | Seed for the LFSR used to generate random waits. |

| Port | Dir | Width | Description |
| --- | --- | --- | --- |
| `clk_i`, `rst_ni` | in | 1 | Clock/reset. |
| `wb_cyc_i`, `wb_stb_i`, `wb_we_i`, `wb_sel_i`, `wb_adr_i`, `wb_dat_i` | in | — | Wishbone command (writes are illegal). |
| `wb_dat_o`, `wb_ack_o`, `wb_err_o`, `wb_stall_o` | out | — | Wishbone response. |

**Tasks / functions**
- `clear_memory(value)` – initialise memory contents.
- `load_hex(path)` – load a hex file via `$readmemh`.

### `rv32i_dmem_model`
- **Location:** `tb/src/rv32i_dmem_model.sv`
- **Purpose:** Behavioural data RAM with optional wait states and store monitoring.

| Parameter | Default | Description |
| --- | --- | --- |
| (Same as instruction model) plus: |
| `RANDOM_SEED` | `32'hc001c0de` | Independent seed for data PRNG. |

| Port | Dir | Width | Description |
| --- | --- | --- | --- |
| Wishbone command inputs | Same semantics as the instruction model. |
| `store_valid_o` | out | 1 | Pulses when a store completes. |
| `store_addr_o`, `store_data_o` | out | 32 | Captured store information (used by scoreboard). |

**Tasks / functions**
- `clear_memory(value)` – initialise contents. |
- `load_hex(path)` – load a memory image. |

## Scoreboard and testbench utilities

Although not synthesizable, two SystemVerilog helper modules participate in simulation and are often extended alongside RTL changes:

- `rv32i_scoreboard` (`tb/src/rv32i_scoreboard.sv`): consumes store events, compares them against expectation files, and reports pass/fail.  Exposes `set_expectation_file()` and `load_expectations()` tasks.
- `rv32i_tb_pkg` (`tb/src/pkg/rv32i_tb_pkg.sv`): utility functions for string handling, expectation parsing, and environment configuration shared across testbenches.

## Usage patterns

- **Replacing the bus fabric:** Integrators targeting AXI, AHB, or another bus can substitute alternative adapters provided they preserve the single-outstanding-transaction contract expected by the pipeline stages.
- **Augmenting hazard logic:** When connecting the optional `rv32i_hazard_unit` and `rv32i_forwarding_unit`, route the register indices from the pipeline payloads (`id_ex_payload_t.rs*`, `ex_mem_payload_t.rd_addr`, etc.) as described above.  The units operate purely on register numbers and write-enable bits.
- **Register file customisation:** `rv32i_register_file` is parameterised for depth and width, enabling experimentation with register windowing or 64-bit paths.  Enforce the assertions when changing parameters.
- **Memory wait-state testing:** Toggle `FIXED_WAIT_CYCLES` or enable random waits in the memory models to stress the stall logic in IF and MEM stages.

Refer back to [`timing_diagrams.md`](timing_diagrams.md) for temporal examples of these interfaces in action.
