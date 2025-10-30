# Architecture Design Document

This document captures the realised micro-architecture of the `rv32i_core` contained in this repository.  It is intended to serve as a living reference for architects, RTL designers, and verification engineers working on the core or integrating it into a system-on-chip.

- [`module_interfaces.md`](module_interfaces.md) provides detailed port-level specifications for every RTL block.
- [`timing_diagrams.md`](timing_diagrams.md) complements this document with cycle-accurate waveforms for key scenarios.

## Overall Architecture Overview

### High-level organisation

```
               +------------------+   IF/ID   +------------------+
   instr_* --->| Instruction Fetch |---------->| Instruction      |
               | (rv32i_if_stage)  |          | Decode (ID)      |
               +------------------+           | rv32i_id_stage   |
                                               +------------------+
                                                        |
                                                        v
                                               +------------------+
                                               | Execute (EX)     |
                                               | rv32i_ex_stage   |
                                               +------------------+
                                                        |
                                                        v
                                               +------------------+
                                               | Memory (MEM)     |
   data_*  <-----------------------------------| rv32i_mem_stage  |
                                               +------------------+
                                                        |
                                                        v
                                               +------------------+
                                               | Write-back (WB)  |
                                               | rv32i_wb_stage   |
                                               +------------------+
```

The core implements a classic five-stage in-order pipeline.  Instruction fetch and data memory traffic leave the core through lightweight ready/valid style interfaces.  Simulation harnesses adapt those ports onto a 32-bit Wishbone fabric using the wrappers in `rtl/bus/`.

### Data-flow and control-flow highlights

- **Program counter management** lives entirely inside the IF stage.  Branch and jump outcomes from EX redirect fetch and flush younger pipeline stages.
- **Instruction decode** generates a rich control payload (`id_ex_payload_t`) that flows forward unchanged until the values are either consumed by the ALU, the MEM stage, or the WB stage.
- **Write-back selection** happens in the WB stage based on the `wb_sel` field that the decoder produced.  No additional prioritisation logic is required because only one source is ever enabled at a time.
- **Pipeline control** is deliberately simple: the MEM stage can back-pressure the entire pipe when a load is outstanding, and the EX stage can request flushes for taken branches and jumps.

### Design philosophy and key decisions

- **Transparency over micro-optimisation.**  The design favours readability and explicit pipeline payloads over tightly-packed control signals.
- **Modularity.**  Each stage and major function (decoder, register file, ALU, immediates) lives in its own module to make unit-level verification straightforward.
- **Deterministic memory handshakes.**  The core assumes single outstanding transactions per instruction/data port.  The Wishbone adapters enforce this behaviour during simulation.
- **Incremental hazard support.**  Load-use stalls and branch flushes are handled in hardware.  Optional forwarding and generic hazard detection units exist in `rtl/core/control/` but are not wired into `rv32i_core` yet, keeping the main datapath easy to reason about while the hazard strategy evolves.

## Five-stage pipeline detailed description

### Instruction Fetch (IF)
- **Module:** `rv32i_if_stage`
- **Responsibilities:** maintain the program counter, issue fetch requests, buffer one instruction, and honour redirects and pipelines stalls.
- **Interfaces:** ready/valid handshake (`instr_req_o`, `instr_gnt_i`, `instr_rvalid_i`) with a single-word buffer to decouple the bus from the rest of the pipeline.
- **Redirect handling:** when EX reports a taken branch or jump, the IF stage discards the buffered instruction, redirects the PC, and drops the next response from memory if it is already in flight.
- **Stall behaviour:** `stall_i` (tied to the MEM stage hold request) freezes the PC and prevents fetch requests from being issued.

### IF/ID pipeline register
Implemented with `rv32i_pipeline_reg#(if_id_payload_t)`.  The payload contains the fetch PC and instruction bits.  Flushes from IF turn the entry invalid, guaranteeing that no wrong-path instructions reach decode.

`if_id_payload_t`

| Field | Width | Description |
| --- | --- | --- |
| `pc` | 32 | Address of the fetched instruction. |
| `instr` | 32 | Raw instruction word. |

### Instruction Decode (ID)
- **Module:** `rv32i_id_stage`
- **Submodules:** `rv32i_decoder`, `rv32i_imm_gen`.
- **Responsibilities:** decode opcodes, produce the full `id_ex_payload_t`, read source operands from the register file, and raise an error on illegal instructions (terminating simulation via `fatal`).
- **Register file access:** asynchronous reads with same-cycle bypass for write-after-read hazards (`rv32i_register_file`).

`id_ex_payload_t` (selected fields)

| Field | Width | Description |
| --- | --- | --- |
| `pc`, `pc_plus4` | 32 | Current PC and PC+4 for link write-back. |
| `instr` | 32 | Instruction word (for tracing/debug). |
| `imm` | 32 | Sign-extended immediate generated by `rv32i_imm_gen`. |
| `rs1_data`, `rs2_data` | 32 | Source operand values. |
| `rs1_addr`, `rs2_addr`, `rd_addr` | 5 | Architectural register indices. |
| `op_a_sel`, `op_b_sel` | 2 | Operand mux selectors for the ALU. |
| `alu_op` | 5 | ALU opcode (see `rv32i_alu`). |
| `wb_sel` | 2 | Selects the source used during write-back. |
| `branch_type`, `branch`, `jump`, `jalr` | — | Branch/jump control. |
| `mem_read`, `mem_write`, `mem_size`, `mem_unsigned` | — | Memory request attributes. |
| `reg_write` | 1 | Enables register write-back downstream. |

### ID/EX pipeline register
Also instantiated via `rv32i_pipeline_reg`.  Flushes from EX (branch redirects) nuke the entry to prevent younger instructions from using stale control bits.

### Execute (EX)
- **Module:** `rv32i_ex_stage`
- **Submodule:** `rv32i_alu`.
- **Operand selection:** uses `op_a_sel`/`op_b_sel` to choose between `rs` values, immediates, `PC`, or constants.
- **ALU operations:** cover the full RV32I arithmetic/logical set.  Comparison results (`cmp_eq`, `cmp_lt`, `cmp_ltu`) are reused for branch decisions.
- **Branch resolution:** taken when `branch` is high and the requested comparison evaluates true, or when any jump bit is asserted.  JALR targets are forced even-aligned per the spec.
- **Outputs:** `ex_mem_payload_t` carries the ALU result, control bits, and the original RS2 data (for stores).

`ex_mem_payload_t`

| Field | Width | Description |
| --- | --- | --- |
| `pc`, `pc_plus4` | 32 | Original PC information for link write-back. |
| `alu_result` | 32 | Result of ALU computation or effective address. |
| `rs2_data` | 32 | Store data forwarded into MEM. |
| `rd_addr` | 5 | Destination register for write-back. |
| `wb_sel`, `mem_read`, `mem_write`, `mem_size`, `mem_unsigned`, `reg_write` | — | Latched control for MEM/WB. |
| `branch_type`, `branch`, `jump`, `jalr` | — | For reference or optional downstream logic. |

### EX/MEM pipeline register
Holds the EX payload until the MEM stage is ready to consume it.  This register honours the hold signal sourced by the MEM stage to keep the operands stable while a load is pending.

### Memory (MEM)
- **Module:** `rv32i_mem_stage`.
- **Responsibilities:** drive memory requests, hold the pipeline steady while a load is outstanding, and package results for write-back.
- **Read path:** On a load, a single request is launched and the stage waits for `data_rvalid_i`.  Returned data is aligned/extended according to `mem_size` and `mem_unsigned`.
- **Write path:** Stores emit byte enables via `mem_size_to_be` and pass RS2 data with appropriate byte steering.  Stores do not stall the pipeline once the request has been issued.
- **Hold behaviour:** `ex_hold_o` asserts during the cycle that a load is launched and remains high until the response arrives, freezing all upstream pipeline registers.

`mem_wb_payload_t`

| Field | Width | Description |
| --- | --- | --- |
| `pc`, `pc_plus4` | 32 | Pass-through for potential debug/tracing. |
| `alu_result` | 32 | Forwarded ALU result (used for ALU ops and addresses). |
| `mem_rdata` | 32 | Load data after alignment/extension. |
| `rd_addr` | 5 | Destination register. |
| `wb_sel` | 2 | Determines write-back source. |
| `reg_write` | 1 | Enables the WB stage write. |

### MEM/WB pipeline register
No hold/flush controls are required because the MEM stage already enforces back-pressure.  Data flows straight into WB on the following cycle.

### Write-back (WB)
- **Module:** `rv32i_wb_stage`.
- **Responsibilities:** select the correct write-back value (`alu_result`, `mem_rdata`, or `pc_plus4`) and gate register writes to avoid x0 modifications.
- **Register file updates:** happen on the rising clock edge when `mem_valid_i` is asserted, landing in `rv32i_register_file`.

## Module hierarchy

```
rv32i_core
├── rv32i_if_stage
├── rv32i_pipeline_reg (IF/ID)
├── rv32i_id_stage
│   ├── rv32i_decoder
│   └── rv32i_imm_gen
├── rv32i_pipeline_reg (ID/EX)
├── rv32i_ex_stage
│   └── rv32i_alu
├── rv32i_pipeline_reg (EX/MEM)
├── rv32i_mem_stage
├── rv32i_pipeline_reg (MEM/WB)
├── rv32i_wb_stage
└── rv32i_register_file
```

Supporting infrastructure used by the top-level simulation harness lives outside the core hierarchy:

- `rtl/bus`: Wishbone adapters (`rv32i_wb_instr_adapter`, `rv32i_wb_data_adapter`), arbiter, and address router.
- `tb/src`: behavioural instruction/data memory models plus the scoreboard.
- `rtl/core/control`: standalone hazard detection and forwarding units (currently unconnected to the pipeline but available for future integration or external experiments).

### Responsibility matrix

| Module | Location | Primary responsibilities |
| --- | --- | --- |
| `rv32i_if_stage` | `rtl/core/pipeline` | PC sequencing, fetch buffering, redirect and stall handling. |
| `rv32i_id_stage` | `rtl/core/pipeline` | Decode, immediate generation, operand collection. |
| `rv32i_decoder` | `rtl/core/decode` | Translate instruction fields into control micro-ops. |
| `rv32i_imm_gen` | `rtl/core/common` | Produce sign-extended immediates for I/S/B/U/J forms. |
| `rv32i_alu` | `rtl/core/common` | Execute arithmetic/logical operations and comparisons. |
| `rv32i_ex_stage` | `rtl/core/pipeline` | Operand selection, ALU invocation, branch resolution. |
| `rv32i_mem_stage` | `rtl/core/pipeline` | Drive load/store requests, align data, stall pipeline on load latency. |
| `rv32i_wb_stage` | `rtl/core/pipeline` | Select write-back value and drive register file update. |
| `rv32i_register_file` | `rtl/core/datapath` | Dual-read, single-write register file with x0 hard-wired to zero and read-after-write bypass. |
| `rv32i_pipeline_reg` | `rtl/core/pipeline` | Parameterised valid/data pipeline register with hold/flush controls. |
| `rv32i_wb_*` adapters | `rtl/bus` | Convert core-side valid/ready semantics to Wishbone master transactions. |
| `rv32i_wb_router` | `rtl/bus` | Decode instruction vs data address ranges and steer to memories. |
| `rv32i_hazard_unit` | `rtl/core/control` | Standalone load-use/structural hazard detector (not wired into `rv32i_core`). |
| `rv32i_forwarding_unit` | `rtl/core/control` | Standalone forwarding selector (used in unit tests only today). |

## Instruction set support matrix

The decoder in `rv32i_decoder.sv` implements the full RV32I base ISA (minus system-level CSR operations).  The table below summarises each instruction family.

### R-type

| Instruction | Encoding (`opcode`/`funct3`/`funct7`) | Operation | Notes |
| --- | --- | --- | --- |
| `ADD` | `0110011 / 000 / 0000000` | `rd ← rs1 + rs2` | |
| `SUB` | `0110011 / 000 / 0100000` | `rd ← rs1 - rs2` | |
| `SLL` | `0110011 / 001 / 0000000` | Logical left shift by `rs2[4:0]`. | |
| `SLT` | `0110011 / 010 / 0000000` | Signed compare, result in bit 0. | |
| `SLTU` | `0110011 / 011 / 0000000` | Unsigned compare. | |
| `XOR` | `0110011 / 100 / 0000000` | Bitwise XOR. | |
| `SRL` | `0110011 / 101 / 0000000` | Logical right shift. | |
| `SRA` | `0110011 / 101 / 0100000` | Arithmetic right shift. | |
| `OR` | `0110011 / 110 / 0000000` | Bitwise OR. | |
| `AND` | `0110011 / 111 / 0000000` | Bitwise AND. | |

### I-type (ALU immediates & shift-immediates)

| Instruction | Encoding | Operation | Notes |
| --- | --- | --- | --- |
| `ADDI` | `0010011 / 000` | `rd ← rs1 + imm[11:0]`. | |
| `SLTI` | `0010011 / 010` | Signed compare against imm. | |
| `SLTIU` | `0010011 / 011` | Unsigned compare against imm. | |
| `XORI` | `0010011 / 100` | Bitwise XOR with imm. | |
| `ORI` | `0010011 / 110` | Bitwise OR with imm. | |
| `ANDI` | `0010011 / 111` | Bitwise AND with imm. | |
| `SLLI` | `0010011 / 001 / 0000000` | Shift left logical (imm[4:0]). | Illegal if `funct7 ≠ 0` (trap during simulation). |
| `SRLI` | `0010011 / 101 / 0000000` | Shift right logical (imm[4:0]). | |
| `SRAI` | `0010011 / 101 / 0100000` | Shift right arithmetic. | |

### I-type (loads & JALR)

| Instruction | Encoding | Operation | Notes |
| --- | --- | --- | --- |
| `LB` / `LH` / `LW` | `0000011 / 000,001,010` | Byte/half/word load with sign extension. | |
| `LBU` / `LHU` | `0000011 / 100,101` | Unsigned byte/half load. | |
| `JALR` | `1100111 / 000` | Jump to `(rs1 + imm) & ~1`, write link to `rd`. | Treated as taken branch in EX.

### S-type

| Instruction | Encoding | Operation | Notes |
| --- | --- | --- | --- |
| `SB` | `0100011 / 000` | Store byte. | |
| `SH` | `0100011 / 001` | Store half-word. | |
| `SW` | `0100011 / 010` | Store word. | |

### B-type

| Instruction | Encoding | Branch condition |
| --- | --- | --- |
| `BEQ` | `1100011 / 000` | Taken if `rs1 == rs2`. |
| `BNE` | `1100011 / 001` | Taken if `rs1 != rs2`. |
| `BLT` | `1100011 / 100` | Taken if `rs1 < rs2` (signed). |
| `BGE` | `1100011 / 101` | Taken if `rs1 ≥ rs2` (signed). |
| `BLTU` | `1100011 / 110` | Taken if `rs1 < rs2` (unsigned). |
| `BGEU` | `1100011 / 111` | Taken if `rs1 ≥ rs2` (unsigned). |

### U/J-type and fence

| Instruction | Encoding | Operation |
| --- | --- | --- |
| `LUI` | `0110111` | Load upper immediate into `rd`. |
| `AUIPC` | `0010111` | Add upper immediate to PC into `rd`. |
| `JAL` | `1101111` | Jump and link (PC-relative). |
| `FENCE` | `0001111` | Recognised but treated as a no-op (no memory ordering side-effects implemented). |

All other opcodes are flagged as illegal in simulation.  CSR, privileged, and multiplication/division extensions are not currently implemented.

## Hazard handling

### Data hazards
- **Register file bypass:** `rv32i_register_file` returns freshly written data when a read address matches the write port in the same cycle.  This resolves write-back-to-decode hazards once the producer reaches WB.
- **Load-use handling:** `rv32i_mem_stage` asserts `ex_hold_o` from the cycle a load request is issued until its data returns.  The hold freezes IF, ID, and EX, inserting the necessary bubble.
- **Forwarding:** No inter-stage forwarding is wired into `rv32i_core` today.  The optional `rv32i_forwarding_unit` models a MEM/WB forwarding policy and is exercised in isolation by unit tests, providing a path for future integration.

### Control hazards
- Branches and jumps resolve in EX.  When taken, both IF and ID pipeline registers are flushed and the IF stage redirects the PC.  There is no prediction—every taken branch incurs a two-cycle bubble.

### Structural hazards
- The pipeline assumes a single memory access can be in flight on each port.  The MEM stage enforces this rule for data loads, while the IF stage serialises fetch requests.  Additional structural hazard inputs can be provided via the optional `structural_hazard_i` port on `rv32i_hazard_unit` (external to the core).

## Memory interface architecture

### Core-facing interface

- **Instruction port:** request/response handshake with separate grant (`instr_gnt_i`) and data valid (`instr_rvalid_i`) signals.  Only one outstanding fetch is supported.  The IF stage provides a single-entry buffer so the rest of the pipeline only sees ready/valid semantics.
- **Data port:** request/response handshake consisting of `data_req_o`, write strobes, address/data, and `data_rvalid_i`.  Loads stall the pipeline until the response arrives; stores complete once the request is accepted.

### Wishbone adaptation in simulation

The testbench bridges the core ports onto a 32-bit Wishbone fabric:

1. `rv32i_wb_instr_adapter` and `rv32i_wb_data_adapter` turn the stage-level handshakes into Wishbone master commands while guaranteeing there is only one active request per port.
2. `rv32i_wb_arbiter` grants the data port priority over instruction fetches when both request the shared downstream bus.
3. `rv32i_wb_router` decodes addresses into independent instruction (ROM) and data (RAM) spaces: instruction memory at `0x0000_0000`, data memory at `0x8000_0000`.
4. Behavioural memory models (`rv32i_imem_model`, `rv32i_dmem_model`) provide simple synchronous storage with optional wait-state injection.

The core itself is agnostic of Wishbone.  Integrators can replace the adapters with any protocol that provides equivalent ready/valid semantics.

## Pipeline timing diagrams

Representative cycle-accurate traces for the scenarios listed below are maintained in [`timing_diagrams.md`](timing_diagrams.md):

1. Single instruction flowing through all five stages.
2. Back-to-back independent instructions.
3. Read-after-write hazard with the optional forwarding unit.
4. Load-use hazard demonstrating the MEM-induced stall.
5. Taken branch causing IF/ID flush.
6. Memory transactions (fetch, load, store, back-to-back accesses) and register file read/write behaviour.

Refer to that document when reasoning about latency, bubbles, and handshake timing.

## Interrupts, debug, and status

`rv32i_core` exposes timer, external, and software interrupt inputs as well as a debug request.  None of these are consumed internally yet; they remain stubs so the interface is ready for future expansion.  The `dbg_halted_o` signal is permanently driven low.

## Future work

- Integrate the existing hazard and forwarding units directly into the pipeline.
- Introduce CSR support and an exception/interrupt pipeline.
- Add optional caches and multi-entry fetch/data buffers to improve throughput under memory latency.
- Extend the verification environment to cover hazard corner cases and long-latency memory scenarios.
