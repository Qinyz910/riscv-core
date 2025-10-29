# RISC-V Core Architecture Design

## Overview

This document captures the architecture of the `riscv-core` project: a five-stage, in-order, single-issue RISC-V core designed around the RV32I base integer instruction set with optional M, C, and CSR extensions. The design prioritizes clarity and pedagogy while leaving room for future performance and feature enhancements. The sections below describe the pipeline structure, module hierarchy, instruction coverage, hazard management strategy, and representative timing diagrams that illustrate how instructions move through the machine.

## Five-Stage Pipeline

The core follows the classic five-stage RISC pipeline. Each stage has a well-defined interface that isolates functionality and simplifies timing closure.

1. **Instruction Fetch (IF)**
   - Maintains the Program Counter (PC) and generates instruction fetch requests to the instruction memory interface.
   - Implements branch prediction bypass (static not-taken) by default and accepts redirect requests from later stages.
   - Captures instruction words into the IF/ID pipeline register together with the fetch PC and prediction metadata.

2. **Instruction Decode (ID)**
   - Decodes the instruction word into opcode, funct3/funct7 fields, immediate values, and control signals.
   - Reads operands from the register file and enqueues CSR requests when applicable.
   - Performs early hazard detection (stall or flush decisions for load-use and control hazards).
   - Generates control bundles for later stages and populates the ID/EX pipeline register.

3. **Execute (EX)**
   - Hosts the Arithmetic Logic Unit (ALU), multiplier/divider (optional `M` extension), branch condition evaluation, and effective address calculation for memory operations.
   - Accepts forwarding data from MEM and WB stages to resolve RAW hazards.
   - Produces branch resolution information (taken/target) that may trigger pipeline redirects.

4. **Memory (MEM)**
   - Interfaces with the data memory subsystem via an AXI-lite inspired request/response channel.
   - Handles load/store alignment, byte-enable generation, and sign/zero extension for load results.
   - Provides memory stage results to MEM/WB pipeline register and forwards data back to EX when necessary.

5. **Write-Back (WB)**
   - Arbitrates between ALU, multiplier/divider, memory, and CSR results for commitment to the register file.
   - Validates writes against CSR side effects and ensures x0 remains hardwired to zero.

### Pipeline Registers

Each adjacent pair of stages is separated by a pipeline register capturing data, control, and validity bits. These registers also hold exception metadata, instruction identifiers, and scoreboard state to facilitate precise exception handling and debug visibility.

## Module Hierarchy

The RTL hierarchy is organized to keep leaf-level logic cohesive and reusable. The expected module breakdown is shown below:

```
core_top
├── if_stage
│   ├── pc_update
│   └── icache_if (optional)
├── id_stage
│   ├── decoder
│   ├── register_file
│   └── hazard_unit
├── ex_stage
│   ├── alu
│   ├── muldiv_unit (optional)
│   └── branch_unit
├── mem_stage
│   ├── dcache_if (optional)
│   ├── load_store_unit
│   └── axi_lite_master
├── wb_stage
│   ├── result_mux
│   └── csr_unit
└── control
    ├── forwarding_unit
    ├── pipeline_registers
    └── exception_unit
```

### Top-Level Integration

- **`core_top`**: Instantiates all pipeline stages, connects pipeline registers, and binds instruction/data memory interfaces. Exposes debug, interrupt, and CSR ports to the SoC fabric.
- **Fetch Subsystem**: Responsible for PC sequencing, instruction memory protocol conversion, and optional instruction cache integration.
- **Decode Subsystem**: Houses the register file and the hazard detection logic that orchestrates stalls/bubbles.
- **Execute Subsystem**: Implements arithmetic, logic, multiply/divide (when enabled), and branch condition evaluation.
- **Memory Subsystem**: Converts pipeline memory requests into AXI-lite (or generic ready/valid) transactions and manages memory responses.
- **Control & Debug**: Centralizes forwarding, exceptions, and CSR-related control, ensuring consistent status reporting.

## Instruction Support Matrix

The table below enumerates the planned instruction coverage. "Y" indicates complete support, "Config" indicates build-time optionality, and "Roadmap" notes future work.

| Instruction Class           | RV32I | RV32M | RV32C | CSR | Notes                                  |
|-----------------------------|:-----:|:-----:|:-----:|:---:|----------------------------------------|
| Integer Register-Register   |   Y   |   –   |   –   |  –  | `ADD`, `SUB`, `XOR`, `OR`, `AND`       |
| Integer Register-Immediate  |   Y   |   –   |   –   |  –  | `ADDI`, `SLTI`, `ORI`, `ANDI`          |
| Shifts                      |   Y   |   –   |   –   |  –  | `SLL`, `SRL`, `SRA`, immediate forms   |
| Control-Flow                |   Y   |   –   |   –   |  –  | Branches, `JAL`, `JALR`                |
| Load/Store                  |   Y   |   –   |   –   |  –  | Byte, halfword, word with alignment    |
| Fences & System             |   Y   |   –   |   –   |  Y  | `FENCE`, `FENCE.I`, `ECALL`, `EBREAK`  |
| Multiply/Divide             |   –   | Config|   –   |  –  | Optional `M` extension unit            |
| Compressed Instructions     |   –   |   –   | Config|  –  | Optional C-extension front-end support |
| CSR Access                  |   –   |   –   |   –   |  Y  | `CSRRW`, `CSRRS`, `CSRRC`, immediates  |
| Privileged Mode (S/U)       |   –   |   –   |   –   |Roadmap| Supervisor support under evaluation |

## Hazard Management

- **Data Hazards**: Resolved using forwarding from MEM and WB to EX. Load-use hazards trigger a single-cycle bubble when data is not yet available.
- **Control Hazards**: Branches are resolved in EX. A taken branch or jump flushes IF and ID, incurring a two-cycle penalty with static not-taken prediction. Future enhancements may introduce a one-bit predictor in IF.
- **Structural Hazards**: Avoided by design through single-issue pipeline and separate instruction/data interfaces.

## Memory Subsystem & CSR Interaction

- **Memory Interface**: A simple ready/valid protocol (compatible with AXI-lite concepts) handles instruction and data accesses. The interface supports byte-enable signaling for sub-word operations and accepts back-pressure from downstream memory.
- **CSR Unit**: Provides access to machine-mode CSRs, including `mstatus`, `mtvec`, `mepc`, `mcause`, and `mtime`. CSR side effects (e.g., interrupts, exceptions) propagate control signals back to IF to redirect execution.

## Pipeline Timing Diagrams

### Back-to-Back ALU Instructions

```
Cycle ->   1    2    3    4    5    6
Instr 1:  IF | ID | EX | MEM | WB
Instr 2:       IF | ID | EX | MEM | WB
Instr 3:            IF | ID | EX | MEM | WB
```

Forwarding from MEM/WB to EX allows instructions 2 and 3 to proceed without stalls.

### Load-Use Hazard

```
Cycle ->   1    2    3    4    5    6    7
Load:     IF | ID | EX | MEM | WB
Use:           IF | ID | ST | EX | MEM | WB
```

`ST` indicates a stall bubble inserted by the hazard unit while waiting for the load data to be written back. The forwarding path from MEM provides the value in cycle 5, enabling the dependent instruction to resume in EX during cycle 6.

### Taken Branch

```
Cycle ->   1    2    3    4    5    6
Branch:   IF | ID | EX | MEM | WB
Next PC:       IF | FL | FL | IF | ID | EX
```

`FL` marks flushed instructions in IF/ID due to a taken branch. The new target PC is issued from EX at cycle 3, and IF restarts with the redirected address in cycle 4.

## Design Rationale & Future Enhancements

- **Modularity** eases verification and allows optional units (e.g., multiplier) to be plugged in without perturbing the base pipeline.
- **Parameterization** (data-width, reset vector, interface selection) enables integration in diverse SoC environments.
- **Roadmap** considerations include adding branch prediction, instruction/data caches, privileged mode support, and an MMU layer.

## References

- RISC-V User-Level ISA Specification (Volume I: Unprivileged ISA)
- RISC-V Privileged Architecture Specification
- "Computer Organization and Design RISC-V Edition" by Patterson & Hennessy
