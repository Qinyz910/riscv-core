# User Guide

This guide describes how to set up the development environment, run simulations, exercise the supplied test programs, and extend the RV32I core.  Use it alongside [`architecture.md`](architecture.md) and [`module_interfaces.md`](module_interfaces.md) when making RTL or verification changes.

## Introduction

The repository contains a modular, five-stage RV32I core, behavioural Wishbone infrastructure, and self-checking SystemVerilog testbenches.  The focus is on readability and extensibility: every pipeline stage lives in its own module, and the verification harness is designed to run on open-source (Icarus Verilog) or commercial simulators.

### Feature summary

- RV32I integer instruction set with full load/store, branch, and jump support.
- Five-stage in-order pipeline with load-use stalls and branch flushes.
- Wishbone-compatible wrappers for both instruction and data ports.
- Behavioural instruction/data memories with optional wait states.
- Scoreboard-based top-level testbench that checks architectural state by monitoring stores.
- Unit-level simulations for the decoder and hazard/forwarding helpers.

### System requirements

| Component | Notes |
| --- | --- |
| Python 3.8+ | Required for helper scripts and pytest-based regression. |
| `pip install -r tests/requirements.txt` | (If present) ensures pytest and utilities are available. |
| RV32I toolchain (GNU) | `riscv64-unknown-elf-gcc` and `objcopy` used to regenerate test programs. |
| Icarus Verilog (`iverilog`, `vvp`) | Used by the supplied pytest tests; alternatively substitute your preferred simulator. |
| GTKWave or other waveform viewer | Optional, for debugging VCD/VPD dumps produced by the benches. |

> **Tip:** The environment variables `RISCV_PREFIX`, `RISCV_GCC`, and `RISCV_OBJCOPY` can be used to point at non-default toolchain installs (see [`tests/build_hex.py`](../tests/build_hex.py)).

## Repository structure

| Path | Description |
| --- | --- |
| `rtl/core/` | Core RTL, split into `pipeline/`, `decode/`, `common/`, and `datapath/`. |
| `rtl/bus/` | Wishbone adapters, arbiter, and router used by the testbench. |
| `tb/` | SystemVerilog testbenches, behavioural memories, and scoreboards. |
| `tests/` | Python-based regression entry points and RV32I assembly programs. |
| `docs/` | This documentation set. |
| `sim/` | Placeholder directories for tool-specific build recipes (Verilator, VCS, etc.). |

## Build and simulation flow

### 1. Clone and configure

```bash
git clone <repo-url>
cd <repo-name>
python3 -m venv .venv
source .venv/bin/activate
pip install -r tests/requirements.txt  # if the file exists
```

Set the project root for simulations that rely on plusargs:

```bash
export PROJECT_ROOT="$(pwd)"
```

### 2. Run unit-level simulations (pytest)

Two pytest targets exercise individual modules using Icarus Verilog.  They automatically skip if the toolchain is missing.

```bash
python -m pytest tests/test_decoder_tb.py
python -m pytest tests/test_hazard_forwarding.py
```

Each test compiles the necessary RTL into a temporary directory and runs `vvp` on the resulting image.

### 3. Run the top-level core testbench manually (Icarus example)

The top-level testbench lives at `tb/src/rv32i_core_tb_top.sv`.  The following sequence compiles it with Icarus Verilog:

```bash
mkdir -p build/icarus
iverilog -g2012 -o build/icarus/rv32i_core_tb.vvp \
    rtl/core/common/rv32i_core_pkg.sv \
    rtl/core/common/rv32i_alu.sv \
    rtl/core/common/rv32i_imm_gen.sv \
    rtl/core/decode/rv32i_decoder.sv \
    rtl/core/datapath/rv32i_register_file.sv \
    rtl/core/pipeline/rv32i_pipeline_reg.sv \
    rtl/core/pipeline/rv32i_if_stage.sv \
    rtl/core/pipeline/rv32i_id_stage.sv \
    rtl/core/pipeline/rv32i_ex_stage.sv \
    rtl/core/pipeline/rv32i_mem_stage.sv \
    rtl/core/pipeline/rv32i_wb_stage.sv \
    rtl/core/rv32i_core.sv \
    rtl/bus/rv32i_wb_pkg.sv \
    rtl/bus/rv32i_wb_instr_adapter.sv \
    rtl/bus/rv32i_wb_data_adapter.sv \
    rtl/bus/rv32i_wb_arbiter.sv \
    rtl/bus/rv32i_wb_router.sv \
    tb/src/pkg/rv32i_tb_pkg.sv \
    tb/src/rv32i_imem_model.sv \
    tb/src/rv32i_dmem_model.sv \
    tb/src/rv32i_scoreboard.sv \
    tb/src/rv32i_core_tb_top.sv
vvp build/icarus/rv32i_core_tb.vvp +TEST=smoke +PROJECT_ROOT=$PROJECT_ROOT
```

Supported `+` plusargs:

| Argument | Default | Description |
| --- | --- | --- |
| `+TEST=<name>` | `smoke` | Selects the program in `tb/programs/<name>.hex`. |
| `+PROGRAM=<path>` | derived | Override program hex path. |
| `+EXPECT=<path>` | derived | Override expectation file. |
| `+DMEM=<path>` | unset | Optional data memory preload. |
| `+WAVE` or `+WAVEFILE=<fn>` | disabled | Enable VCD/VPD/FSDB dumps. |
| `+TIMEOUT=<cycles>` | 200000 | Override watchdog timeout. |

### 4. Viewing waveforms

When `+WAVE` is supplied, the benches emit VCD by default.  Open the resulting file with GTKWave:

```bash
gtkwave smoke.vcd
```

### 5. Using commercial simulators

The `sim/vcs/` and `sim/verilator/` directories are placeholders.  Add tool-specific Makefiles or scripts there; ensure they include the same source lists shown above.

## Test programs

Two sets of programs ship with the repo:

- `tb/programs/*.hex` – compact self-checking hex files used by the scoreboard-driven testbench (`smoke`, `alu`).  Each has a matching `.exp` file describing the expected store sequence.
- `tests/programs/*.S` – human-readable RV32I assembly snippets with pre-generated `.hex` outputs.  These emphasise specific instruction categories (arithmetic, logical, branches, loads/stores, immediates) and follow the completion convention described in [`tests/README.md`](../tests/README.md).

### Regenerating hex images

Use the helper script to rebuild all assembly programs:

```bash
python3 tests/build_hex.py                  # rebuild every .S file
python3 tests/build_hex.py arithmetic       # rebuild just arithmetic.S
python3 tests/build_hex.py --keep-artifacts # keep intermediate ELF/BIN files
```

The script requires the RV32I GCC toolchain mentioned earlier.  Generated artefacts overwrite the existing `.hex` files in place.

### Writing a new test program

1. Create `tests/programs/<name>.S` using the termination convention (write `1` to `0x00001000`).
2. Run `python3 tests/build_hex.py <name>` to emit the `.hex` companion.
3. Optionally create `tb/programs/<name>.hex` and `.exp` if the test should run inside the scoreboard harness.
4. Add a pytest or SystemVerilog regression hook to exercise the program.

## Extending the design

### Adding a new instruction

1. Update `rv32i_decoder.sv` to recognise the opcode/funct combination and populate `decode_ctrl_t` accordingly.
2. Extend `rv32i_alu.sv` (or another functional unit) if the operation requires new datapath logic.
3. Capture immediates in `rv32i_imm_gen.sv` if a new encoding is used.
4. Update [`architecture.md`](architecture.md#instruction-set-support-matrix) to document the new instruction.
5. Add directed test programs or unit tests that cover the new behaviour.

### Introducing additional pipeline stages or forwarding

- Instantiate the optional `rv32i_hazard_unit` / `rv32i_forwarding_unit` and route register indices extracted from the pipeline payloads.
- Use the `hold_i` and `flush_i` controls on `rv32i_pipeline_reg` to insert new stage boundaries safely.
- Update [`timing_diagrams.md`](timing_diagrams.md) to reflect the revised pipeline timing.

### Adding new peripherals or bus fabrics

- Replace the Wishbone adapters with protocol-specific bridges.  Keep the core-facing handshake identical (`req`, `gnt`, `rvalid`) to avoid touching the pipeline logic.
- Extend `rv32i_wb_router` or introduce a new address decoder to expose additional memory-mapped devices.

### Debugging tips

- Use the `+WAVEFILE=<name>.vcd` plusarg to generate waveforms while reproducing failures.
- Enable random wait states in `rv32i_imem_model` / `rv32i_dmem_model` to shake out hidden pipeline bugs.
- The scoreboard prints a detailed mismatch log showing the expected vs observed store values before calling `$fatal`.

## Common issues and troubleshooting

| Symptom | Likely cause | Resolution |
| --- | --- | --- |
| `pytest` skips tests | `iverilog`/`vvp` not found in PATH | Install Icarus Verilog or adjust PATH. |
| `build_hex.py` aborts with "Unable to locate riscv64-unknown-elf-gcc" | Toolchain not installed | Install a RV32I GCC toolchain or set `RISCV_PREFIX`/`RISCV_GCC`. |
| Simulation hangs at timeout | Load transaction never returned | Check Wishbone wiring; ensure memories acknowledge transactions.  Consider enabling VCD and reviewing handshake signals. |
| Scoreboard reports unexpected store | RTL bug or wrong `.exp` expectation | Compare against reference run, update expectation file if intentional. |
| Illegal instruction fatal in ID stage | Program uses unsupported opcode | Extend the decoder/ALU and update documentation. |

## Additional resources

- [`architecture.md`](architecture.md) – conceptual overview, pipeline details, instruction coverage.
- [`module_interfaces.md`](module_interfaces.md) – port-level specifications for every RTL block.
- [`timing_diagrams.md`](timing_diagrams.md) – waveforms illustrating pipeline and bus timing.

For questions or contributions, follow the guidelines in the top-level [`README.md`](../README.md).
