# RISC-V Core User Guide

## Introduction

Welcome to the `riscv-core` project. This guide helps you navigate the repository, set up the toolchain, run simulations, and extend the verification collateral. The codebase targets hobbyists, researchers, and students who want to explore a clean five-stage in-order RISC-V implementation.

## Repository Layout

```
.
├── docs/                # Architecture design, user guide, and interface references
├── rtl/                 # Core RTL sources (SystemVerilog)
│   ├── core/            # Pipeline stages, register file, CSR unit
│   ├── bus/             # Wishbone adapters and arbitration logic
│   └── top/             # SoC integration examples
├── sim/                 # Simulation harnesses and scripts
│   ├── verilator/       # Verilator projects and makefiles
│   └── modelsim/        # Mentor/Questa simulation setup (optional)
├── tests/               # Assembly and C regression suites
│   ├── isa/             # ISA compliance tests
│   ├── directed/        # Hand-written edge cases
│   └── random/          # Constrained random test generators
└── tools/               # Utility scripts (linting, test generators, coverage)
```

> **Note:** Some directories may be introduced gradually. If a folder is missing, initialize it as described above when you add content.

## Prerequisites

- **Toolchain**: `riscv64-unknown-elf-gcc` (version 11 or later) for compiling tests.
- **Simulator**: Verilator 5.x is the reference flow. Any SystemVerilog simulator with DPI support (e.g., Questa, VCS) can also be used.
- **Python 3.10+**: Required for helper scripts in `tools/`.
- **CMake / Ninja (optional)**: Alternative build system support.

Install toolchain packages using your OS distribution or the official RISC-V GNU toolchain build scripts.

## Quick Start: Build & Run Simulation

1. **Clone the repository**
   ```bash
   git clone https://github.com/<org>/riscv-core.git
   cd riscv-core
   ```

2. **Set up the environment**
   - Export the RISC-V toolchain path:
     ```bash
     export RISCV=/opt/riscv
     export PATH="$RISCV/bin:$PATH"
     ```
   - Install Python dependencies (if any):
     ```bash
     pip install -r tools/requirements.txt
     ```

3. **Build the core with Verilator**
   ```bash
   make -C sim/verilator build
   ```

4. **Run the smoke test suite**
   ```bash
   make -C sim/verilator run-smoke
   ```
   This compiles the RTL, links against the Verilator harness, and executes the basic ISA sanity tests. Waveforms are written to `sim/verilator/out/` by default.

5. **(Optional) Run with Synopsys VCS**
   ```bash
   make -C sim/vcs run TEST=smoke WAVE=1
   ```
   The VCS flow performs the same source discovery and elaboration steps, writing outputs to `sim/vcs/out/<test>/`. Tweak the `TEST` parameter to change the program image and set `COVERAGE=1` to collect VCS coverage data.

## Detailed Simulation Flow

1. **RTL Elaboration**: The make target triggers Verilator to translate SystemVerilog sources under `rtl/` into a cycle-accurate C++ model.
2. **Test Program Compilation**: Test binaries in `tests/` are cross-compiled using the RISC-V GCC toolchain.
3. **Memory Image Generation**: The compiled ELF binaries are converted into hex or binary images consumed by the simulation harness.
4. **Execution**: The harness loads the memory image, resets the core, and runs until pass/fail signature criteria are met.
5. **Reporting**: Test status, coverage metrics (if enabled), and waveforms are archived in `sim/verilator/out/<test-name>/`.

## Extending the Test Suite

### Adding a New Directed Test

1. Create the test source in `tests/directed/<name>.S` (assembly) or `.c` (C).
2. Update `tests/Makefile` (or the Python test manifest) to compile the new test.
3. Provide an expected signature or reference output under `tests/signatures/`.
4. Run the directed regression:
   ```bash
   make -C sim/verilator run-directed TEST=<name>
   ```

### Integrating ISA Compliance Suites

- Place the official RISC-V ISA tests under `tests/isa/`.
- Use the helper script:
  ```bash
  python tools/run_isa.py --sim verilator --subset rv32i
  ```
- The script aggregates pass/fail statistics and stores results in `reports/isa/<date>/`.

### Randomized & Coverage-Driven Testing

- Utilize `tests/random/generate.py` to create stimulus sequences with configurable instruction mixes.
- Enable functional coverage by toggling the `ENABLE_COVERAGE` flag in `sim/verilator/config.mk`.
- Inspect coverage reports at `reports/coverage/` using the provided HTML viewers.

## Debugging Tips

- **Waveform Inspection**: Toggle `WAVE=1` when invoking make targets to dump VCD/FSDB files.
- **Assertions**: SystemVerilog assertions reside under `rtl/core/assertions/`; enable `ASSERT_ON` during builds.
- **Logging**: The DPI harness prints per-cycle traces when `TRACE=1` is set.

## Contribution Workflow

1. Fork the repository and create a feature branch.
2. Run `tools/lint.sh` before submitting a pull request.
3. Ensure all regressions under `sim/verilator` and any enabled premium simulator flows pass.
4. Update documentation in `docs/` if your change affects the architecture or interfaces.

## Support & Further Reading

- Architecture overview: [`docs/architecture.md`](architecture.md)
- Interface specifications: [`docs/module-interfaces.md`](module-interfaces.md)
- RISC-V specifications: [https://riscv.org/technical/specifications/](https://riscv.org/technical/specifications/)

For issues or feature requests, open a GitHub issue or reach out to the maintainers via the discussion board.
