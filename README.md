# RISC-V Core

`riscv-core` is an educational yet production-minded implementation of a five-stage, single-issue RV32I processor. The design emphasizes clarity, modularity, and extensibility so contributors can explore architectural concepts, add optional extensions (M, C, CSR), and integrate the core into SoC environments with minimal friction.

## Project Overview

- **Pipeline**: Classic IF/ID/EX/MEM/WB pipeline with robust hazard and forwarding logic.
- **Instruction Set**: Full RV32I support with optional RV32M (multiply/divide) and RV32C (compressed) extensions.
- **Interfaces**: Clean ready/valid instruction interface and AXI-lite style data interface for easy system integration.
- **Verification**: Verilator-based simulation harness, ISA compliance suites, and directed/randomized tests.

For an in-depth architectural description, refer to [`docs/architecture.md`](docs/architecture.md).

## Quick Start

1. **Clone the repository**
   ```bash
   git clone https://github.com/<org>/riscv-core.git
   cd riscv-core
   ```
2. **Install prerequisites**
   - RISC-V GCC toolchain (`riscv64-unknown-elf-gcc`)
   - Verilator 5.x
   - Python 3.10+
3. **Set environment variables**
   ```bash
   export RISCV=/opt/riscv
   export PATH="$RISCV/bin:$PATH"
   ```
4. **Build the Verilator model**
   ```bash
   make -C sim/verilator build
   ```
5. **Run smoke tests**
   ```bash
   make -C sim/verilator run-smoke
   ```
6. **(Optional) Exercise the VCS flow**
   ```bash
   make -C sim/vcs run TEST=smoke WAVE=1
   ```

## Verification & Testing

- **ISA Compliance**: Execute the official RISC-V ISA suite using `python tools/run_isa.py --sim verilator --subset rv32i`.
- **Directed Tests**: Add assembly/C tests under `tests/directed/` and trigger them with `make -C sim/verilator run-directed TEST=<name>`.
- **Randomized Testing**: Use `tests/random/generate.py` for constrained random stimulus and review coverage reports in `reports/coverage/`.
- **Waveforms & Debug**: Enable wave dumps with `WAVE=1` and inspect traces using GTKWave or your preferred viewer.

## Documentation

- Architecture design document: [`docs/architecture.md`](docs/architecture.md)
- User guide & workflow: [`docs/user-guide.md`](docs/user-guide.md)
- Module interface specifications: [`docs/module-interfaces.md`](docs/module-interfaces.md)

## Contributing

Contributions are welcome! Before opening a pull request, run the linting and simulation flows, and update documentation when your change affects behavior, interfaces, or workflows. Check the [User Guide](docs/user-guide.md) for the repository layout and contribution checklist.
