# RV32I Five-Stage Core

A modular, single-issue RV32I processor implemented as an educational yet production-ready five-stage pipeline.  The repository includes self-checking SystemVerilog testbenches, Wishbone-compatible bus wrappers, and detailed documentation for architects and verification engineers.

> 📚 Documentation quick links: [Architecture](docs/architecture.md) · [Module Interfaces](docs/module_interfaces.md) · [Timing Diagrams](docs/timing_diagrams.md) · [User Guide](docs/user_guide.md)

## Key features

- RV32I base ISA (arithmetic, logical, load/store, branch, jump, and fence) with decode-time illegal instruction checks.
- Classic IF/ID/EX/MEM/WB pipeline with explicit pipeline payload structs and transparent stall/flush logic.
- Wishbone-compatible instruction and data interfaces, plus behavioural memory models for simulation.
- Configurable register file (depth/width) with same-cycle bypassing for read-after-write hazards.
- Scoreboard-driven top-level testbench and unit-level regressions runnable on open-source tools (Icarus Verilog, pytest).
- Comprehensive documentation covering micro-architecture, interfaces, timing, and developer workflows.

## Quick start

```bash
# Clone and set up Python environment
git clone <repo-url>
cd <repo-name>
python3 -m venv .venv && source .venv/bin/activate
pip install -r tests/requirements.txt  # if provided

# Run unit-level HDL tests (requires iverilog and vvp)
python -m pytest tests/test_decoder_tb.py
python -m pytest tests/test_hazard_forwarding.py

# Build and run the top-level core testbench
export PROJECT_ROOT="$(pwd)"
iverilog -g2012 -o build/rv32i_tb.vvp \
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
vvp build/rv32i_tb.vvp +TEST=smoke +PROJECT_ROOT=$PROJECT_ROOT
```

For richer workflows (waveform dumping, alternative simulators, regenerating programs) see the [User Guide](docs/user_guide.md).

## Repository layout

| Path | Description |
| --- | --- |
| `rtl/core/` | Pipeline stages, decoder, ALU, immediates, register file, and top-level core. |
| `rtl/bus/` | Wishbone master adapters, arbiter, and address router. |
| `tb/` | SystemVerilog testbenches, memory models, and scoreboard infrastructure. |
| `tests/` | Python-based regression hooks and RV32I assembly sources. |
| `docs/` | Architecture, interface, timing, and user-facing documentation. |
| `sim/` | Placeholders for tool-specific build recipes (Verilator, VCS, etc.). |

## Working with the project

- **Documentation:** Start with the [architecture overview](docs/architecture.md) for a conceptual tour, then consult [module interfaces](docs/module_interfaces.md) and [timing diagrams](docs/timing_diagrams.md) for implementation detail.
- **Testing:** Extend the pytest regressions or the SystemVerilog scoreboard when adding features.  Follow the completion convention described in [`tests/README.md`](tests/README.md) for new RV32I programs.
- **Tooling:** The design targets open-source flows by default but remains simulator-agnostic.  Add Makefiles or scripts under `sim/` for commercial tools.
- **Contributing:** Use feature branches, keep RTL and documentation changes in sync, and include tests that cover new behaviour.  See [`docs/user_guide.md`](docs/user_guide.md#extending-the-design) for recommended procedures when adding instructions or peripherals.

## License

All RTL and supporting files carry the `Apache-2.0` SPDX identifier.  Add a `LICENSE` file at the repository root before the first external release if one is not already present.

## Contact & contributions

Issues and patches are welcome.  Please provide:

1. A clear description of the problem or enhancement.
2. Reproduction steps or test cases.
3. Any necessary updates to documentation or regressions.

Happy hacking!
