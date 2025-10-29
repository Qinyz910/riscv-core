# Synopsys VCS Simulation Flow

This directory hosts the make targets and helper scripts required to run the
`riscv-core` verification environment on Synopsys VCS.

## Quick Start

```bash
cd sim/vcs
make run TEST=smoke
```

The command above will:

1. Discover RTL and testbench sources based on the defaults described below.
2. Elaborate the design with VCS, writing build products into `out/<test>/build/`.
3. Launch the simulation binary, archiving logs in `out/<test>/logs/` and waves in
   `out/<test>/waves/` when enabled.

### Common Targets

| Target      | Description                                                                 |
|-------------|-----------------------------------------------------------------------------|
| `run`       | Compile the RTL and run the selected test (`TEST=<name>`).                  |
| `compile`   | Stop after compilation/elaboration.                                         |
| `lint`      | Compile with `-lint=all` and other lint-focused flags.                      |
| `clean`     | Remove the `out/` directory for the VCS flow.                               |

Additional knobs can be enabled by passing variables to `make`:

- `WAVE=1` – enable waveform dumping hooks.
- `COVERAGE=1` – enable coverage options (line/toggle/branch by default).
- `LINT=1` – include lint flags in the compile step (also set automatically by `make lint`).
- `PROGRAM=/path/to/image` – explicitly provide the program image consumed by the testbench.

## Environment Variables

The flow can be customized using the following environment variables:

| Variable             | Purpose                                                                                         |
|----------------------|-------------------------------------------------------------------------------------------------|
| `VCS`                | Absolute path to the VCS executable.                                                            |
| `VCS_HOME` / `SYNOPSYS` | Location of the VCS installation; the flow looks for `bin/vcs` inside this directory.          |
| `VCS_RTL_DIRS`       | Colon/comma separated list of directories containing RTL sources. Defaults to `<repo>/rtl`.    |
| `VCS_TB_DIRS`        | Colon/comma separated list of testbench directories. Defaults to `sim/vcs/tb`.                 |
| `VCS_EXTRA_FILELISTS`| Additional file lists (`.f` files) to append to the compilation.                                |
| `VCS_INC_DIRS`       | Include directories forwarded as `+incdir+`.                                                    |
| `VCS_DEFINES`        | Space separated list of `+define+` macro definitions.                                           |
| `VCS_PLUSARGS`       | Extra plusargs passed to the simulation executable.                                             |
| `VCS_EXTRA_FLAGS`    | Additional flags appended to the VCS compile command.                                           |
| `VCS_COVERAGE_FLAGS` | Override the default coverage flags (`-cm line+tgl+branch`).                                    |
| `VCS_TEST_DIRS`      | Colon/comma separated directories for locating test program images.                             |

If neither `VCS` nor `VCS_HOME` is set, the scripts attempt to locate the tool via
`PATH`. If the executable cannot be found, the flow aborts with a descriptive
error message.

## Output Layout

Compilation and simulation artifacts are organized as follows:

```
sim/vcs/out/<test>/
  ├── build/      # Compiled objects, generated libraries, and the `simv` binary
  ├── run/        # Working directory for the simulation step
  ├── waves/      # Waveform dumps (`.vpd`, `.vcd`, `.fsdb`, depending on the TB)
  ├── coverage/   # Coverage databases when coverage is enabled
  └── logs/
      ├── compile.log   # Output from the VCS compile/elaboration stage
      └── simulate.log  # Output from the simulation execution
```

## Test Program Selection

`make run TEST=<name>` attempts to locate a program image named `<name>` under
`tests/directed/`, `tests/isa/`, or `tests/programs/`. The search order can be
customized by setting `VCS_TEST_DIRS`, or you can pass an explicit file path with
`PROGRAM=/path/to/image`.

If no program image is located, the flow continues after printing a warning so
that you can still perform bring-up of the infrastructure without a memory image
in place.

## Error Handling

The helper scripts are defensive and terminate early when tooling is missing or
when no RTL/testbench sources are discovered. Consult the log files mentioned
above for solver-specific error details.
