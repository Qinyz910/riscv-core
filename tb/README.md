# RV32I Core Testbench

This directory contains a synthesizable-friendly SystemVerilog testbench focused on
running directed programs against the `rv32i_core` DUT.  The environment provides
simple instruction/data memory models, protocol assertions, a scoreboard that
tracks architectural results, and infrastructure to select tests and waveforms via
plusargs.  The testbench is intended to be consumed by the VCS flow under
`sim/vcs`, but it can also be used with other simulators.

## Key Components

- **`rv32i_tb_pkg.sv`** – shared typedefs, configuration helpers, and utility
  routines for the verification environment.
- **`rv32i_imem_model.sv`** – Wishbone-compatible instruction ROM with configurable
  latency and support for loading hex/ELF images.
- **`rv32i_dmem_model.sv`** – Wishbone data RAM that applies byte enables,
  captures load/store activity, and exposes transaction events for the scoreboard.
- **`rv32i_scoreboard.sv`** – checks store transactions against expectations read
  from disk and raises pass/fail events.
- **`rv32i_core_tb_top.sv`** – top-level harness that glues together the core,
  memories, scoreboard, waveform control, and simulation services (clock, reset,
  program loading, timeouts, etc.).

## Running Tests

The recommended entry point is the VCS makefile:

```bash
make -C sim/vcs run TEST=smoke        # build + run with the default program
make -C sim/vcs run TEST=smoke WAVE=1 # additionally dump waveforms
```

Additional configuration is controlled through plusargs:

- `+TEST=<name>` – selects which entry from `tb/programs/` to execute.  The
  harness will look for `<name>.hex` and `<name>.exp` files unless overridden by
  `+PROGRAM` or `+EXPECT`.
- `+PROGRAM=<path>` – explicit path to the program to load into instruction
  memory.
- `+EXPECT=<path>` – explicit path to the expectation file consumed by the
  scoreboard (defaults to the program image with an `.exp` extension when
  present).
- `+DMEM=<path>` – optional data memory initialization image loaded alongside
  the program.
- `+WAVEFILE=<path>` – name (and optionally extension) of the waveform dump file.
  `.vcd` and `.vpd` formats are supported out of the box.
- `+TIMEOUT=<cycles>` – overrides the default simulation timeout value.

The simulation exits automatically with a pass/fail message once the scoreboard
matches all expected results (typically triggered by a store to the "tohost"
address).

## Program Images & Expectations

Sample programs can be found in `tb/programs/`.  The repository currently ships
with:

- `smoke` – sanity program that adds two immediate values and reports the result
  via the tohost register pair.
- `alu` – slightly more involved arithmetic sequence exercising immediate and
  register ALU operations before signalling pass.

Each test includes a corresponding expectation file with one store transaction
per line using the format:

```
<address> <data>
```

Addresses and data are interpreted as 32-bit hexadecimal values.  Lines starting
with `#` are ignored.  The order is significant and must match the order of
stores produced by the DUT.

## Extending the Environment

1. Add additional programs under `tb/programs/<name>.hex`.
2. Provide matching expectations under `tb/programs/<name>.exp`.
3. Update any high-level documentation or regressions as needed.

The environment is intentionally lightweight, making it straightforward to port
into other tool flows or extend with coverage, assertions, and more detailed
models as the RTL matures.
