# RV32I Sample Programs

The `tests/programs` directory hosts a set of hand-written RV32I assembly snippets that exercise the core through common instruction categories. Each program is provided as both a human-readable `.S` source file and a word-oriented `.hex` file suitable for loading into simulation memories.

## Termination Convention

All programs share the same completion protocol so the testbench can detect forward progress:

- A per-program status region is anchored at **`0x0000_1000`**.
- Writing the value `1` to address `0x0000_1000` indicates the test has finished.
- Many programs also deposit intermediate results at successive word offsets (for example, `0x0000_1004`, `0x0000_1008`, ...). See the inline comments in each assembly file for the exact layout.

This convention keeps the core running in-place (each program spins on a self-branch after storing the flag) so external logic can poll memory without needing a trap handler.

## Program Catalog

| File | Category | Key Instructions | Notes |
| --- | --- | --- | --- |
| `arithmetic.S` | Arithmetic | `add`, `sub` | Sums small constants, stores the doubled result, and signals completion. |
| `logical.S` | Logical | `and`, `or`, `xor` | Demonstrates bitwise operations on masked immediates. |
| `immediates.S` | Immediate | `addi`, `slti`, `slli`, `srli`, `xori`, `ori`, `andi` | Captures the results of several immediate-form ALU ops. |
| `branches_jumps.S` | Branch / Jump | `beq`, `jal`, `jalr` | Counts up via a loop, exercises link register handling, then halts via an indirect jump. |
| `load_store.S` | Load / Store | `lw`, `sw`, `sb`, `lb`, `sh`, `lh` | Moves data through different-sized memory accesses before flagging completion. |

Each `.hex` companion file contains one 32-bit instruction per line, little-endian packed to match the default simulation memory format.

## Regenerating Hex Images

Use any standard RV32I bare-metal toolchain (for example, the GNU tools distributed with `riscv64-unknown-elf-gcc`). The helper script will take care of assembling, linking at address zero, and converting the raw binary to word-addressable hex.

```bash
# From the repository root
python3 tests/build_hex.py
```

The script honors the following environment variables:

- `RISCV_PREFIX` (default: `riscv64-unknown-elf`)
- `RISCV_GCC` / `RISCV_OBJCOPY` (optional overrides)

Generated `.hex` files are written in-place next to their sources. Intermediate ELF/BIN artifacts are kept in a temporary directory and discarded automatically, so the working tree remains clean.

If you prefer to drive the tools manually, the sequence mirrors what the helper executes:

```bash
PREFIX=${RISCV_PREFIX:-riscv64-unknown-elf}
$PREFIX-gcc -march=rv32i -mabi=ilp32 -nostdlib -nostartfiles \
    -Ttext=0x0 -Wl,--no-relax -o /tmp/program.elf tests/programs/arithmetic.S
$PREFIX-objcopy -O binary /tmp/program.elf /tmp/program.bin
python3 - <<'PY'
from pathlib import Path
bin_path = Path('/tmp/program.bin')
data = bin_path.read_bytes()
if len(data) % 4:
    data += b'\x00' * (4 - (len(data) % 4))
with Path('tests/programs/arithmetic.hex').open('w', encoding='ascii') as fp:
    for i in range(0, len(data), 4):
        fp.write(f"{int.from_bytes(data[i:i+4], 'little'):08x}\n")
PY
```

Passing `--keep-artifacts` to `build_hex.py` performs the same regeneration while copying the intermediate ELF/BIN outputs next to the `.hex` file for inspection.
