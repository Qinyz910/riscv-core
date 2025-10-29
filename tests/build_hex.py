#!/usr/bin/env python3
"""Assemble the RV32I sample programs and regenerate their .hex images."""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
PROGRAM_DIR = SCRIPT_DIR / "programs"

DEFAULT_PREFIX = "riscv64-unknown-elf"


def _resolve_tool(explicit_env: str, suffix: str) -> str:
    candidate = os.environ.get(explicit_env)
    if candidate:
        if shutil.which(candidate):
            return candidate
        candidate_path = Path(candidate)
        if candidate_path.is_file() and os.access(candidate_path, os.X_OK):
            return str(candidate_path)
        sys.exit(f"{explicit_env} is set but the tool '{candidate}' was not found or is not executable")

    prefix = os.environ.get("RISCV_PREFIX", DEFAULT_PREFIX)
    tool_name = f"{prefix}-{suffix}"
    resolved = shutil.which(tool_name)
    if not resolved:
        sys.exit(
            f"Unable to locate '{tool_name}'. Set RISCV_PREFIX or the {explicit_env} environment variable "
            "to point at a valid RISC-V GCC toolchain."
        )
    return tool_name


GCC = _resolve_tool("RISCV_GCC", "gcc")
OBJCOPY = _resolve_tool("RISCV_OBJCOPY", "objcopy")

COMMON_CFLAGS = [
    "-march=rv32i",
    "-mabi=ilp32",
    "-nostdlib",
    "-nostartfiles",
    "-Ttext=0x0",
    "-Wl,--no-relax",
]


def _run(cmd: list[str]) -> None:
    try:
        subprocess.run(cmd, check=True)
    except subprocess.CalledProcessError as exc:
        sys.exit(
            "Command failed ({}):\n{}".format(
                exc.returncode,
                " ".join(cmd),
            )
        )


def _bin_to_hex(bin_path: Path, hex_path: Path) -> int:
    data = bin_path.read_bytes()
    if not data:
        hex_path.write_text("")
        return 0

    if len(data) % 4:
        data += b"\x00" * (4 - (len(data) % 4))

    words = [int.from_bytes(data[i : i + 4], "little") for i in range(0, len(data), 4)]
    with hex_path.open("w", encoding="ascii") as fp:
        for word in words:
            fp.write(f"{word:08x}\n")
    return len(words)


def build_program(src: Path, keep_artifacts: bool) -> None:
    stem = src.stem
    if not PROGRAM_DIR.exists():
        sys.exit(f"Program directory '{PROGRAM_DIR}' does not exist")

    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir_path = Path(tmpdir)
        elf_path = tmpdir_path / f"{stem}.elf"
        bin_path = tmpdir_path / f"{stem}.bin"

        compile_cmd = [GCC, *COMMON_CFLAGS, "-o", str(elf_path), str(src)]
        _run(compile_cmd)

        objcopy_cmd = [OBJCOPY, "-O", "binary", str(elf_path), str(bin_path)]
        _run(objcopy_cmd)

        hex_path = PROGRAM_DIR / f"{stem}.hex"
        word_count = _bin_to_hex(bin_path, hex_path)

        if keep_artifacts:
            dest_elf = PROGRAM_DIR / f"{stem}.elf"
            dest_bin = PROGRAM_DIR / f"{stem}.bin"
            shutil.copy2(elf_path, dest_elf)
            shutil.copy2(bin_path, dest_bin)

    print(f"[+] {src.name} -> {hex_path.name} ({word_count} words)")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "programs",
        nargs="*",
        help="Optional list of program basenames (without extension) to rebuild.",
    )
    parser.add_argument(
        "--keep-artifacts",
        action="store_true",
        help="Copy the intermediate ELF and BIN files next to the .hex output for inspection.",
    )
    args = parser.parse_args()

    if not PROGRAM_DIR.exists():
        sys.exit(f"Program directory '{PROGRAM_DIR}' was not found")

    sources = sorted(PROGRAM_DIR.glob("*.S"))
    if args.programs:
        requested = set(args.programs)
        sources = [src for src in sources if src.stem in requested]
        missing = requested - {src.stem for src in sources}
        if missing:
            sys.exit(f"Unknown program(s): {', '.join(sorted(missing))}")

    if not sources:
        sys.exit("No assembly sources found under tests/programs")

    for src in sources:
        build_program(src, keep_artifacts=args.keep_artifacts)


if __name__ == "__main__":
    main()
