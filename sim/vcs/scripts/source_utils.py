#!/usr/bin/env python3
"""Utilities for building source file lists for the VCS flow."""

from __future__ import annotations

import os
from pathlib import Path
from typing import Iterable, List, Sequence

# SystemVerilog / Verilog extensions that we care about when building file lists.
SV_EXTENSIONS: Sequence[str] = (".sv", ".svh", ".v", ".vh")


def _normalize_path(value: str) -> Path:
    """Expand environment variables and return a resolved Path instance."""
    return Path(os.path.expandvars(os.path.expanduser(value))).resolve()


def parse_path_list(raw: str | None) -> List[Path]:
    """Parse a colon or comma separated path list into Path objects.

    Empty strings and non-existent entries are ignored.
    """
    if not raw:
        return []

    separators = [":", ","]
    tokens = [raw]
    for sep in separators:
        tokens = sum([token.split(sep) for token in tokens], [])
    return [_normalize_path(token.strip()) for token in tokens if token.strip()]


def existing_directories(candidates: Iterable[Path]) -> List[Path]:
    """Return only directories that currently exist on disk."""
    return [path for path in candidates if path.is_dir()]


def gather_sv_sources(paths: Iterable[Path]) -> List[Path]:
    """Recursively gather SV/Verilog sources from the provided paths.

    Paths may point at directories or individual files. Non-existent paths are
    skipped silently to allow optional components in the RTL/TB tree.
    """
    collected: List[Path] = []
    seen = set()

    for entry in paths:
        if entry.is_dir():
            for ext in SV_EXTENSIONS:
                for candidate in entry.rglob(f"*{ext}"):
                    if candidate not in seen and candidate.is_file():
                        seen.add(candidate)
                        collected.append(candidate)
        elif entry.is_file() and entry.suffix.lower() in SV_EXTENSIONS:
            if entry not in seen:
                seen.add(entry)
                collected.append(entry)

    collected.sort()
    return collected


def write_filelist(sources: Sequence[Path], destination: Path) -> None:
    """Write the gathered sources to a VCS compatible file list."""
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open("w", encoding="utf-8") as handle:
        for source in sources:
            handle.write(f"{source}\n")


def resolve_program(test_name: str, search_roots: Iterable[Path]) -> Path | None:
    """Locate a program image for the provided test name.

    The function looks for common file extensions used for memory images. It
    returns the first match, or None if nothing was found.
    """
    candidate_extensions = (".hex", ".mem", ".elf", ".bin")

    for root in search_roots:
        if not root.exists():
            continue
        for extension in candidate_extensions:
            candidate = root / f"{test_name}{extension}"
            if candidate.is_file():
                return candidate
    return None
