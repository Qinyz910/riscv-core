#!/usr/bin/env python3
"""Entry point for building and running Synopsys VCS simulations."""

from __future__ import annotations

import argparse
import os
import shlex
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import List

from source_utils import (
    existing_directories,
    gather_sv_sources,
    parse_path_list,
    resolve_program,
    write_filelist,
)


@dataclass
class FlowConfig:
    project_root: Path
    sim_root: Path
    action: str
    test: str
    wave: bool
    coverage: bool
    lint: bool
    program: Path | None
    plusargs: List[str]
    extra_vcs_flags: List[str]


class FlowError(Exception):
    """Custom exception raised when the flow encounters a blocking error."""


def parse_args() -> FlowConfig:
    parser = argparse.ArgumentParser(description="Drive the Synopsys VCS flow")
    parser.add_argument("--project-root", required=True, help="Absolute path to the repository root")
    parser.add_argument("--sim-root", required=True, help="Absolute path to sim/vcs")
    parser.add_argument("--action", choices=["compile", "run"], default="run")
    parser.add_argument("--test", required=True, help="Name of the test to build / run")
    parser.add_argument("--wave", action="store_true", help="Enable waveform dumping flags")
    parser.add_argument("--coverage", action="store_true", help="Enable coverage collection flags")
    parser.add_argument("--lint", action="store_true", help="Enable aggressive linting flags during compile")
    parser.add_argument("--program", help="Explicit path to a program image for the selected test")
    parser.add_argument(
        "--plusarg",
        action="append",
        dest="plusargs",
        default=None,
        help="Additional plusargs to pass to the simulation executable",
    )
    parser.add_argument(
        "--vcs-flag",
        action="append",
        dest="extra_flags",
        default=None,
        help="Extra flags forwarded directly to the VCS compile invocation",
    )

    arguments = parser.parse_args()

    project_root = Path(arguments.project_root).resolve()
    sim_root = Path(arguments.sim_root).resolve()

    if arguments.program:
        program = Path(arguments.program).expanduser().resolve()
    else:
        program = None

    plusargs = arguments.plusargs or []
    extra_flags = arguments.extra_flags or []

    return FlowConfig(
        project_root=project_root,
        sim_root=sim_root,
        action=arguments.action,
        test=arguments.test,
        wave=arguments.wave,
        coverage=arguments.coverage,
        lint=arguments.lint,
        program=program,
        plusargs=plusargs,
        extra_vcs_flags=extra_flags,
    )


def find_vcs_binary() -> Path | None:
    """Resolve the VCS executable path using common environment variables."""
    env_candidates = [
        os.environ.get("VCS"),
    ]

    vcs_home = os.environ.get("VCS_HOME") or os.environ.get("SYNOPSYS")
    if vcs_home:
        env_candidates.append(str(Path(vcs_home) / "bin" / "vcs"))

    for candidate in env_candidates:
        if not candidate:
            continue
        candidate_path = Path(candidate).expanduser()
        if candidate_path.is_file() and os.access(candidate_path, os.X_OK):
            return candidate_path.resolve()

    which_result = shutil.which("vcs")
    if which_result:
        return Path(which_result).resolve()
    return None


def build_environment_summary(config: FlowConfig, vcs_path: Path) -> str:
    summary = [
        "VCS Flow Configuration:",
        f"  VCS binary        : {vcs_path}",
        f"  Project root      : {config.project_root}",
        f"  Simulation root   : {config.sim_root}",
        f"  Action            : {config.action}",
        f"  Test              : {config.test}",
        f"  Waveforms         : {'on' if config.wave else 'off'}",
        f"  Coverage          : {'on' if config.coverage else 'off'}",
        f"  Lint              : {'on' if config.lint else 'off'}",
    ]
    if config.program:
        summary.append(f"  Program image     : {config.program}")
    if config.plusargs:
        summary.append(f"  Extra plusargs    : {config.plusargs}")
    if config.extra_vcs_flags:
        summary.append(f"  Extra VCS flags   : {config.extra_vcs_flags}")
    return "\n".join(summary)


def resolve_source_directories(config: FlowConfig) -> tuple[list[Path], list[Path]]:
    """Determine RTL and TB directories using environment overrides as needed."""
    default_rtl = [config.project_root / "rtl"]
    default_tb = [config.sim_root / "tb"]

    rtl_dirs = parse_path_list(os.environ.get("VCS_RTL_DIRS")) or default_rtl
    tb_dirs = parse_path_list(os.environ.get("VCS_TB_DIRS")) or default_tb

    return existing_directories(rtl_dirs), existing_directories(tb_dirs)


def gather_sources(config: FlowConfig) -> tuple[list[Path], list[Path]]:
    rtl_dirs, tb_dirs = resolve_source_directories(config)

    rtl_sources = gather_sv_sources(rtl_dirs)
    tb_sources = gather_sv_sources(tb_dirs)

    if not rtl_sources and not tb_sources:
        raise FlowError(
            "Did not find any RTL or testbench sources. Ensure the default directories "
            "exist or provide overrides via VCS_RTL_DIRS / VCS_TB_DIRS."
        )

    extra_filelists = [path for path in parse_path_list(os.environ.get("VCS_EXTRA_FILELISTS")) if path.is_file()]

    resolved_sources: list[Path] = []
    resolved_sources.extend(rtl_sources)
    resolved_sources.extend(tb_sources)

    return resolved_sources, extra_filelists


def resolve_program_image(config: FlowConfig) -> Path | None:
    if config.program:
        if not config.program.exists():
            raise FlowError(f"Provided program image does not exist: {config.program}")
        return config.program

    search_roots = parse_path_list(os.environ.get("VCS_TEST_DIRS"))
    if not search_roots:
        search_roots = [
            config.project_root / "tests" / "directed",
            config.project_root / "tests" / "isa",
            config.project_root / "tests" / "programs",
        ]

    return resolve_program(config.test, search_roots)


def combine_plusargs(config: FlowConfig) -> list[str]:
    env_plusargs = os.environ.get("VCS_PLUSARGS")
    parsed_env = shlex.split(env_plusargs) if env_plusargs else []
    return parsed_env + config.plusargs


def combine_vcs_flags(config: FlowConfig) -> list[str]:
    env_flags = os.environ.get("VCS_EXTRA_FLAGS")
    parsed_env = shlex.split(env_flags) if env_flags else []
    return parsed_env + config.extra_vcs_flags


def run_command(command: list[str], log_path: Path, workdir: Path) -> None:
    log_path.parent.mkdir(parents=True, exist_ok=True)
    with log_path.open("w", encoding="utf-8") as logfile:
        process = subprocess.run(command, cwd=workdir, stdout=logfile, stderr=subprocess.STDOUT)
    if process.returncode != 0:
        raise FlowError(f"Command failed with exit code {process.returncode}: {command[0]} (see {log_path})")


def invoke_compile(
    config: FlowConfig,
    vcs_path: Path,
    sources: list[Path],
    extra_filelists: list[Path],
    filelist_path: Path,
    build_dir: Path,
    coverage_dir: Path,
    compile_log: Path,
) -> None:
    write_filelist(sources, filelist_path)

    include_dirs = parse_path_list(os.environ.get("VCS_INC_DIRS"))
    defines = shlex.split(os.environ.get("VCS_DEFINES", ""))

    command: list[str] = [str(vcs_path), "-full64", "-sverilog", "+vcs+lic+wait", "-timescale=1ns/1ps"]

    if config.lint:
        command.extend(["-lint=all", "-notice"])

    if config.wave or config.coverage:
        command.append("-debug_access+all")

    for include_dir in include_dirs:
        command.append(f"+incdir+{include_dir}")

    for define in defines:
        command.append(f"+define+{define}")

    command.extend(["-Mdir", str(build_dir / "csrc")])
    command.extend(["-o", str(build_dir / "simv")])

    if config.coverage:
        coverage_args = os.environ.get("VCS_COVERAGE_FLAGS", "-cm line+tgl+branch")
        command.extend(shlex.split(coverage_args))
        command.extend(["-cm_dir", str(coverage_dir)])

    command.extend(combine_vcs_flags(config))
    command.extend(["-f", str(filelist_path)])
    for filelist in extra_filelists:
        command.extend(["-f", str(filelist)])

    run_command(command, compile_log, workdir=build_dir)


def invoke_simulation(
    config: FlowConfig,
    program_image: Path | None,
    build_dir: Path,
    run_dir: Path,
    wave_dir: Path,
    coverage_dir: Path,
    run_log: Path,
) -> None:
    simv = build_dir / "simv"
    if not simv.exists():
        raise FlowError(f"Simulation executable not found: {simv}. Run the compile stage first.")

    command: list[str] = [str(simv), "+vcs+lic+wait", f"+TEST={config.test}"]

    if program_image:
        command.append(f"+PROGRAM={program_image}")

    if config.wave:
        wave_dir.mkdir(parents=True, exist_ok=True)
        wave_file = wave_dir / f"{config.test}.vpd"
        command.append(f"+WAVEFILE={wave_file}")

    if config.coverage:
        command.extend(["-cm_dir", str(coverage_dir)])
        command.extend(["-cm_name", config.test])

    command.extend(combine_plusargs(config))

    run_command(command, run_log, workdir=run_dir)


def run_flow(config: FlowConfig) -> None:
    vcs_path = find_vcs_binary()
    if not vcs_path:
        raise FlowError(
            "Synopsys VCS executable not found. Set the VCS or VCS_HOME environment variable "
            "or ensure 'vcs' is present on PATH."
        )

    print(build_environment_summary(config, vcs_path))

    out_root = config.sim_root / "out"
    test_root = out_root / config.test
    build_dir = test_root / "build"
    run_dir = test_root / "run"
    wave_dir = test_root / "waves"
    coverage_dir = test_root / "coverage"
    filelist_path = build_dir / "filelist.f"
    compile_log = test_root / "logs" / "compile.log"
    run_log = test_root / "logs" / "simulate.log"

    build_dir.mkdir(parents=True, exist_ok=True)
    run_dir.mkdir(parents=True, exist_ok=True)

    sources, extra_filelists = gather_sources(config)

    program_image = resolve_program_image(config)
    if not program_image:
        print(
            "Warning: No program image resolved for test '{}' (override with --program or VCS_TEST_DIRS).".format(
                config.test
            )
        )

    invoke_compile(
        config=config,
        vcs_path=vcs_path,
        sources=sources,
        extra_filelists=extra_filelists,
        filelist_path=filelist_path,
        build_dir=build_dir,
        coverage_dir=coverage_dir,
        compile_log=compile_log,
    )

    if config.action == "compile":
        print(f"Compilation finished. Artifacts are under {test_root}.")
        return

    invoke_simulation(
        config=config,
        program_image=program_image,
        build_dir=build_dir,
        run_dir=run_dir,
        wave_dir=wave_dir,
        coverage_dir=coverage_dir,
        run_log=run_log,
    )
    print(f"Simulation finished. Logs are available at {run_log}.")


def main() -> int:
    try:
        config = parse_args()
        run_flow(config)
        return 0
    except FlowError as error:
        print(f"[ERROR] {error}", file=sys.stderr)
        return 2
    except KeyboardInterrupt:
        print("Flow interrupted by user", file=sys.stderr)
        return 130


if __name__ == "__main__":
    sys.exit(main())
