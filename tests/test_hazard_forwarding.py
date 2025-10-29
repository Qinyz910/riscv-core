import shutil
import subprocess
import tempfile
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]

SOURCES = [
    ROOT / "rtl" / "core" / "control" / "rv32i_control_pkg.sv",
    ROOT / "rtl" / "core" / "control" / "rv32i_hazard_unit.sv",
    ROOT / "rtl" / "core" / "control" / "rv32i_forwarding_unit.sv",
    ROOT / "tb" / "src" / "rv32i_hazard_forward_tb.sv",
]


def run_simulation():
    if shutil.which("iverilog") is None:
        pytest.skip("iverilog is required to run this test")
    if shutil.which("vvp") is None:
        pytest.skip("vvp is required to run this test")

    with tempfile.TemporaryDirectory() as build_dir:
        build_path = Path(build_dir)
        image_path = build_path / "hazard_forward_tb.vvp"

        compile_cmd = ["iverilog", "-g2012", "-o", str(image_path)]
        compile_cmd.extend(str(src) for src in SOURCES)
        subprocess.run(compile_cmd, check=True, cwd=ROOT)

        run_cmd = ["vvp", str(image_path)]
        subprocess.run(run_cmd, check=True, cwd=ROOT)


def test_hazard_forwarding_tb():
    run_simulation()
