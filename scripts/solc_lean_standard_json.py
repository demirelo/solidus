#!/usr/bin/env python3
"""solc-compatible Standard JSON wrapper backed by the Lean bytecode path.

This wrapper is intentionally narrow: it behaves like solc for `--standard-json`
calls by reading Standard JSON from stdin and returning solc-shaped JSON with
Lean-produced bytecode.  Non-Standard-JSON invocations are delegated to the real
solc so tools can still probe `--version`, `--help`, and similar metadata.
"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from pathlib import Path


def default_real_solc() -> str:
    local_solc = Path.home() / ".local" / "bin" / "solc"
    if local_solc.exists():
        return str(local_solc)
    return "solc"


def default_lake() -> str:
    local_lake = Path.home() / ".elan" / "bin" / "lake"
    if local_lake.exists():
        return str(local_lake)
    return "lake"


def env_flag(name: str) -> bool:
    value = os.environ.get(name)
    if value is None:
        return False
    return value.strip().lower() not in {"", "0", "false", "no", "off"}


def env_flag_default(name: str, default: bool) -> bool:
    value = os.environ.get(name)
    if value is None:
        return default
    return value.strip().lower() not in {"", "0", "false", "no", "off"}


def validate_standard_json_output(output: str) -> int:
    import validate_bridge_json

    with tempfile.NamedTemporaryFile(
        "w",
        encoding="utf-8",
        suffix=".json",
        delete=False,
    ) as handle:
        handle.write(output)
        path = Path(handle.name)
    try:
        return validate_bridge_json.main(["--quiet", str(path)])
    finally:
        try:
            path.unlink()
        except FileNotFoundError:
            pass


def main(argv: list[str]) -> int:
    script_dir = Path(__file__).resolve().parent
    root = script_dir.parent
    real_solc = os.environ.get("SOLC_LEAN_REAL_SOLC", default_real_solc())
    if "--standard-json" not in argv:
        try:
            return subprocess.run([real_solc, *argv]).returncode
        except FileNotFoundError:
            print(
                f"error: could not find real solc executable {real_solc!r}; "
                "set SOLC_LEAN_REAL_SOLC",
                file=sys.stderr,
            )
            return 1

    bridge = Path(
        os.environ.get(
            "SOLC_LEAN_BRIDGE",
            root / "scripts" / "solidity_to_yul_lean.py",
        )
    )
    lake = os.environ.get("SOLC_LEAN_LAKE", os.environ.get("LAKE", default_lake()))
    lake_cwd = Path(os.environ.get("SOLC_LEAN_LAKE_CWD", root))
    namespace = os.environ.get("SOLC_LEAN_NAMESPACE", "Generated.SolcLeanWrapper")
    bridge_json_dir = os.environ.get("SOLC_LEAN_BRIDGE_JSON_DIR")
    extra_solc_args = [arg for arg in argv if arg != "--standard-json"]
    command = [
        sys.executable,
        str(bridge),
        "-",
        "--input-format",
        "standard-json",
        "--format",
        "standard-json-output",
        "--all-contracts",
        "--solc",
        real_solc,
        "--lake",
        lake,
        "--lake-cwd",
        str(lake_cwd),
        "--namespace",
        namespace,
    ]
    if env_flag("SOLC_LEAN_OPTIMIZED"):
        command.append("--optimized")
    if bridge_json_dir:
        command.extend(["--bridge-json-dir", str(Path(bridge_json_dir).resolve())])
    for arg in extra_solc_args:
        command.append(f"--solc-arg={arg}")
    try:
        completed = subprocess.run(
            command,
            input=sys.stdin.read(),
            text=True,
            capture_output=True,
        )
    except FileNotFoundError as exc:
        print(f"error: could not run {exc.filename!r}", file=sys.stderr)
        return 1
    stdout = completed.stdout or ""
    stderr = completed.stderr or ""
    if completed.returncode != 0:
        if stdout:
            sys.stdout.write(stdout)
        if stderr:
            sys.stderr.write(stderr)
        return completed.returncode
    if env_flag_default("SOLC_LEAN_VALIDATE_OUTPUT", True):
        validation_result = validate_standard_json_output(stdout)
        if validation_result != 0:
            if stderr:
                sys.stderr.write(stderr)
            print(
                "error: solc-lean produced invalid Standard JSON output",
                file=sys.stderr,
            )
            return validation_result
    if stderr:
        sys.stderr.write(stderr)
    if stdout:
        sys.stdout.write(stdout)
    return completed.returncode


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
