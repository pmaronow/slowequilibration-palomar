#!/usr/bin/env python3
"""Shared helpers for local checks against the pinned official verifier."""
from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import importlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

PALOMAR_REPOSITORY = "https://github.com/PalomarRegistry/PalomarSubmission.git"
PALOMAR_REVISION = "d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44"
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc2"
LEAN_REVISION = "11acb17ec6b07a8f9e9173e6845197929540936b"
MATHLIB_REVISION = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_THEOREMS = ["SlowEquilibrationCondensedSource." + name for name in (
    "theorem_1_2", "corollary_1_3_a", "corollary_1_3_b",
    "corollary_1_3_b_degree_window", "corollary_1_3_b_support", "corollary_1_3_c",
    "corollary_1_3_d", "theorem_1_4_haar", "theorem_1_4", "theorem_1_5", "theorem_1_6"
)] + ["SlowEquilibrationCuspSource.theorem_1_7"]
ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def git_head(path: Path) -> str:
    return subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"],
                                   text=True).strip()


def official_verifier(path: Path):
    path = path.resolve(strict=True)
    require(git_head(path) == PALOMAR_REVISION, "Wrong PalomarSubmission revision")
    require(not subprocess.check_output(
        ["git", "-C", str(path), "status", "--porcelain"], text=True).strip(),
        "The pinned PalomarSubmission checkout must be clean")
    sys.path.insert(0, str(path))
    return importlib.import_module("scripts.verify_submission")


def proof_snapshot(project: Path) -> dict[str, str]:
    result = {}
    controls = {"comparator.json", "lean-toolchain", "lake-manifest.json", "lakefile.toml",
                "lakefile.lean"}
    for directory, subdirectories, filenames in os.walk(project, followlinks=False):
        subdirectories[:] = sorted(n for n in subdirectories
                                   if n not in {".git", ".lake", "__pycache__"})
        for name in sorted(filenames):
            path = Path(directory) / name
            if path.suffix == ".lean" or path.parent == project and name in controls:
                require(not path.is_symlink(), f"Proof input must be a regular file: {path}")
                result[path.relative_to(project).as_posix()] = sha256(path)
    return dict(sorted(result.items()))


def host_limits() -> dict:
    paths = {"memory_max": "/sys/fs/cgroup/memory.max",
             "memory_current": "/sys/fs/cgroup/memory.current",
             "memory_stat": "/sys/fs/cgroup/memory.stat",
             "memory_events": "/sys/fs/cgroup/memory.events",
             "swap_max": "/sys/fs/cgroup/memory.swap.max",
             "meminfo": "/proc/meminfo",
             "overcommit_memory": "/proc/sys/vm/overcommit_memory",
             "max_map_count": "/proc/sys/vm/max_map_count"}
    result = {}
    for name, filename in paths.items():
        try:
            result[name] = Path(filename).read_text().strip()
        except OSError:
            result[name] = None
    result["ulimit"] = subprocess.check_output(["/bin/sh", "-c", "ulimit -a"], text=True)
    return result


def toolchain_info(project: Path, official):
    require((project / "lean-toolchain").read_text().strip() == TOOLCHAIN,
            "The project does not select the pinned rc2 toolchain")
    env = {**os.environ, "ELAN_TOOLCHAIN": TOOLCHAIN}
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], env=env,
                                         text=True).strip()).resolve(strict=True)
    tools = official.toolchain_tools(prefix)
    version = subprocess.check_output([str(tools["lean"]), "--version"], text=True).strip()
    require("version 4.35.0-rc2," in version and LEAN_REVISION in version,
            "Lean binary does not match the pinned rc2 release")
    return prefix, tools, version


def dependency_paths(project: Path) -> tuple[list[Path], dict[str, dict]]:
    manifest = json.loads((project / "lake-manifest.json").read_text())
    packages_root = project / manifest.get("packagesDir", ".lake/packages")
    entries = {}
    paths = []
    for entry in manifest["packages"]:
        name = entry["name"]
        require(entry["type"] == "git", f"Unpinned non-Git dependency: {name}")
        package = (packages_root / name).resolve(strict=True)
        require(git_head(package) == entry["rev"], f"Wrong dependency revision: {name}")
        require(subprocess.run(["git", "-C", str(package), "diff", "--quiet", "HEAD"],
                               check=False).returncode == 0,
                f"Modified tracked dependency files: {name}")
        entries[name] = {"path": str(package), "revision": entry["rev"], "url": entry["url"]}
        library = package / ".lake/build/lib/lean"
        if library.is_dir():
            paths.append(library.resolve())
    require(entries.get("mathlib", {}).get("revision") == MATHLIB_REVISION,
            "Wrong Mathlib pin")
    mathlib = Path(entries["mathlib"]["path"])
    nested = json.loads((mathlib / "lake-manifest.json").read_text())
    for entry in nested["packages"]:
        require(entries.get(entry["name"], {}).get("revision") == entry["rev"],
                f"Mathlib dependency pin mismatch: {entry['name']}")
    require((mathlib / "lean-toolchain").read_text().strip() == TOOLCHAIN,
            "Mathlib toolchain differs from the project")
    return paths, entries


def run_logged(command: list[str], *, cwd: Path, log: Path,
               environment: dict[str, str], output: Path | None = None) -> dict:
    print(f"Running {log.stem}", flush=True)
    start = time.monotonic()
    with log.open("w") as errors:
        if output is None:
            proc = subprocess.run(command, cwd=cwd, env=environment,
                                  stdout=errors, stderr=subprocess.STDOUT, check=False)
        else:
            with output.open("wb") as stream:
                proc = subprocess.run(command, cwd=cwd, env=environment,
                                      stdout=stream, stderr=errors, check=False)
    result = {"command": command, "exit_code": proc.returncode,
              "elapsed_seconds": round(time.monotonic() - start, 3),
              "log": str(log), "log_sha256": sha256(log)}
    if output is not None:
        result.update(output=str(output), bytes=output.stat().st_size,
                      output_sha256=sha256(output))
    print(f"Finished: exit {proc.returncode}; {result['elapsed_seconds']} seconds", flush=True)
    return result
