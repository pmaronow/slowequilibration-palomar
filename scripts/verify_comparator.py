#!/usr/bin/env python3
"""Replay this package locally with the pinned official Comparator and three kernels.

The Challenge is compiled against pinned Mathlib and its dependency closure only,
under the official verifier's fresh canonical module alias. Exports and kernels run
in the official bubblewrap policy. This is not a registry submission or verdict.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from palomar_common import (LEAN_REVISION, PALOMAR_REVISION, ROOT, TOOLCHAIN,
                            dependency_paths, host_limits, now, official_verifier,
                            proof_snapshot, require, run_logged, sha256,
                            toolchain_info, write_json)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=ROOT)
    parser.add_argument("--palomar-submission", type=Path, required=True)
    parser.add_argument("--output-parent", type=Path,
                        help="External directory for fresh scratch output and large exports")
    parser.add_argument("--report", type=Path,
                        default=ROOT / "verification/comparator/result.json")
    parser.add_argument("--check-host-only", action="store_true")
    parser.add_argument("--keep-exports", action="store_true")
    args = parser.parse_args()
    project = args.project.resolve(strict=True)
    parent = args.output_parent.resolve() if args.output_parent else project.parent / "scratch"
    require(not parent.is_relative_to(project), "Scratch output must be outside the package")
    parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="slowequilibration-comparator-", dir=parent))
    report_path = args.report.resolve()
    report = {"recorded_at": now(), "scope": "Local protected Comparator replay only",
              "palomar_revision": PALOMAR_REVISION, "lean_revision": LEAN_REVISION,
              "project": str(project), "scratch": str(work), "commands": [],
              "accepted": False, "kernel_replay_attempted": False,
              "kernel_replay_performed": False,
              "host_limits": host_limits()}
    official = None
    before = None
    exports = []
    try:
        official = official_verifier(args.palomar_submission)
        prefix, tools, version = toolchain_info(project, official)
        libraries, dependencies = dependency_paths(project)
        bwrap_name = shutil.which("bwrap")
        require(bwrap_name is not None, "bubblewrap is required")
        bwrap = Path(bwrap_name).resolve(strict=True)
        bwrap_version = subprocess.check_output([str(bwrap), "--version"], text=True).strip()
        require(bwrap_version == "bubblewrap 0.12.0", "Expected bubblewrap 0.12.0")
        digests = official.tool_digests(tools, bwrap)
        kernels = official.protected_kernels(tools)
        report.update(toolchain=TOOLCHAIN, lean_version=version, toolchain_prefix=str(prefix),
                      bubblewrap_version=bwrap_version, tools_sha256=digests,
                      dependencies=dependencies, external_kernels=kernels)
        environment = {"PATH": str(prefix / "bin") + ":" + os.defpath,
                       "HOME": "/tmp/home", "TMPDIR": "/tmp", "LANG": "C.UTF-8",
                       "LEAN_NUM_THREADS": "1", "ELAN_TOOLCHAIN": TOOLCHAIN,
                       "LEAN_ABORT_ON_PANIC": "1", "COMPARATOR_BWRAP": str(bwrap)}
        system_paths = sorted({p.resolve() for p in map(Path, ("/usr", "/bin", "/lib", "/lib64"))
                               if p.exists()})

        def confined(command, *, cwd, paths=(), readable=(), writable=(), output=None,
                     name, nested=False, allow_failure=False):
            env = {**environment, "LEAN_PATH": os.pathsep.join(str(p) for p in paths)}
            argv = official.bwrap_command(
                list(map(str, command)), bwrap=bwrap, writable_directories=list(writable),
                readable_paths=sorted({cwd, *readable, *paths, *official.system_readable_paths()}),
                executable_paths=[prefix, bwrap, *system_paths], environment=env,
                nested_sandbox=nested)
            boundary = argv.index("--")
            argv[boundary:boundary] = ["--dir", "/tmp/home", "--setenv", "ELAN_TOOLCHAIN", TOOLCHAIN,
                                     "--setenv", "LEAN_NUM_THREADS", "1"]
            result = run_logged(argv, cwd=cwd, log=work / f"{name}.log",
                                environment=environment, output=output)
            result["phase"] = name
            report["commands"].append(result)
            write_json(work / "result.json", report)
            require(allow_failure or result["exit_code"] == 0,
                    f"{name} exited {result['exit_code']}; inspect {result['log']}")
            return result

        true = Path(shutil.which("true") or "/usr/bin/true").resolve(strict=True)
        confined([true], cwd=work, writable=[work], name="sandbox-preflight", nested=True)
        if args.check_host_only:
            report.update(host_preflight_passed=True, status="HOST_PREFLIGHT_PASS",
                          limitation="No Challenge compilation, export, or kernel replay performed")
            print("HOST PREFLIGHT PASS", flush=True)
            return 0

        config = official.load_comparator_config(project / "comparator.json")
        report["configuration"] = config
        before = proof_snapshot(project)
        report["proof_sources_sha256"] = before
        runners = [Path(__file__), Path(__file__).with_name("palomar_common.py"),
                   Path(__file__).with_name("verify_sources.py"), Path(__file__).with_name("verify.sh")]
        runner_digests = {p.name: sha256(p) for p in runners}
        report["runner_sources_sha256"] = runner_digests
        require((project / ".lake/build/lib/lean" /
                 official.module_source_suffix(config["solution_module"]).with_suffix(".olean")).is_file(),
                "Build Solution before Comparator replay")
        protected = official.protected_comparator_config(
            project / "comparator.json", work / "protected-comparator.json", kernels=kernels)
        alias = json.loads(protected.read_text())["challenge_module"]
        canonical_source = work / "canonical/src" / Path(*alias.split(".")).with_suffix(".lean")
        canonical_source.parent.mkdir(parents=True)
        challenge_source = project / official.module_source_suffix(config["challenge_module"]).with_suffix(".lean")
        canonical_source.write_bytes(challenge_source.read_bytes())
        canonical_library = work / "canonical/lib"
        canonical_object = canonical_library / Path(*alias.split(".")).with_suffix(".olean")
        canonical_object.parent.mkdir(parents=True)
        trusted_paths = [*libraries, prefix / "lib/lean"]
        candidate_paths = [project / ".lake/build/lib/lean", *trusted_paths]
        confined([tools["lean"], "-j1", "-DautoImplicit=false", "--root=" + str(work / "canonical/src"),
                  canonical_source, "-o", canonical_object], cwd=work / "canonical/src",
                 paths=trusted_paths, readable=[work / "canonical/src"], writable=[canonical_library],
                 name="canonical-challenge-compile")
        report["canonical_challenge"] = {"module": alias, "source_sha256": sha256(canonical_source),
                                         "olean_sha256": sha256(canonical_object),
                                         "trusted_paths": list(map(str, trusted_paths))}
        targets = official.comparator_export_targets(config, official.primitive_targets(prefix))
        for side, module, paths in [("challenge", alias, [canonical_library, *trusted_paths]),
                                    ("solution", config["solution_module"], candidate_paths)]:
            output = work / f"{side}.ndjson"
            exports.append(output)
            confined([tools["leanexport"], module, "--", *targets], cwd=work,
                     paths=paths, output=output, name=f"{side}-export")
            official.verify_export(output)
        require(proof_snapshot(project) == before, "Proof inputs changed during export")
        require(official.tool_digests(tools, bwrap) == digests, "Verifier binaries changed")
        judge = work / "judge"
        judge.mkdir()
        report["kernel_replay_attempted"] = True
        judgment = confined([tools["lake"], "comparator", "--config", protected,
                  "--challenge-from-export", exports[0], "--solution-from-export", exports[1]],
                 cwd=judge, readable=[protected, *exports], writable=[judge],
                 name="comparator", nested=True, allow_failure=True)
        transcript = (work / "comparator.log").read_text()
        report["kernel_results"] = {}
        for kernel in ("con-ron", "nanoda", "Lean default"):
            report["kernel_results"][kernel] = next((verdict for verb, verdict in (
                ("accepts", "accepted"), ("rejected", "rejected")) if re.search(
                    "^" + re.escape(kernel) + " kernel " + verb + " the solution$",
                    transcript, re.MULTILINE)), "not-observed")
        report["kernel_replay_performed"] = all(
            result != "not-observed" for result in report["kernel_results"].values())
        markers = ["con-ron kernel accepts the solution", "nanoda kernel accepts the solution",
                   "Lean default kernel accepts the solution", "Your solution is okay!"]
        report["kernel_acceptance"] = {marker: bool(re.search(
            "^" + re.escape(marker) + "$", transcript, re.MULTILINE)) for marker in markers}
        require(judgment["exit_code"] == 0, "Comparator rejected or could not complete; inspect external logs")
        require(all(report["kernel_acceptance"].values()), "Missing a required Comparator acceptance marker")
        require(proof_snapshot(project) == before, "Proof inputs changed during verification")
        require(official.tool_digests(tools, bwrap) == digests, "Verifier binaries changed")
        require({p.name: sha256(p) for p in runners} == runner_digests, "Verification scripts changed")
        official_verifier(args.palomar_submission)
        report.update(accepted=True, status="PASS", proof_inputs_unchanged=True,
                      limitation="Local cached-dependency replay; not full clean registry intake or editorial review")
        print("COMPARATOR PASS: Lean default, NanoDa, and con-ron accepted", flush=True)
        return 0
    except Exception as error:
        report.update(status="FAIL", error=str(error))
        print(f"FAIL: {error}", flush=True)
        return 1
    finally:
        report["finished_at"] = now()
        if before is not None:
            report["proof_inputs_unchanged"] = proof_snapshot(project) == before
        report["host_limits_after"] = host_limits()
        write_json(work / "result.json", report)
        if report["accepted"] or report.get("host_preflight_passed"):
            write_json(report_path, report)
            # Only the accepted verdict transcript is part of the current evidence.
            # Raw export/compilation logs and failures stay in external scratch.
            if report["accepted"]:
                shutil.copyfile(work / "comparator.log", report_path.parent / "comparator.log")
        else:
            print(f"Failure evidence retained outside the package: {work / 'result.json'}", flush=True)
        if not args.keep_exports:
            for output in exports:
                output.unlink(missing_ok=True)


if __name__ == "__main__":
    raise SystemExit(main())
