#!/usr/bin/env python3
"""Apply official non-executing source/configuration checks to this package.

This is local validation, not Palomar intake or an editorial determination.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

from palomar_common import (EXPECTED_THEOREMS, PALOMAR_REVISION, ROOT, now, official_verifier,
                            proof_snapshot, require, sha256, toolchain_info, write_json)


def code_without_strings(official, text: str) -> str:
    text = official.strip_lean_comments(text)
    return re.sub(r'"(?:\\.|[^"\\])*"', lambda m: "\n" * m.group().count("\n"), text)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=ROOT)
    parser.add_argument("--palomar-submission", type=Path, required=True)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    project = args.project.resolve(strict=True)
    report = {"recorded_at": now(), "scope": "Local official source/configuration checks",
              "palomar_revision": PALOMAR_REVISION, "passed": False}
    try:
        official = official_verifier(args.palomar_submission)
        config = official.load_comparator_config(project / "comparator.json")
        require(set(config["theorem_names"]) == set(EXPECTED_THEOREMS) and
                len(config["theorem_names"]) == len(EXPECTED_THEOREMS),
                "Comparator must compare exactly the twelve six-headline theorem exports")
        require(not config.get("definition_names"),
                "This package has no separately configured definition holes")
        metadata_path = project / "formalization.yaml"
        metadata = official.submission_contract.load_formalization_metadata(metadata_path)
        official.submission_contract.normalized_provenance(metadata)
        summary, issues = official.inspect_lean_sources(project)
        require(not issues, "\n".join(str(issue) for issue in issues))
        official.reject_committed_build_artifacts(project)
        _, tools, version = toolchain_info(project, official)
        source_files = [p for p in official.lean_source_files(project) if p.name != "lakefile.lean"]
        for start in range(0, len(source_files), 64):
            batch = source_files[start:start + 64]
            proc = subprocess.run([str(tools["lean"]), "--deps-json", *map(str, batch)],
                                  cwd=project, text=True, capture_output=True, check=False)
            require(proc.returncode == 0, "Lean header parser failed: " + proc.stderr[-2000:])
            entries = json.loads(proc.stdout)["imports"]
            require(len(entries) == len(batch), "Lean header count differs from source count")
            for path, entry in zip(batch, entries, strict=True):
                header = official.parse_lean_header(json.dumps({"imports": [entry]}))
                require(header.is_module, f"Not a Lean module: {path.relative_to(project)}")
        challenge = project / official.module_source_suffix(config["challenge_module"]).with_suffix(".lean")
        require(challenge.is_file() and not challenge.is_symlink(), "Challenge source is missing")
        text = challenge.read_text()
        require(challenge.stat().st_size <= official.MAX_CHALLENGE_BYTES,
                "Challenge exceeds the official 100 KiB cap")
        require(len(text.splitlines()) <= official.MAX_CHALLENGE_LINES,
                "Challenge exceeds the official 1000-line cap")
        challenge_holes = re.findall(r"(?<![\w.])(?:sorry|admit|axiom)(?![\w'])",
                                    code_without_strings(official, text))
        require(challenge_holes == ["sorry"] * len(EXPECTED_THEOREMS),
                "Challenge must have exactly twelve intentional theorem statement holes")
        solution = project / official.module_source_suffix(config["solution_module"]).with_suffix(".lean")
        require(solution.is_file() and not solution.is_symlink(), "Solution source is missing")
        holes = []
        for path in official.lean_source_files(project):
            if path == challenge:
                continue
            code = code_without_strings(official, path.read_text())
            for match in re.finditer(r"(?<![\w.])(?:sorry|admit|axiom)(?![\w'])", code):
                holes.append(f"{path.relative_to(project)}:{code[:match.start()].count(chr(10)) + 1}: {match.group()}")
        require(not holes, "Unexpected proof holes or source axioms:\n" + "\n".join(holes))
        report.update(passed=True, source_requirements=summary, configuration=config,
                      lean_version=version, parsed_source_headers=len(source_files),
                      technical_metadata_valid=True, formalization_sha256=sha256(metadata_path),
                      challenge_bytes=challenge.stat().st_size,
                      challenge_lines=len(text.splitlines()), proof_sources=proof_snapshot(project),
                      intentional_challenge_statement_holes=len(challenge_holes),
                      proof_holes_outside_challenge=0,
                      limitation="Canonical Challenge compilation and kernels are checked separately")
        print(f"PASS: official source/configuration checks; {summary['files_checked']} Lean files")
    except Exception as error:
        report["error"] = str(error)
        print(f"FAIL: {error}", file=sys.stderr)
    if args.report and (report["passed"] or not args.report.resolve().is_relative_to(project)):
        write_json(args.report.resolve(), report)
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
