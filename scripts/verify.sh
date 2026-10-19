#!/usr/bin/env bash
set -euo pipefail
if [[ $# -ne 1 ]]; then
  printf '%s\n' 'Usage: bash scripts/verify.sh /path/to/pinned/PalomarSubmission' >&2
  exit 2
fi
palomar_submission_path=$(cd "$1" && pwd)
cd "$(dirname "$0")/.."
export ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0-rc2
export LEAN_NUM_THREADS=1
mkdir -p verification
python3 scripts/verify_sources.py --palomar-submission "$palomar_submission_path" \
  --report verification/source-checks.json
lake build
audit_work=$(mktemp -d "${TMPDIR:-/tmp}/slowequilibration-audit.XXXXXX")
if lake env lean -j1 -DautoImplicit=false -DwarningAsError=true Audit.lean \
    > "$audit_work/axiom-audit.log" 2>&1; then
  cp "$audit_work/axiom-audit.log" verification/axiom-audit.log
else
  printf 'Audit failed; inspect %s\n' "$audit_work/axiom-audit.log" >&2
  exit 1
fi
python3 scripts/verify_comparator.py --palomar-submission "$palomar_submission_path"
