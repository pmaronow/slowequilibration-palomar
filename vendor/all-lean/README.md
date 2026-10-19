# Vendored foundations

This directory contains 1,374 Lean modules from `pmaronow/all-lean` at
`4b5409b513d8ae9160b29401bff2ce6d3e95e5f1`, selected by the transitive import
closure of the six headline proofs and their independent statement bridges.
The files are byte-identical to that source. `VENDORED.json` records each hash.

The module names and original per-library Lean options are preserved in
`lakefile.toml`. This is vendored source, not a separate Lake dependency.

The upstream MIT license and retained third-party licenses/notices are in
`../../LICENSES/all-lean/`. Its filtered `source-origins.json` records the
origins of the retained modules.
