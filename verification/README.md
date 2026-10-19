# Verification record

The records below describe fresh local checks of this six-headline package on
October 19, 2026. They do not reuse certificates from the earlier repository.
The [source report](source-checks.json) records the exact Lean sources and build
controls; [provenance](../PROVENANCE.json) records their origins.

| Check | Current result | Evidence |
| --- | --- | --- |
| Official source, configuration, header, and technical metadata requirements | PASS: 3,940 Lean files; exactly twelve intentional Challenge placeholders; no proof holes elsewhere | [Source report](source-checks.json) |
| Default `lake build` | PASS: 12,871 jobs, with cached dependencies and build objects | [Dated build receipt](build-result.json) |
| Strict `Audit.lean` check | PASS: twelve exports and 248 source-interface declarations; zero warnings or errors | [Dated audit receipt](axiom-audit-result.json), [audit log](axiom-audit.log) |
| Official Comparator statement, reachable-helper, and axiom comparison | PASS in the current protected run | Final replay receipt pending |
| Independent kernel replay | **Pending**: con-ron is running; NanoDa and Lean default have not yet returned verdicts | No kernel acceptance is claimed |

The audit permits only `propext`, `Classical.choice`, and `Quot.sound`. It also
checks that Chen's finite-mixture Parisi formula is an explicit premise in the
expected eight exports. The finite-dimensional Haar result and Theorems
1.5–1.7 have no literature premise. The ordinary build permits existing
infrastructure warnings; the separate Audit invocation uses
`-DwarningAsError=true`.

## Protected comparison

The replay uses the official PalomarSubmission verifier at
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, Lean `v4.35.0-rc2`
(`11acb17ec6b07a8f9e9173e6845197929540936b`), and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The runner records executable
digests, dependency revisions, commands, exit codes, and source hashes.

A fresh canonical Challenge is compiled under a random module alias with only
the pinned Mathlib dependencies and Lean core available. Candidate-local
libraries are excluded from that compilation. The bundled Comparator checks
the twelve theorem types and recursively checks complete reachable helper
declarations. No definition-hole exemptions are configured. It then runs
con-ron, NanoDa, and Lean default on the Solution export inside its own
sandbox.

The runner writes an accepted `comparator/result.json` and `comparator.log`
only after exit zero, all three kernel acceptance markers, and the final
Comparator success marker. That accepted record does not yet exist for this
checkpoint. Large exports, compilation logs, and failed attempts remain in
external scratch storage.

## Reproduction and scope

Follow the pinned setup in the [repository guide](../README.md), then run:

```sh
bash scripts/verify.sh /path/to/pinned/PalomarSubmission
```

This reruns the source checks, default build, strict Audit, and protected
Comparator replay. The two `*-result.json` build and audit files are dated
saved receipts for this snapshot; this command does not regenerate those two
summaries. Its exit status and current logs describe the new run. Use a fresh
checkout if preserving the saved evidence unchanged.

These checks use locally cached dependency objects and existing build
artifacts. They are distinct from a clean Palomar registry intake, public
submission, registration, editorial review, or acceptance. The independent
kernel replay remains pending at this checkpoint.
